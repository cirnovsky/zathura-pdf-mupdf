/* SPDX-License-Identifier: Zlib */

/*
 * Text layer and annotation access for zathura's cursor and visual modes.
 *
 * Annotations are identified by the object number of their PDF dictionary,
 * which stays stable while the document is open. Every entry point takes the
 * document mutex for its whole duration, as the rest of the plugin does.
 */

#include <glib.h>
#include <glib/gstdio.h>
#include <mupdf/pdf.h>
#include <unistd.h>

#include "plugin.h"
#include "utils.h"

static zathura_rectangle_t rect_from_fz(fz_rect r) {
  return (zathura_rectangle_t){.x1 = r.x0, .y1 = r.y0, .x2 = r.x1, .y2 = r.y1};
}

/* zathura works in doubles, MuPDF in floats. */
static fz_quad quad_from_rect(const zathura_rectangle_t* r) {
  return fz_quad_from_rect((fz_rect){(float)r->x1, (float)r->y1, (float)r->x2, (float)r->y2});
}

static mupdf_document_t* doc_of(zathura_page_t* page) {
  return zathura_document_get_data(zathura_page_get_document(page));
}

/* ------------------------------------------------------------------------ */
/* characters                                                               */

struct char_walk {
  girara_list_t* list;
  unsigned int line;
  unsigned int block;
};

static void walk_line(struct char_walk* w, fz_stext_line* line) {
  for (fz_stext_char* ch = line->first_char; ch != NULL; ch = ch->next) {
    zathura_text_char_t* c = g_new(zathura_text_char_t, 1);
    fz_rect r              = fz_rect_from_quad(ch->quad);

    /* Zero-width characters, e.g. synthesised spaces, still need a box. */
    if (fz_is_empty_rect(r)) {
      r.x1 = r.x0 + 0.5f;
      if (r.y1 <= r.y0) {
        r.y0 = line->bbox.y0;
        r.y1 = line->bbox.y1;
      }
    }
    *c = (zathura_text_char_t){.box = rect_from_fz(r), .c = ch->c, .line = w->line, .block = w->block};
    girara_list_append(w->list, c);
  }
}

/* Text blocks may be nested inside structure blocks; visit them in order. */
static void walk_blocks(struct char_walk* w, fz_stext_block* block) {
  for (; block != NULL; block = block->next) {
    if (block->type == FZ_STEXT_BLOCK_STRUCT && block->u.s.down != NULL) {
      walk_blocks(w, block->u.s.down->first_block);
    }
    if (block->type != FZ_STEXT_BLOCK_TEXT) {
      continue;
    }

    const size_t before = girara_list_size(w->list);
    for (fz_stext_line* line = block->u.t.first_line; line != NULL; line = line->next) {
      if (line->first_char != NULL) {
        walk_line(w, line);
        w->line++;
      }
    }
    if (girara_list_size(w->list) != before) {
      w->block++;
    }
  }
}

girara_list_t* pdf_page_get_chars(zathura_page_t* page, void* data, zathura_error_t* error) {
  mupdf_page_t* mpage = data;
  mupdf_document_t* mdoc;
  struct char_walk w = {0};

  if (page == NULL || mpage == NULL || mpage->text == NULL) {
    zathura_check_set_error(error, ZATHURA_ERROR_INVALID_ARGUMENTS);
    return NULL;
  }
  mdoc   = doc_of(page);
  w.list = girara_list_new_with_free(g_free);

  g_mutex_lock(&mdoc->mutex);
  if (mpage->extracted_text == false) {
    mupdf_page_extract_text(mdoc, mpage);
  }
  walk_blocks(&w, mpage->text->first_block);
  g_mutex_unlock(&mdoc->mutex);

  return w.list;
}

/* ------------------------------------------------------------------------ */
/* annotations                                                              */

/*
 * Lock the document and look up the PDF page behind a zathura page.
 * On success the caller holds the mutex and must call page_unlock().
 */
struct locked_page {
  mupdf_document_t* mdoc;
  fz_context* ctx;
  pdf_page* page;
};

static zathura_error_t page_lock(zathura_page_t* page, mupdf_page_t* mpage, struct locked_page* lp) {
  if (page == NULL || mpage == NULL) {
    return ZATHURA_ERROR_INVALID_ARGUMENTS;
  }
  lp->mdoc = doc_of(page);
  lp->ctx  = lp->mdoc->ctx;

  g_mutex_lock(&lp->mdoc->mutex);
  if (pdf_document_from_fz_document(lp->ctx, lp->mdoc->document) == NULL) {
    g_mutex_unlock(&lp->mdoc->mutex);
    return ZATHURA_ERROR_NOT_IMPLEMENTED; /* EPUB, XPS, images, ... */
  }
  lp->page = pdf_page_from_fz_page(lp->ctx, mpage->page);
  return ZATHURA_ERROR_OK;
}

static void page_unlock(struct locked_page* lp) {
  g_mutex_unlock(&lp->mdoc->mutex);
}

/* Borrowed reference: annotations are owned by their page. */
static pdf_annot* annot_find(struct locked_page* lp, int id) {
  for (pdf_annot* a = pdf_first_annot(lp->ctx, lp->page); a != NULL; a = pdf_next_annot(lp->ctx, a)) {
    if (pdf_to_num(lp->ctx, pdf_annot_obj(lp->ctx, a)) == id) {
      return a;
    }
  }
  return NULL;
}

static void annotation_free(void* data) {
  zathura_annotation_t* a = data;

  g_free(a->rects);
  g_free(a->contents);
  g_free(a);
}

static bool has_quads(enum pdf_annot_type type) {
  return type == PDF_ANNOT_HIGHLIGHT || type == PDF_ANNOT_UNDERLINE || type == PDF_ANNOT_STRIKE_OUT ||
         type == PDF_ANNOT_SQUIGGLY;
}

static zathura_annotation_type_t type_from_pdf(enum pdf_annot_type type) {
  switch (type) {
  case PDF_ANNOT_HIGHLIGHT:
    return ZATHURA_ANNOTATION_HIGHLIGHT;
  case PDF_ANNOT_TEXT:
    return ZATHURA_ANNOTATION_TEXT;
  default:
    return ZATHURA_ANNOTATION_OTHER;
  }
}

/* The annotation's colour as RGB: gray is expanded, a missing colour is yellow. */
static void color_from_pdf(fz_context* ctx, pdf_annot* annot, double rgb[3]) {
  float c[4] = {0};
  int n      = 0;

  pdf_annot_color(ctx, annot, &n, c);
  if (n == 3) {
    rgb[0] = c[0], rgb[1] = c[1], rgb[2] = c[2];
  } else if (n == 1) {
    rgb[0] = rgb[1] = rgb[2] = c[0];
  } else {
    rgb[0] = 1, rgb[1] = 1, rgb[2] = 0;
  }
}

static zathura_annotation_t* annotation_from_pdf(fz_context* ctx, pdf_annot* annot) {
  zathura_annotation_t* a  = g_new0(zathura_annotation_t, 1);
  enum pdf_annot_type type = pdf_annot_type(ctx, annot);
  const char* contents     = pdf_annot_contents(ctx, annot);

  a->id     = pdf_to_num(ctx, pdf_annot_obj(ctx, annot));
  a->type   = type_from_pdf(type);
  a->bounds = rect_from_fz(pdf_bound_annot(ctx, annot));
  if (contents != NULL && *contents != '\0') {
    a->contents = g_strdup(contents);
  }
  color_from_pdf(ctx, annot, a->color);

  if (has_quads(type)) {
    a->n_rects = pdf_annot_quad_point_count(ctx, annot);
    a->rects   = g_new(zathura_rectangle_t, a->n_rects);
    for (size_t i = 0; i < a->n_rects; i++) {
      a->rects[i] = rect_from_fz(fz_rect_from_quad(pdf_annot_quad_point(ctx, annot, (int)i)));
    }
  }
  return a;
}

girara_list_t* pdf_page_get_annotations(zathura_page_t* page, void* data, zathura_error_t* error) {
  girara_list_t* list = girara_list_new_with_free(annotation_free);
  struct locked_page lp;

  if (page_lock(page, data, &lp) != ZATHURA_ERROR_OK) {
    return list; /* no annotations rather than an error: the caller just shows none */
  }
  fz_try(lp.ctx) {
    for (pdf_annot* a = pdf_first_annot(lp.ctx, lp.page); a != NULL; a = pdf_next_annot(lp.ctx, a)) {
      enum pdf_annot_type type = pdf_annot_type(lp.ctx, a);

      if (type != PDF_ANNOT_POPUP && type != PDF_ANNOT_LINK && type != PDF_ANNOT_WIDGET) {
        girara_list_append(list, annotation_from_pdf(lp.ctx, a));
      }
    }
  }
  fz_catch(lp.ctx) {
    zathura_check_set_error(error, ZATHURA_ERROR_UNKNOWN);
  }
  page_unlock(&lp);

  return list;
}

int pdf_page_add_highlight(zathura_page_t* page, void* data, girara_list_t* rectangles, const double color[3],
                           const char* contents, const char* author, zathura_error_t* error) {
  const int n               = rectangles != NULL ? (int)girara_list_size(rectangles) : 0;
  const float rgb[3]        = {(float)color[0], (float)color[1], (float)color[2]};
  pdf_annot* volatile annot = NULL;
  fz_quad* quads;
  struct locked_page lp;
  zathura_error_t err;
  int id = -1;

  if (n == 0) {
    zathura_check_set_error(error, ZATHURA_ERROR_INVALID_ARGUMENTS);
    return -1;
  }
  err = page_lock(page, data, &lp);
  if (err != ZATHURA_ERROR_OK) {
    zathura_check_set_error(error, err);
    return -1;
  }

  quads = g_new(fz_quad, n);
  for (int i = 0; i < n; i++) {
    quads[i] = quad_from_rect(girara_list_nth(rectangles, i));
  }

  fz_try(lp.ctx) {
    annot = pdf_create_annot(lp.ctx, lp.page, PDF_ANNOT_HIGHLIGHT);
    pdf_set_annot_color(lp.ctx, annot, 3, rgb);
    pdf_set_annot_quad_points(lp.ctx, annot, n, quads);
    if (author != NULL && *author != '\0') {
      pdf_set_annot_author(lp.ctx, annot, author);
    }
    if (contents != NULL && *contents != '\0') {
      pdf_set_annot_contents(lp.ctx, annot, contents);
    }
    pdf_update_annot(lp.ctx, annot);
    pdf_update_page(lp.ctx, lp.page);
    id = pdf_to_num(lp.ctx, pdf_annot_obj(lp.ctx, annot));
  }
  fz_always(lp.ctx) {
    pdf_drop_annot(lp.ctx, annot);
  }
  fz_catch(lp.ctx) {
    zathura_check_set_error(error, ZATHURA_ERROR_UNKNOWN);
    id = -1;
  }
  page_unlock(&lp);
  g_free(quads);

  return id;
}

zathura_error_t pdf_page_set_annotation_contents(zathura_page_t* page, void* data, int id, const char* contents) {
  zathura_error_t err;
  struct locked_page lp;
  pdf_annot* annot;

  err = page_lock(page, data, &lp);
  if (err != ZATHURA_ERROR_OK) {
    return err;
  }
  annot = annot_find(&lp, id);
  if (annot == NULL) {
    err = ZATHURA_ERROR_INVALID_ARGUMENTS;
  } else {
    fz_try(lp.ctx) {
      pdf_set_annot_contents(lp.ctx, annot, contents != NULL ? contents : "");
      pdf_update_annot(lp.ctx, annot);
      pdf_update_page(lp.ctx, lp.page);
    }
    fz_catch(lp.ctx) {
      err = ZATHURA_ERROR_UNKNOWN;
    }
  }
  page_unlock(&lp);

  return err;
}

zathura_error_t pdf_page_delete_annotation(zathura_page_t* page, void* data, int id) {
  zathura_error_t err;
  struct locked_page lp;
  pdf_annot* annot;

  err = page_lock(page, data, &lp);
  if (err != ZATHURA_ERROR_OK) {
    return err;
  }
  annot = annot_find(&lp, id);
  if (annot == NULL) {
    err = ZATHURA_ERROR_INVALID_ARGUMENTS;
  } else {
    fz_try(lp.ctx) {
      pdf_delete_annot(lp.ctx, lp.page, annot);
      pdf_update_page(lp.ctx, lp.page);
    }
    fz_catch(lp.ctx) {
      err = ZATHURA_ERROR_UNKNOWN;
    }
  }
  page_unlock(&lp);

  return err;
}

/* ------------------------------------------------------------------------ */
/* saving                                                                   */

/*
 * Append the changes to the end of the file. The bytes already there are not
 * touched, so the open document stays valid.
 *
 * MuPDF writes only the objects changed since the previous save, but before
 * appending it truncates the file to doc->file_size, which it never updates.
 * Left alone, a second save would cut off the first save's increment, losing
 * those changes and breaking the xref chain. So move file_size past each
 * increment we write.
 */
static zathura_error_t save_incremental(fz_context* ctx, pdf_document* doc, const char* path) {
  pdf_write_options opts = pdf_default_write_options;
  GStatBuf st;

  opts.do_incremental = 1;
  fz_try(ctx) {
    pdf_save_document(ctx, doc, path, &opts);
  }
  fz_catch(ctx) {
    return ZATHURA_ERROR_UNKNOWN;
  }
  if (g_stat(path, &st) == 0) {
    doc->file_size = st.st_size;
  }
  return ZATHURA_ERROR_OK;
}

/*
 * Write a complete new file next to the old one and rename it into place. The
 * open document still reads the old, now unlinked, file and must be reopened.
 */
static zathura_error_t save_rewrite(fz_context* ctx, pdf_document* doc, const char* path) {
  pdf_write_options opts = pdf_default_write_options;
  g_autofree char* tmp   = g_strdup_printf("%s.zathura-XXXXXX", path);
  zathura_error_t err    = ZATHURA_ERROR_OK;
  GStatBuf st;
  int fd;

  fd = g_mkstemp(tmp);
  if (fd < 0) {
    return ZATHURA_ERROR_UNKNOWN;
  }
  close(fd);
  if (g_stat(path, &st) == 0) {
    g_chmod(tmp, st.st_mode & 07777); /* mkstemp creates 0600 */
  }

  opts.do_garbage = 1;
  fz_try(ctx) {
    pdf_save_document(ctx, doc, tmp, &opts);
  }
  fz_catch(ctx) {
    err = ZATHURA_ERROR_UNKNOWN;
  }
  if (err != ZATHURA_ERROR_OK || g_rename(tmp, path) != 0) {
    g_unlink(tmp);
    return ZATHURA_ERROR_UNKNOWN;
  }
  return ZATHURA_ERROR_OK;
}

zathura_error_t pdf_document_save(zathura_document_t* document, void* data, bool* needs_reload) {
  mupdf_document_t* mdoc = data;
  const char* path       = document != NULL ? zathura_document_get_path(document) : NULL;
  zathura_error_t err    = ZATHURA_ERROR_OK;
  pdf_document* doc;

  *needs_reload = false;
  if (mdoc == NULL || path == NULL) {
    return ZATHURA_ERROR_INVALID_ARGUMENTS;
  }

  g_mutex_lock(&mdoc->mutex);
  doc = pdf_document_from_fz_document(mdoc->ctx, mdoc->document);
  if (doc == NULL) {
    err = ZATHURA_ERROR_NOT_IMPLEMENTED;
  } else if (pdf_has_unsaved_changes(mdoc->ctx, doc) == 0) {
    err = ZATHURA_ERROR_OK;
  } else if (pdf_can_be_saved_incrementally(mdoc->ctx, doc)) {
    err = save_incremental(mdoc->ctx, doc, path);
  } else {
    err           = save_rewrite(mdoc->ctx, doc, path);
    *needs_reload = err == ZATHURA_ERROR_OK;
  }
  g_mutex_unlock(&mdoc->mutex);

  return err;
}
