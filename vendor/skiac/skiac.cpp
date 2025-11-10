#include "skiac.h"

#include "include/core/SkCanvas.h"
#include "include/core/SkColor.h"
#include "include/core/SkColorSpace.h"
#include "include/core/SkData.h"
#include "include/core/SkFont.h"
#include "include/core/SkFontMetrics.h"
#include "include/core/SkFontMgr.h"
#include "include/core/SkFontTypes.h"
#include "include/core/SkImageFilter.h"
#include "include/core/SkImage.h"
#include "include/core/SkMatrix.h"
#include "include/core/SkMaskFilter.h"
#include "include/core/SkPaint.h"
#include "include/core/SkPathEffect.h"
#include "include/core/SkPath.h"
#include "include/core/SkPathBuilder.h"
#include "include/core/SkRect.h"
#include "include/core/SkSamplingOptions.h"
#include "include/core/SkShader.h"
#include "include/core/SkTileMode.h"
#include "include/core/SkColorFilter.h"
#include "include/core/SkSurface.h"
#include "include/core/SkSurfaceProps.h"
#include "include/gpu/ganesh/GrBackendSurface.h"
#include "include/gpu/ganesh/GrDirectContext.h"
#include "include/gpu/ganesh/SkSurfaceGanesh.h"
#include "include/gpu/ganesh/gl/GrGLAssembleInterface.h"
#include "include/gpu/ganesh/gl/GrGLBackendSurface.h"
#include "include/gpu/ganesh/gl/GrGLDirectContext.h"
#include "include/gpu/ganesh/gl/GrGLInterface.h"
#include "include/ports/SkFontMgr_fontconfig.h"
#include "include/ports/SkFontScanner_FreeType.h"
#include "include/effects/SkImageFilters.h"
#include "include/effects/SkRuntimeEffect.h"
#include "include/effects/SkGradientShader.h"
#include "include/effects/SkDashPathEffect.h"
#include "include/effects/SkCornerPathEffect.h"
#include "include/effects/SkDiscretePathEffect.h"
#include "include/effects/SkBlurMaskFilter.h"
#include <optional>

//=================================================================================================
// Opaque Type Implementations
//=================================================================================================

struct skiac_gr_direct_context_t {
  GrDirectContext *context;
};

struct skiac_sk_surface_t {
  SkSurface *surface;
};

struct skiac_sk_canvas_t {
  SkCanvas *canvas;
};

struct skiac_sk_paint_t {
  SkPaint *paint;
};

struct skiac_sk_path_t {
  SkPathBuilder *builder;
};

struct skiac_sk_image_t {
  SkImage *image;
};

struct skiac_sk_font_t {
  SkFont *font;
};

struct skiac_sk_data_t {
  SkData *data;
};

struct skiac_sk_color_space_t {
  SkColorSpace *color_space;
};

struct skiac_sk_surface_props_t {
  SkSurfaceProps *props;
};

struct skiac_gr_gl_framebuffer_info_t {
  GrGLFramebufferInfo info;
};

struct skiac_gr_backend_render_target_t {
  GrBackendRenderTarget *target;
};

struct skiac_sk_shader_t { SkShader *shader; };
struct skiac_sk_color_filter_t { SkColorFilter *cf; };
struct skiac_sk_image_filter_t { SkImageFilter *f; };
struct skiac_sk_path_effect_t { SkPathEffect *pe; };
struct skiac_sk_mask_filter_t { SkMaskFilter *mf; };
struct skiac_sk_runtime_effect_t { SkRuntimeEffect *e; };

extern "C" {

//=================================================================================================

// GrGLInterface

//=================================================================================================

const GrGLInterface *
skiac_gr_gl_make_assembled_interface(void *ctx, GrGLGetProc get_proc) {
  return GrGLMakeAssembledInterface(ctx, get_proc).release();
}

void skiac_gr_gl_interface_unref(const GrGLInterface *interface) {
  if (interface) {
    interface->unref();
  }
}

//=================================================================================================

// GrDirectContext

//=================================================================================================

skiac_gr_direct_context_t *
skiac_gr_direct_context_make_gl(const GrGLInterface *gl_interface) {
  auto dctx = GrDirectContexts::MakeGL(sk_ref_sp(gl_interface)).release();
  return new skiac_gr_direct_context_t{dctx};
}

void skiac_gr_direct_context_unref(skiac_gr_direct_context_t *context) {
  if (context) {
    context->context->unref();
    delete context;
  }
}

void skiac_gr_direct_context_flush_and_submit(
    skiac_gr_direct_context_t *context) {
  context->context->flushAndSubmit(GrSyncCpu::kNo);
}

//=================================================================================================
// GrBackendRenderTarget
//=================================================================================================

skiac_gr_backend_render_target_t *
skiac_gr_backend_render_target_make_gl(int width, int height, int sample_cnt,
                                       int stencil_bits, unsigned int fbo_id,
                                       unsigned int format) {
  GrGLFramebufferInfo fb_info;
  fb_info.fFBOID = fbo_id;
  fb_info.fFormat = format;
  auto target = new GrBackendRenderTarget(GrBackendRenderTargets::MakeGL(
      width, height, sample_cnt, stencil_bits, fb_info));
  return new skiac_gr_backend_render_target_t{target};
}

void skiac_gr_backend_render_target_unref(
    skiac_gr_backend_render_target_t *target) {
  if (target) {
    delete target->target;
    delete target;
  }
}

//=================================================================================================
// SkColorSpace
//=================================================================================================
skiac_sk_color_space_t *skiac_sk_color_space_make_srgb() {
  return new skiac_sk_color_space_t{SkColorSpace::MakeSRGB().release()};
}

void skiac_sk_color_space_unref(skiac_sk_color_space_t *color_space) {
  if (color_space) {
    color_space->color_space->unref();
    delete color_space;
  }
}

//=================================================================================================
// SkSurfaceProps
//=================================================================================================
skiac_sk_surface_props_t *skiac_sk_surface_props_create(uint32_t flags,
                                                        int pixel_geometry) {
  return new skiac_sk_surface_props_t{
      new SkSurfaceProps(flags, (SkPixelGeometry)pixel_geometry)};
}

void skiac_sk_surface_props_unref(skiac_sk_surface_props_t *props) {
  if (props) {
    delete props->props;
    delete props;
  }
}

//=================================================================================================
// SkSurface
//=================================================================================================
skiac_sk_surface_t *skiac_sk_surface_wrap_backend_render_target(
    skiac_gr_direct_context_t *context,
    skiac_gr_backend_render_target_t *target, skiac_gr_surface_origin_t origin,
    skiac_sk_color_type_t color_type, skiac_sk_color_space_t *color_space,
    skiac_sk_surface_props_t *props) {
  GrSurfaceOrigin gr_origin = (origin == GR_SURFACE_ORIGIN_TOP_LEFT)
                                  ? kTopLeft_GrSurfaceOrigin
                                  : kBottomLeft_GrSurfaceOrigin;
  SkColorType sk_color_type;
  switch (color_type) {
  case SK_COLOR_TYPE_RGBA_8888:
    sk_color_type = kRGBA_8888_SkColorType;
    break;
  case SK_COLOR_TYPE_N32:
    sk_color_type = kN32_SkColorType;
    break;
  default:
    sk_color_type = kUnknown_SkColorType;
    break;
  }
  auto surface =
      SkSurfaces::WrapBackendRenderTarget(
          context->context, *target->target, gr_origin, sk_color_type,
          sk_sp<SkColorSpace>(color_space->color_space),
          props ? props->props : nullptr)
          .release();
  return new skiac_sk_surface_t{surface};
}

void skiac_sk_surface_unref(skiac_sk_surface_t *surface) {
  if (surface) {
    surface->surface->unref();
    delete surface;
  }
}

skiac_sk_canvas_t *skiac_sk_surface_get_canvas(skiac_sk_surface_t *surface) {
  return new skiac_sk_canvas_t{surface->surface->getCanvas()};
}

//=================================================================================================
// SkCanvas
//=================================================================================================
void skiac_sk_canvas_clear(skiac_sk_canvas_t *canvas, uint32_t color) {
  canvas->canvas->clear(color);
}

void skiac_sk_canvas_draw_rect(skiac_sk_canvas_t *canvas,
                               const skiac_rect_t *rect,
                               const skiac_sk_paint_t *paint) {
  SkRect sk_rect =
      SkRect::MakeXYWH(rect->x, rect->y, rect->width, rect->height);
  canvas->canvas->drawRect(sk_rect, *paint->paint);
}

void skiac_sk_canvas_draw_circle(skiac_sk_canvas_t *canvas, float cx, float cy,
                                 float radius, const skiac_sk_paint_t *paint) {
  canvas->canvas->drawCircle(cx, cy, radius, *paint->paint);
}

void skiac_sk_canvas_draw_line(skiac_sk_canvas_t *canvas, float x0, float y0,
                               float x1, float y1,
                               const skiac_sk_paint_t *paint) {
  canvas->canvas->drawLine(x0, y0, x1, y1, *paint->paint);
}

void skiac_sk_canvas_draw_point(skiac_sk_canvas_t *canvas, float x, float y,
                                const skiac_sk_paint_t *paint) {
  canvas->canvas->drawPoint(x, y, *paint->paint);
}

void skiac_sk_canvas_draw_oval(skiac_sk_canvas_t *canvas,
                               const skiac_rect_t *oval_bounds,
                               const skiac_sk_paint_t *paint) {
  SkRect r = SkRect::MakeXYWH(oval_bounds->x, oval_bounds->y,
                              oval_bounds->width, oval_bounds->height);
  canvas->canvas->drawOval(r, *paint->paint);
}

void skiac_sk_canvas_draw_round_rect(skiac_sk_canvas_t *canvas,
                                     const skiac_rect_t *rect, float rx,
                                     float ry, const skiac_sk_paint_t *paint) {
  SkRect r = SkRect::MakeXYWH(rect->x, rect->y, rect->width, rect->height);
  canvas->canvas->drawRoundRect(r, rx, ry, *paint->paint);
}

void skiac_sk_canvas_draw_paint(skiac_sk_canvas_t *canvas,
                                const skiac_sk_paint_t *paint) {
  canvas->canvas->drawPaint(*paint->paint);
}

void skiac_sk_canvas_draw_path(skiac_sk_canvas_t *canvas,
                               const skiac_sk_path_t *path,
                               const skiac_sk_paint_t *paint) {
  SkPath p = path->builder->snapshot();
  canvas->canvas->drawPath(p, *paint->paint);
}

void skiac_sk_canvas_draw_image(skiac_sk_canvas_t *canvas,
                                const skiac_sk_image_t *image, float x,
                                float y) {
  canvas->canvas->drawImage(sk_ref_sp(image->image), x, y, SkSamplingOptions());
}

// State/transform/clip
void skiac_sk_canvas_save(skiac_sk_canvas_t *canvas) { canvas->canvas->save(); }

void skiac_sk_canvas_restore(skiac_sk_canvas_t *canvas) {
  canvas->canvas->restore();
}

void skiac_sk_canvas_translate(skiac_sk_canvas_t *canvas, float dx, float dy) {
  canvas->canvas->translate(dx, dy);
}

void skiac_sk_canvas_scale(skiac_sk_canvas_t *canvas, float sx, float sy) {
  canvas->canvas->scale(sx, sy);
}

void skiac_sk_canvas_rotate(skiac_sk_canvas_t *canvas, float degrees) {
  canvas->canvas->rotate(degrees);
}

void skiac_sk_canvas_skew(skiac_sk_canvas_t *canvas, float sx, float sy) {
  canvas->canvas->skew(sx, sy);
}

void skiac_sk_canvas_clip_rect(skiac_sk_canvas_t *canvas,
                               const skiac_rect_t *rect, bool do_aa) {
  SkRect r = SkRect::MakeXYWH(rect->x, rect->y, rect->width, rect->height);
  canvas->canvas->clipRect(r, SkClipOp::kIntersect, do_aa);
}

int skiac_sk_canvas_save_layer(skiac_sk_canvas_t *canvas,
                               const skiac_rect_t *bounds_or_null,
                               const skiac_sk_paint_t *paint_or_null) {
  const SkRect *r = nullptr;
  SkRect tmp;
  if (bounds_or_null) {
    tmp = SkRect::MakeXYWH(bounds_or_null->x, bounds_or_null->y,
                           bounds_or_null->width, bounds_or_null->height);
    r = &tmp;
  }
  const SkPaint *p = paint_or_null ? paint_or_null->paint : nullptr;
  return canvas->canvas->saveLayer(r, p);
}

void skiac_sk_canvas_concat(skiac_sk_canvas_t *canvas,
                            const skiac_matrix_t *mat) {
  SkMatrix m;
  m.setAll(mat->m00, mat->m01, mat->m02, mat->m10, mat->m11, mat->m12, mat->m20,
           mat->m21, mat->m22);
  canvas->canvas->concat(m);
}

void skiac_sk_canvas_clip_path(skiac_sk_canvas_t *canvas,
                               const skiac_sk_path_t *path, bool do_aa) {
  SkPath p = path->builder->snapshot();
  canvas->canvas->clipPath(p, SkClipOp::kIntersect, do_aa);
}

void skiac_sk_canvas_set_matrix(skiac_sk_canvas_t *canvas,
                                const skiac_matrix_t *mat) {
  SkMatrix m;
  m.setAll(mat->m00, mat->m01, mat->m02, mat->m10, mat->m11, mat->m12, mat->m20,
           mat->m21, mat->m22);
  canvas->canvas->setMatrix(m);
}

void skiac_sk_canvas_reset_matrix(skiac_sk_canvas_t *canvas) {
  canvas->canvas->resetMatrix();
}

void skiac_sk_canvas_draw_arc(skiac_sk_canvas_t *canvas,
                              const skiac_rect_t *oval_bounds,
                              float start_angle_deg, float sweep_angle_deg,
                              bool use_center, const skiac_sk_paint_t *paint) {
  SkRect r = SkRect::MakeXYWH(oval_bounds->x, oval_bounds->y,
                              oval_bounds->width, oval_bounds->height);
  canvas->canvas->drawArc(r, start_angle_deg, sweep_angle_deg, use_center,
                          *paint->paint);
}

void skiac_sk_canvas_clip_oval(skiac_sk_canvas_t *canvas,
                               const skiac_rect_t *oval_bounds, bool do_aa) {
  SkPathBuilder b;
  SkRect r = SkRect::MakeXYWH(oval_bounds->x, oval_bounds->y,
                              oval_bounds->width, oval_bounds->height);
  b.addOval(r);
  SkPath p = b.snapshot();
  canvas->canvas->clipPath(p, SkClipOp::kIntersect, do_aa);
}

void skiac_sk_canvas_clip_round_rect(skiac_sk_canvas_t *canvas,
                                     const skiac_rect_t *rect, float rx,
                                     float ry, bool do_aa) {
  SkRRect rr;
  SkRect r = SkRect::MakeXYWH(rect->x, rect->y, rect->width, rect->height);
  rr.setRectXY(r, rx, ry);
  canvas->canvas->clipRRect(rr, SkClipOp::kIntersect, do_aa);
}

int skiac_sk_canvas_save_count(const skiac_sk_canvas_t *canvas) {
  return canvas->canvas->getSaveCount();
}

void skiac_sk_canvas_restore_to_count(skiac_sk_canvas_t *canvas,
                                      int save_count) {
  canvas->canvas->restoreToCount(save_count);
}

void skiac_sk_canvas_draw_rrect(skiac_sk_canvas_t *canvas,
                                const skiac_rect_t *rect, float rx, float ry,
                                const skiac_sk_paint_t *paint) {
  SkRRect rr;
  SkRect r = SkRect::MakeXYWH(rect->x, rect->y, rect->width, rect->height);
  rr.setRectXY(r, rx, ry);
  canvas->canvas->drawRRect(rr, *paint->paint);
}

void skiac_sk_canvas_draw_drrect(skiac_sk_canvas_t *canvas,
                                 const skiac_rect_t *outer_rect, float outer_rx,
                                 float outer_ry, const skiac_rect_t *inner_rect,
                                 float inner_rx, float inner_ry,
                                 const skiac_sk_paint_t *paint) {
  SkRRect outer;
  SkRRect inner;
  SkRect ro = SkRect::MakeXYWH(outer_rect->x, outer_rect->y, outer_rect->width,
                               outer_rect->height);
  SkRect ri = SkRect::MakeXYWH(inner_rect->x, inner_rect->y, inner_rect->width,
                               inner_rect->height);
  outer.setRectXY(ro, outer_rx, outer_ry);
  inner.setRectXY(ri, inner_rx, inner_ry);
  canvas->canvas->drawDRRect(outer, inner, *paint->paint);
}

//=================================================================================================
// SkPaint
//=================================================================================================
skiac_sk_paint_t *skiac_sk_paint_create() {
  return new skiac_sk_paint_t{new SkPaint()};
}

void skiac_sk_paint_unref(skiac_sk_paint_t *paint) {
  if (paint) {
    delete paint->paint;
    delete paint;
  }
}

void skiac_sk_paint_set_anti_alias(skiac_sk_paint_t *paint, bool anti_alias) {
  paint->paint->setAntiAlias(anti_alias);
}

bool skiac_sk_paint_is_anti_alias(const skiac_sk_paint_t *paint) {
  return paint->paint->isAntiAlias();
}

void skiac_sk_paint_set_color(skiac_sk_paint_t *paint, uint32_t color) {
  paint->paint->setColor(color);
}

uint32_t skiac_sk_paint_get_color(const skiac_sk_paint_t *paint) {
  return paint->paint->getColor();
}

void skiac_sk_paint_set_alpha(skiac_sk_paint_t *paint, uint8_t alpha) {
  SkColor c = paint->paint->getColor();
  paint->paint->setColor(SkColorSetA(c, alpha));
}

uint8_t skiac_sk_paint_get_alpha(const skiac_sk_paint_t *paint) {
  return SkColorGetA(paint->paint->getColor());
}

void skiac_sk_paint_set_dither(skiac_sk_paint_t *paint, bool dither) {
  paint->paint->setDither(dither);
}

bool skiac_sk_paint_is_dither(const skiac_sk_paint_t *paint) {
  return paint->paint->isDither();
}

void skiac_sk_paint_set_stroke_width(skiac_sk_paint_t *paint, float width) {
  paint->paint->setStrokeWidth(width);
}

float skiac_sk_paint_get_stroke_width(const skiac_sk_paint_t *paint) {
  return paint->paint->getStrokeWidth();
}

void skiac_sk_paint_set_stroke_miter(skiac_sk_paint_t *paint, float miter) {
  paint->paint->setStrokeMiter(miter);
}

float skiac_sk_paint_get_stroke_miter(const skiac_sk_paint_t *paint) {
  return paint->paint->getStrokeMiter();
}

void skiac_sk_paint_set_stroke_cap(skiac_sk_paint_t *paint,
                                   skiac_sk_paint_cap_t cap) {
  SkPaint::Cap c = SkPaint::kButt_Cap;
  switch (cap) {
  case SK_PAINT_CAP_ROUND:
    c = SkPaint::kRound_Cap;
    break;
  case SK_PAINT_CAP_SQUARE:
    c = SkPaint::kSquare_Cap;
    break;
  case SK_PAINT_CAP_BUTT:
  default:
    c = SkPaint::kButt_Cap;
    break;
  }
  paint->paint->setStrokeCap(c);
}

skiac_sk_paint_cap_t
skiac_sk_paint_get_stroke_cap(const skiac_sk_paint_t *paint) {
  switch (paint->paint->getStrokeCap()) {
  case SkPaint::kRound_Cap:
    return SK_PAINT_CAP_ROUND;
  case SkPaint::kSquare_Cap:
    return SK_PAINT_CAP_SQUARE;
  case SkPaint::kButt_Cap:
  default:
    return SK_PAINT_CAP_BUTT;
  }
}

void skiac_sk_paint_set_stroke_join(skiac_sk_paint_t *paint,
                                    skiac_sk_paint_join_t join) {
  SkPaint::Join j = SkPaint::kMiter_Join;
  switch (join) {
  case SK_PAINT_JOIN_ROUND:
    j = SkPaint::kRound_Join;
    break;
  case SK_PAINT_JOIN_BEVEL:
    j = SkPaint::kBevel_Join;
    break;
  case SK_PAINT_JOIN_MITER:
  default:
    j = SkPaint::kMiter_Join;
    break;
  }
  paint->paint->setStrokeJoin(j);
}

skiac_sk_paint_join_t
skiac_sk_paint_get_stroke_join(const skiac_sk_paint_t *paint) {
  switch (paint->paint->getStrokeJoin()) {
  case SkPaint::kRound_Join:
    return SK_PAINT_JOIN_ROUND;
  case SkPaint::kBevel_Join:
    return SK_PAINT_JOIN_BEVEL;
  case SkPaint::kMiter_Join:
  default:
    return SK_PAINT_JOIN_MITER;
  }
}

void skiac_sk_paint_set_style(skiac_sk_paint_t *paint,
                              skiac_sk_paint_style_t style) {
  SkPaint::Style sk_style;
  switch (style) {
  case SK_PAINT_STYLE_FILL:
    sk_style = SkPaint::kFill_Style;
    break;
  case SK_PAINT_STYLE_STROKE:
    sk_style = SkPaint::kStroke_Style;
    break;
  case SK_PAINT_STYLE_STROKE_AND_FILL:
    sk_style = SkPaint::kStrokeAndFill_Style;
    break;
  }
  paint->paint->setStyle(sk_style);
}

skiac_sk_paint_style_t skiac_sk_paint_get_style(const skiac_sk_paint_t *paint) {
  switch (paint->paint->getStyle()) {
  case SkPaint::kStroke_Style:
    return SK_PAINT_STYLE_STROKE;
  case SkPaint::kStrokeAndFill_Style:
    return SK_PAINT_STYLE_STROKE_AND_FILL;
  case SkPaint::kFill_Style:
  default:
    return SK_PAINT_STYLE_FILL;
  }
}

void skiac_sk_paint_set_blend_mode(skiac_sk_paint_t *paint,
                                   skiac_sk_blend_mode_t mode) {
  SkBlendMode bm = SkBlendMode::kSrcOver;
  switch (mode) {
  case SK_BLENDMODE_CLEAR:
    bm = SkBlendMode::kClear;
    break;
  case SK_BLENDMODE_SRC:
    bm = SkBlendMode::kSrc;
    break;
  case SK_BLENDMODE_DST:
    bm = SkBlendMode::kDst;
    break;
  case SK_BLENDMODE_SRC_OVER:
    bm = SkBlendMode::kSrcOver;
    break;
  case SK_BLENDMODE_DST_OVER:
    bm = SkBlendMode::kDstOver;
    break;
  case SK_BLENDMODE_MULTIPLY:
    bm = SkBlendMode::kMultiply;
    break;
  case SK_BLENDMODE_SCREEN:
    bm = SkBlendMode::kScreen;
    break;
  case SK_BLENDMODE_OVERLAY:
    bm = SkBlendMode::kOverlay;
    break;
  case SK_BLENDMODE_DARKEN:
    bm = SkBlendMode::kDarken;
    break;
  case SK_BLENDMODE_LIGHTEN:
    bm = SkBlendMode::kLighten;
    break;
  }
  paint->paint->setBlendMode(bm);
}

skiac_sk_blend_mode_t
skiac_sk_paint_get_blend_mode(const skiac_sk_paint_t *paint) {
  SkBlendMode bm = SkBlendMode::kSrcOver;
  if (auto obm = paint->paint->asBlendMode()) {
    bm = *obm;
  }
  switch (bm) {
  case SkBlendMode::kClear:
    return SK_BLENDMODE_CLEAR;
  case SkBlendMode::kSrc:
    return SK_BLENDMODE_SRC;
  case SkBlendMode::kDst:
    return SK_BLENDMODE_DST;
  case SkBlendMode::kSrcOver:
    return SK_BLENDMODE_SRC_OVER;
  case SkBlendMode::kDstOver:
    return SK_BLENDMODE_DST_OVER;
  case SkBlendMode::kMultiply:
    return SK_BLENDMODE_MULTIPLY;
  case SkBlendMode::kScreen:
    return SK_BLENDMODE_SCREEN;
  case SkBlendMode::kOverlay:
    return SK_BLENDMODE_OVERLAY;
  case SkBlendMode::kDarken:
    return SK_BLENDMODE_DARKEN;
  case SkBlendMode::kLighten:
    return SK_BLENDMODE_LIGHTEN;
  default:
    return SK_BLENDMODE_SRC_OVER;
  }
}

// SkPath
skiac_sk_path_t *skiac_sk_path_create() {
  return new skiac_sk_path_t{new SkPathBuilder()};
}

void skiac_sk_path_unref(skiac_sk_path_t *path) {
  if (path) {
    delete path->builder;
    delete path;
  }
}

void skiac_sk_path_move_to(skiac_sk_path_t *path, float x, float y) {
  path->builder->moveTo(x, y);
}

void skiac_sk_path_line_to(skiac_sk_path_t *path, float x, float y) {
  path->builder->lineTo(x, y);
}

void skiac_sk_path_quad_to(skiac_sk_path_t *path, float cx, float cy, float x,
                           float y) {
  path->builder->quadTo(cx, cy, x, y);
}

void skiac_sk_path_cubic_to(skiac_sk_path_t *path, float cx1, float cy1,
                            float cx2, float cy2, float x, float y) {
  path->builder->cubicTo(cx1, cy1, cx2, cy2, x, y);
}

void skiac_sk_path_close(skiac_sk_path_t *path) { path->builder->close(); }

void skiac_sk_path_add_rect(skiac_sk_path_t *path, const skiac_rect_t *rect) {
  SkRect r = SkRect::MakeXYWH(rect->x, rect->y, rect->width, rect->height);
  path->builder->addRect(r);
}

void skiac_sk_path_add_circle(skiac_sk_path_t *path, float cx, float cy,
                              float r) {
  path->builder->addCircle(cx, cy, r);
}

void skiac_sk_path_add_oval(skiac_sk_path_t *path, const skiac_rect_t *rect) {
  SkRect r = SkRect::MakeXYWH(rect->x, rect->y, rect->width, rect->height);
  path->builder->addOval(r);
}

void skiac_sk_path_add_round_rect(skiac_sk_path_t *path,
                                  const skiac_rect_t *rect, float rx,
                                  float ry) {
  SkRect r = SkRect::MakeXYWH(rect->x, rect->y, rect->width, rect->height);
  path->builder->addRRect(SkRRect::MakeRectXY(r, rx, ry));
}

void skiac_sk_path_add_arc(skiac_sk_path_t *path,
                           const skiac_rect_t *oval_bounds,
                           float start_angle_deg, float sweep_angle_deg) {
  SkRect r = SkRect::MakeXYWH(oval_bounds->x, oval_bounds->y,
                              oval_bounds->width, oval_bounds->height);
  path->builder->addArc(r, start_angle_deg, sweep_angle_deg);
}

// SkImage
skiac_sk_image_t *
skiac_sk_surface_make_image_snapshot(skiac_sk_surface_t *surface) {
  return new skiac_sk_image_t{surface->surface->makeImageSnapshot().release()};
}

void skiac_sk_image_unref(skiac_sk_image_t *image) {
  if (image) {
    image->image->unref();
    delete image;
  }
}

//=================================================================================================
// SkFont
//=================================================================================================
skiac_sk_font_t *skiac_sk_font_create_default(float size) {
  auto f = new SkFont();
  f->setSize(size);
  return new skiac_sk_font_t{f};
}

skiac_sk_font_t *skiac_sk_font_create_from_file(const char *path, float size) {
  if (!path)
    return nullptr;
  auto scanner = SkFontScanner_Make_FreeType();
  auto mgr = SkFontMgr_New_FontConfig(nullptr, std::move(scanner));
  if (!mgr)
    return nullptr;
  auto tf = mgr->makeFromFile(path);
  if (!tf)
    return nullptr;
  auto f = new SkFont(tf, size);
  return new skiac_sk_font_t{f};
}

void skiac_sk_font_unref(skiac_sk_font_t *font) {
  if (font) {
    delete font->font;
    delete font;
  }
}

void skiac_sk_font_set_size(skiac_sk_font_t *font, float size) {
  font->font->setSize(size);
}

float skiac_sk_font_get_size(const skiac_sk_font_t *font) {
  return font->font->getSize();
}

float skiac_sk_font_measure_text_width_utf8(const skiac_sk_font_t *font,
                                            const char *text) {
  if (!text)
    return 0.0f;
  size_t len = strlen(text);
  return font->font->measureText(text, len, SkTextEncoding::kUTF8, nullptr);
}

void skiac_sk_canvas_draw_text(skiac_sk_canvas_t *canvas, const char *text,
                               float x, float y, const skiac_sk_font_t *font,
                               const skiac_sk_paint_t *paint) {
  if (!text)
    return;
  size_t len = strlen(text);
  canvas->canvas->drawSimpleText(text, len, SkTextEncoding::kUTF8, x, y,
                                 *font->font, *paint->paint);
}

void skiac_sk_font_set_edging(skiac_sk_font_t *font,
                              skiac_sk_font_edging_t edging) {
  SkFont::Edging e = SkFont::Edging::kAlias;
  switch (edging) {
  case SK_FONT_EDGING_ANTIALIAS:
    e = SkFont::Edging::kAntiAlias;
    break;
  case SK_FONT_EDGING_SUBPIXEL_ANTIALIAS:
    e = SkFont::Edging::kSubpixelAntiAlias;
    break;
  case SK_FONT_EDGING_ALIAS:
  default:
    e = SkFont::Edging::kAlias;
    break;
  }
  font->font->setEdging(e);
}

skiac_sk_font_edging_t skiac_sk_font_get_edging(const skiac_sk_font_t *font) {
  switch (font->font->getEdging()) {
  case SkFont::Edging::kAntiAlias:
    return SK_FONT_EDGING_ANTIALIAS;
  case SkFont::Edging::kSubpixelAntiAlias:
    return SK_FONT_EDGING_SUBPIXEL_ANTIALIAS;
  case SkFont::Edging::kAlias:
  default:
    return SK_FONT_EDGING_ALIAS;
  }
}

void skiac_sk_font_set_hinting(skiac_sk_font_t *font,
                               skiac_sk_font_hinting_t hinting) {
  SkFontHinting h = SkFontHinting::kNone;
  switch (hinting) {
  case SK_FONT_HINTING_SLIGHT:
    h = SkFontHinting::kSlight;
    break;
  case SK_FONT_HINTING_NORMAL:
    h = SkFontHinting::kNormal;
    break;
  case SK_FONT_HINTING_FULL:
    h = SkFontHinting::kFull;
    break;
  case SK_FONT_HINTING_NONE:
  default:
    h = SkFontHinting::kNone;
    break;
  }
  font->font->setHinting(h);
}

skiac_sk_font_hinting_t skiac_sk_font_get_hinting(const skiac_sk_font_t *font) {
  switch (font->font->getHinting()) {
  case SkFontHinting::kSlight:
    return SK_FONT_HINTING_SLIGHT;
  case SkFontHinting::kNormal:
    return SK_FONT_HINTING_NORMAL;
  case SkFontHinting::kFull:
    return SK_FONT_HINTING_FULL;
  case SkFontHinting::kNone:
  default:
    return SK_FONT_HINTING_NONE;
  }
}

void skiac_sk_font_set_subpixel(skiac_sk_font_t *font, bool subpixel) {
  font->font->setSubpixel(subpixel);
}
void skiac_sk_font_set_linear_metrics(skiac_sk_font_t *font, bool linear) {
  font->font->setLinearMetrics(linear);
}
void skiac_sk_font_set_embolden(skiac_sk_font_t *font, bool embolden) {
  font->font->setEmbolden(embolden);
}
void skiac_sk_font_set_baseline_snap(skiac_sk_font_t *font, bool snap) {
  font->font->setBaselineSnap(snap);
}

float skiac_sk_font_get_spacing(const skiac_sk_font_t *font) {
  return font->font->getSpacing();
}

float skiac_sk_font_get_metrics(const skiac_sk_font_t *font,
                                skiac_sk_font_metrics_t *out_metrics_or_null) {
  SkFontMetrics m;
  SkScalar spacing = font->font->getMetrics(&m);
  if (out_metrics_or_null) {
    out_metrics_or_null->flags = m.fFlags;
    out_metrics_or_null->top = m.fTop;
    out_metrics_or_null->ascent = m.fAscent;
    out_metrics_or_null->descent = m.fDescent;
    out_metrics_or_null->bottom = m.fBottom;
    out_metrics_or_null->leading = m.fLeading;
    out_metrics_or_null->avgCharWidth = m.fAvgCharWidth;
    out_metrics_or_null->maxCharWidth = m.fMaxCharWidth;
    out_metrics_or_null->xMin = m.fXMin;
    out_metrics_or_null->xMax = m.fXMax;
    out_metrics_or_null->xHeight = m.fXHeight;
    out_metrics_or_null->capHeight = m.fCapHeight;
    out_metrics_or_null->underlineThickness = m.fUnderlineThickness;
    out_metrics_or_null->underlinePosition = m.fUnderlinePosition;
    out_metrics_or_null->strikeoutThickness = m.fStrikeoutThickness;
    out_metrics_or_null->strikeoutPosition = m.fStrikeoutPosition;
  }
  return spacing;
}

int skiac_sk_font_text_to_glyphs_utf8(const skiac_sk_font_t *font,
                                      const char *text,
                                      uint16_t *out_glyphs_or_null,
                                      int max_glyphs) {
  if (!text)
    return 0;
  size_t len = strlen(text);
  if (!out_glyphs_or_null || max_glyphs <= 0) {
    return (int)font->font->countText(text, len, SkTextEncoding::kUTF8);
  }
  SkSpan<SkGlyphID> dst(reinterpret_cast<SkGlyphID *>(out_glyphs_or_null),
                        (size_t)max_glyphs);
  return (int)font->font->textToGlyphs(text, len, SkTextEncoding::kUTF8, dst);
}

//=================================================================================================
// SkData + Image decode
//=================================================================================================
skiac_sk_data_t *skiac_sk_data_make_with_copy(const void *ptr, size_t len) {
  if (!ptr && len != 0)
    return nullptr;
  auto d = SkData::MakeWithCopy(ptr, len).release();
  return new skiac_sk_data_t{d};
}

skiac_sk_data_t *skiac_sk_data_make_from_file(const char *path) {
  if (!path)
    return nullptr;
  auto sp = SkData::MakeFromFileName(path);
  if (!sp)
    return nullptr;
  return new skiac_sk_data_t{sp.release()};
}

void skiac_sk_data_unref(skiac_sk_data_t *data) {
  if (data) {
    if (data->data)
      data->data->unref();
    delete data;
  }
}

skiac_sk_image_t *skiac_sk_image_make_from_encoded(skiac_sk_data_t *data) {
  if (!data || !data->data)
    return nullptr;
  auto img = SkImages::DeferredFromEncodedData(sk_ref_sp(data->data)).release();
  return new skiac_sk_image_t{img};
}

//=================================================================================================
// SkColor
//=================================================================================================
uint32_t skiac_sk_color_set_argb(uint8_t a, uint8_t r, uint8_t g, uint8_t b) {
  return SkColorSetARGB(a, r, g, b);
}

} // extern "C"

// ============================= RuntimeEffect (SkSL) =============================
extern "C" {

skiac_sk_runtime_effect_t *skiac_runtime_effect_make_for_shader(const char *sksl) {
  if (!sksl) return nullptr;
  SkRuntimeEffect::Result res = SkRuntimeEffect::MakeForShader(SkString(sksl));
  if (!res.effect) return nullptr;
  return new skiac_sk_runtime_effect_t{res.effect.release()};
}

void skiac_runtime_effect_unref(skiac_sk_runtime_effect_t *e) {
  if (e) { if (e->e) e->e->unref(); delete e; }
}

size_t skiac_runtime_effect_uniform_size(const skiac_sk_runtime_effect_t *e) {
  return e && e->e ? e->e->uniformSize() : 0;
}

skiac_sk_shader_t *skiac_runtime_effect_make_shader(const skiac_sk_runtime_effect_t *e, const skiac_sk_data_t *uniforms_or_null) {
  if (!e || !e->e) return nullptr;
  sk_sp<const SkData> u = (uniforms_or_null && uniforms_or_null->data)
                              ? sk_ref_sp(uniforms_or_null->data)
                              : SkData::MakeEmpty();
  auto s = e->e->makeShader(u, (sk_sp<SkShader>*)nullptr, 0, nullptr).release();
  return s ? new skiac_sk_shader_t{s} : nullptr;
}

} // extern "C"

// ============================= Effects / Styles impls =============================
extern "C" {

void skiac_sk_shader_unref(skiac_sk_shader_t *shader) { if (shader) { if (shader->shader) shader->shader->unref(); delete shader; } }
void skiac_sk_color_filter_unref(skiac_sk_color_filter_t *cf) { if (cf) { if (cf->cf) cf->cf->unref(); delete cf; } }
void skiac_sk_image_filter_unref(skiac_sk_image_filter_t *f) { if (f) { if (f->f) f->f->unref(); delete f; } }
void skiac_sk_path_effect_unref(skiac_sk_path_effect_t *pe) { if (pe) { if (pe->pe) pe->pe->unref(); delete pe; } }
void skiac_sk_mask_filter_unref(skiac_sk_mask_filter_t *mf) { if (mf) { if (mf->mf) mf->mf->unref(); delete mf; } }

// Color filters
skiac_sk_color_filter_t *skiac_sk_color_filter_make_blend(uint32_t rgba, int blend_mode) {
  auto cf = SkColorFilters::Blend(rgba, (SkBlendMode)blend_mode).release();
  return cf ? new skiac_sk_color_filter_t{cf} : nullptr;
}

skiac_sk_color_filter_t *skiac_sk_color_filter_make_matrix(const float row_major_20[20], bool clamp) {
  auto cf = SkColorFilters::Matrix(row_major_20, clamp ? SkColorFilters::Clamp::kYes : SkColorFilters::Clamp::kNo).release();
  return cf ? new skiac_sk_color_filter_t{cf} : nullptr;
}

// Image filters
skiac_sk_image_filter_t *skiac_sk_image_filter_make_blur(float sx, float sy) {
  auto f = SkImageFilters::Blur(sx, sy, SkTileMode::kDecal, nullptr).release();
  return f ? new skiac_sk_image_filter_t{f} : nullptr;
}

skiac_sk_image_filter_t *skiac_sk_image_filter_make_color_filter(skiac_sk_color_filter_t *cf) {
  if (!cf) return nullptr;
  auto f = SkImageFilters::ColorFilter(sk_ref_sp(cf->cf), nullptr).release();
  return f ? new skiac_sk_image_filter_t{f} : nullptr;
}

// Shaders
static SkTileMode toTileMode(skiac_sk_tile_mode_t m) {
  switch (m) {
    case SK_TILEMODE_REPEAT: return SkTileMode::kRepeat;
    case SK_TILEMODE_MIRROR: return SkTileMode::kMirror;
    case SK_TILEMODE_DECAL:  return SkTileMode::kDecal;
    case SK_TILEMODE_CLAMP: default: return SkTileMode::kClamp;
  }
}

skiac_sk_shader_t *skiac_sk_shader_make_solid_color(uint32_t rgba) {
  auto s = SkShaders::Color(rgba).release();
  return s ? new skiac_sk_shader_t{s} : nullptr;
}

skiac_sk_shader_t *skiac_sk_shader_make_linear_gradient(float x0, float y0, float x1, float y1,
                                                        uint32_t c0, uint32_t c1,
                                                        skiac_sk_tile_mode_t tile_mode) {
  SkPoint pts[2] = { {x0, y0}, {x1, y1} };
  SkColor colors[2] = { c0, c1 };
  auto s = SkGradientShader::MakeLinear(pts, colors, nullptr, 2, toTileMode(tile_mode)).release();
  return s ? new skiac_sk_shader_t{s} : nullptr;
}

// Path effects
skiac_sk_path_effect_t *skiac_sk_path_effect_make_dash(const float *intervals, int count, float phase) {
  if (!intervals || count <= 0) return nullptr;
  auto pe = SkDashPathEffect::Make({intervals, (size_t)count}, phase).release();
  return pe ? new skiac_sk_path_effect_t{pe} : nullptr;
}

skiac_sk_path_effect_t *skiac_sk_path_effect_make_corner(float radius) {
  auto pe = SkCornerPathEffect::Make(radius).release();
  return pe ? new skiac_sk_path_effect_t{pe} : nullptr;
}

skiac_sk_path_effect_t *skiac_sk_path_effect_make_discrete(float seg_length, float dev) {
  auto pe = SkDiscretePathEffect::Make(seg_length, dev).release();
  return pe ? new skiac_sk_path_effect_t{pe} : nullptr;
}

// Mask filters
skiac_sk_mask_filter_t *skiac_sk_mask_filter_make_blur(int style, float sigma) {
  auto mf = SkMaskFilter::MakeBlur((SkBlurStyle)style, sigma).release();
  return mf ? new skiac_sk_mask_filter_t{mf} : nullptr;
}

// Paint setters
void skiac_sk_paint_set_shader(skiac_sk_paint_t *paint, const skiac_sk_shader_t *shader) {
  paint->paint->setShader(shader ? sk_ref_sp(shader->shader) : nullptr);
}
void skiac_sk_paint_set_color_filter(skiac_sk_paint_t *paint, const skiac_sk_color_filter_t *cf) {
  paint->paint->setColorFilter(cf ? sk_ref_sp(cf->cf) : nullptr);
}
void skiac_sk_paint_set_image_filter(skiac_sk_paint_t *paint, const skiac_sk_image_filter_t *f) {
  paint->paint->setImageFilter(f ? sk_ref_sp(f->f) : nullptr);
}
void skiac_sk_paint_set_path_effect(skiac_sk_paint_t *paint, const skiac_sk_path_effect_t *pe) {
  paint->paint->setPathEffect(pe ? sk_ref_sp(pe->pe) : nullptr);
}
void skiac_sk_paint_set_mask_filter(skiac_sk_paint_t *paint, const skiac_sk_mask_filter_t *mf) {
  paint->paint->setMaskFilter(mf ? sk_ref_sp(mf->mf) : nullptr);
}

} // extern "C"
