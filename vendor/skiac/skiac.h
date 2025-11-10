#ifndef SKIAC_H
#define SKIAC_H

#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>

#ifdef __cplusplus
extern "C" {
#endif

//=================================================================================================
// Opaque Type Declarations
//=================================================================================================

typedef struct skiac_gr_direct_context_t skiac_gr_direct_context_t;
typedef struct skiac_sk_surface_t skiac_sk_surface_t;
typedef struct skiac_sk_canvas_t skiac_sk_canvas_t;
typedef struct skiac_sk_paint_t skiac_sk_paint_t;
typedef struct skiac_sk_path_t skiac_sk_path_t;
typedef struct skiac_sk_image_t skiac_sk_image_t;
typedef struct skiac_sk_font_t skiac_sk_font_t;
typedef struct skiac_sk_data_t skiac_sk_data_t;
typedef struct skiac_sk_shader_t skiac_sk_shader_t;
typedef struct skiac_sk_color_filter_t skiac_sk_color_filter_t;
typedef struct skiac_sk_image_filter_t skiac_sk_image_filter_t;
typedef struct skiac_sk_path_effect_t skiac_sk_path_effect_t;
typedef struct skiac_sk_mask_filter_t skiac_sk_mask_filter_t;
typedef struct skiac_sk_runtime_effect_t skiac_sk_runtime_effect_t;
typedef struct skiac_sk_color_space_t skiac_sk_color_space_t;
typedef struct skiac_sk_surface_props_t skiac_sk_surface_props_t;
typedef struct skiac_gr_gl_framebuffer_info_t skiac_gr_gl_framebuffer_info_t;
typedef struct skiac_gr_backend_render_target_t skiac_gr_backend_render_target_t;
typedef struct skiac_sk_rect_t skiac_sk_rect_t;
typedef struct GrGLInterface GrGLInterface;

typedef struct {
    float m00, m01, m02;
    float m10, m11, m12;
    float m20, m21, m22;
} skiac_matrix_t;

//=================================================================================================
// Enums
//=================================================================================================

typedef enum {
    GR_SURFACE_ORIGIN_TOP_LEFT,
    GR_SURFACE_ORIGIN_BOTTOM_LEFT,
} skiac_gr_surface_origin_t;

typedef enum {
    SK_COLOR_TYPE_UNKNOWN,
    SK_COLOR_TYPE_RGBA_8888,
    SK_COLOR_TYPE_N32,
} skiac_sk_color_type_t;

typedef enum {
    SK_PAINT_STYLE_FILL,
    SK_PAINT_STYLE_STROKE,
    SK_PAINT_STYLE_STROKE_AND_FILL,
} skiac_sk_paint_style_t;

typedef enum {
    SK_BLENDMODE_CLEAR,
    SK_BLENDMODE_SRC,
    SK_BLENDMODE_DST,
    SK_BLENDMODE_SRC_OVER,
    SK_BLENDMODE_DST_OVER,
    SK_BLENDMODE_MULTIPLY,
    SK_BLENDMODE_SCREEN,
    SK_BLENDMODE_OVERLAY,
    SK_BLENDMODE_DARKEN,
    SK_BLENDMODE_LIGHTEN,
} skiac_sk_blend_mode_t;

typedef enum {
    SK_PAINT_CAP_BUTT,
    SK_PAINT_CAP_ROUND,
    SK_PAINT_CAP_SQUARE,
} skiac_sk_paint_cap_t;

typedef enum {
    SK_PAINT_JOIN_MITER,
    SK_PAINT_JOIN_ROUND,
    SK_PAINT_JOIN_BEVEL,
} skiac_sk_paint_join_t;

//=================================================================================================
// Structs
//=================================================================================================

typedef struct {
    float x;
    float y;
    float width;
    float height;
} skiac_rect_t;

//=================================================================================================
// Function Pointers
//=================================================================================================

typedef void (*GrGLFuncPtr)();
typedef GrGLFuncPtr (*GrGLGetProc)(void* ctx, const char name[]);

//=================================================================================================
// Function Declarations
//=================================================================================================

// GrGLInterface
const GrGLInterface* skiac_gr_gl_make_assembled_interface(void* ctx, GrGLGetProc get_proc);
void skiac_gr_gl_interface_unref(const GrGLInterface* interface);

// GrDirectContext
skiac_gr_direct_context_t* skiac_gr_direct_context_make_gl(const GrGLInterface* gl_interface);
void skiac_gr_direct_context_unref(skiac_gr_direct_context_t* context);
void skiac_gr_direct_context_flush_and_submit(skiac_gr_direct_context_t* context);

// GrBackendRenderTarget
skiac_gr_backend_render_target_t* skiac_gr_backend_render_target_make_gl(int width, int height, int sample_cnt, int stencil_bits, unsigned int fbo_id, unsigned int format);
void skiac_gr_backend_render_target_unref(skiac_gr_backend_render_target_t* target);

// SkColorSpace
skiac_sk_color_space_t* skiac_sk_color_space_make_srgb();
void skiac_sk_color_space_unref(skiac_sk_color_space_t* color_space);

// SkSurfaceProps
skiac_sk_surface_props_t* skiac_sk_surface_props_create(uint32_t flags, int pixel_geometry);
void skiac_sk_surface_props_unref(skiac_sk_surface_props_t* props);

// SkSurface
skiac_sk_surface_t* skiac_sk_surface_wrap_backend_render_target(
    skiac_gr_direct_context_t* context,
    skiac_gr_backend_render_target_t* target,
    skiac_gr_surface_origin_t origin,
    skiac_sk_color_type_t color_type,
    skiac_sk_color_space_t* color_space,
    skiac_sk_surface_props_t* props
);
void skiac_sk_surface_unref(skiac_sk_surface_t* surface);
skiac_sk_canvas_t* skiac_sk_surface_get_canvas(skiac_sk_surface_t* surface);

// SkCanvas
void skiac_sk_canvas_clear(skiac_sk_canvas_t* canvas, uint32_t color);
void skiac_sk_canvas_draw_rect(skiac_sk_canvas_t* canvas, const skiac_rect_t* rect, const skiac_sk_paint_t* paint);
void skiac_sk_canvas_draw_circle(skiac_sk_canvas_t* canvas, float cx, float cy, float radius, const skiac_sk_paint_t* paint);
void skiac_sk_canvas_draw_line(skiac_sk_canvas_t* canvas, float x0, float y0, float x1, float y1, const skiac_sk_paint_t* paint);
void skiac_sk_canvas_draw_point(skiac_sk_canvas_t* canvas, float x, float y, const skiac_sk_paint_t* paint);
void skiac_sk_canvas_draw_oval(skiac_sk_canvas_t* canvas, const skiac_rect_t* oval_bounds, const skiac_sk_paint_t* paint);
void skiac_sk_canvas_draw_round_rect(skiac_sk_canvas_t* canvas, const skiac_rect_t* rect, float rx, float ry, const skiac_sk_paint_t* paint);
void skiac_sk_canvas_draw_paint(skiac_sk_canvas_t* canvas, const skiac_sk_paint_t* paint);
void skiac_sk_canvas_draw_path(skiac_sk_canvas_t* canvas, const skiac_sk_path_t* path, const skiac_sk_paint_t* paint);
void skiac_sk_canvas_draw_image(skiac_sk_canvas_t* canvas, const skiac_sk_image_t* image, float x, float y);

// SkCanvas state/transform/clip
void skiac_sk_canvas_save(skiac_sk_canvas_t* canvas);
void skiac_sk_canvas_restore(skiac_sk_canvas_t* canvas);
void skiac_sk_canvas_translate(skiac_sk_canvas_t* canvas, float dx, float dy);
void skiac_sk_canvas_scale(skiac_sk_canvas_t* canvas, float sx, float sy);
void skiac_sk_canvas_rotate(skiac_sk_canvas_t* canvas, float degrees);
void skiac_sk_canvas_skew(skiac_sk_canvas_t* canvas, float sx, float sy);
void skiac_sk_canvas_clip_rect(skiac_sk_canvas_t* canvas, const skiac_rect_t* rect, bool do_aa);
int  skiac_sk_canvas_save_layer(skiac_sk_canvas_t* canvas, const skiac_rect_t* bounds_or_null, const skiac_sk_paint_t* paint_or_null);
void skiac_sk_canvas_concat(skiac_sk_canvas_t* canvas, const skiac_matrix_t* mat);
void skiac_sk_canvas_clip_path(skiac_sk_canvas_t* canvas, const skiac_sk_path_t* path, bool do_aa);
void skiac_sk_canvas_set_matrix(skiac_sk_canvas_t* canvas, const skiac_matrix_t* mat);
void skiac_sk_canvas_reset_matrix(skiac_sk_canvas_t* canvas);
void skiac_sk_canvas_draw_arc(skiac_sk_canvas_t* canvas, const skiac_rect_t* oval_bounds, float start_angle_deg, float sweep_angle_deg, bool use_center, const skiac_sk_paint_t* paint);
void skiac_sk_canvas_clip_oval(skiac_sk_canvas_t* canvas, const skiac_rect_t* oval_bounds, bool do_aa);
void skiac_sk_canvas_clip_round_rect(skiac_sk_canvas_t* canvas, const skiac_rect_t* rect, float rx, float ry, bool do_aa);
int  skiac_sk_canvas_save_count(const skiac_sk_canvas_t* canvas);
void skiac_sk_canvas_restore_to_count(skiac_sk_canvas_t* canvas, int save_count);
void skiac_sk_canvas_draw_rrect(skiac_sk_canvas_t* canvas, const skiac_rect_t* rect, float rx, float ry, const skiac_sk_paint_t* paint);
void skiac_sk_canvas_draw_drrect(skiac_sk_canvas_t* canvas, const skiac_rect_t* outer_rect, float outer_rx, float outer_ry, const skiac_rect_t* inner_rect, float inner_rx, float inner_ry, const skiac_sk_paint_t* paint);

// SkPaint
skiac_sk_paint_t* skiac_sk_paint_create();
void skiac_sk_paint_unref(skiac_sk_paint_t* paint);
void skiac_sk_paint_set_anti_alias(skiac_sk_paint_t* paint, bool anti_alias);
bool skiac_sk_paint_is_anti_alias(const skiac_sk_paint_t* paint);
void skiac_sk_paint_set_color(skiac_sk_paint_t* paint, uint32_t color);
uint32_t skiac_sk_paint_get_color(const skiac_sk_paint_t* paint);
void skiac_sk_paint_set_alpha(skiac_sk_paint_t* paint, uint8_t alpha);
uint8_t skiac_sk_paint_get_alpha(const skiac_sk_paint_t* paint);
void skiac_sk_paint_set_dither(skiac_sk_paint_t* paint, bool dither);
bool skiac_sk_paint_is_dither(const skiac_sk_paint_t* paint);
void skiac_sk_paint_set_stroke_width(skiac_sk_paint_t* paint, float width);
float skiac_sk_paint_get_stroke_width(const skiac_sk_paint_t* paint);
void skiac_sk_paint_set_stroke_miter(skiac_sk_paint_t* paint, float miter);
float skiac_sk_paint_get_stroke_miter(const skiac_sk_paint_t* paint);
void skiac_sk_paint_set_stroke_cap(skiac_sk_paint_t* paint, skiac_sk_paint_cap_t cap);
skiac_sk_paint_cap_t skiac_sk_paint_get_stroke_cap(const skiac_sk_paint_t* paint);
void skiac_sk_paint_set_stroke_join(skiac_sk_paint_t* paint, skiac_sk_paint_join_t join);
skiac_sk_paint_join_t skiac_sk_paint_get_stroke_join(const skiac_sk_paint_t* paint);
void skiac_sk_paint_set_style(skiac_sk_paint_t* paint, skiac_sk_paint_style_t style);
skiac_sk_paint_style_t skiac_sk_paint_get_style(const skiac_sk_paint_t* paint);
void skiac_sk_paint_set_blend_mode(skiac_sk_paint_t* paint, skiac_sk_blend_mode_t mode);
skiac_sk_blend_mode_t skiac_sk_paint_get_blend_mode(const skiac_sk_paint_t* paint);

// SkPath
skiac_sk_path_t* skiac_sk_path_create();
void skiac_sk_path_unref(skiac_sk_path_t* path);
void skiac_sk_path_move_to(skiac_sk_path_t* path, float x, float y);
void skiac_sk_path_line_to(skiac_sk_path_t* path, float x, float y);
void skiac_sk_path_quad_to(skiac_sk_path_t* path, float cx, float cy, float x, float y);
void skiac_sk_path_cubic_to(skiac_sk_path_t* path, float cx1, float cy1, float cx2, float cy2, float x, float y);
void skiac_sk_path_close(skiac_sk_path_t* path);
void skiac_sk_path_add_rect(skiac_sk_path_t* path, const skiac_rect_t* rect);
void skiac_sk_path_add_circle(skiac_sk_path_t* path, float cx, float cy, float r);
void skiac_sk_path_add_oval(skiac_sk_path_t* path, const skiac_rect_t* rect);
void skiac_sk_path_add_round_rect(skiac_sk_path_t* path, const skiac_rect_t* rect, float rx, float ry);
void skiac_sk_path_add_arc(skiac_sk_path_t* path, const skiac_rect_t* oval_bounds, float start_angle_deg, float sweep_angle_deg);

// Font enums and metrics struct
typedef enum {
    SK_FONT_EDGING_ALIAS,
    SK_FONT_EDGING_ANTIALIAS,
    SK_FONT_EDGING_SUBPIXEL_ANTIALIAS,
} skiac_sk_font_edging_t;

typedef enum {
    SK_FONT_HINTING_NONE,
    SK_FONT_HINTING_SLIGHT,
    SK_FONT_HINTING_NORMAL,
    SK_FONT_HINTING_FULL,
} skiac_sk_font_hinting_t;

typedef struct {
    uint32_t flags;
    float top;
    float ascent;
    float descent;
    float bottom;
    float leading;
    float avgCharWidth;
    float maxCharWidth;
    float xMin;
    float xMax;
    float xHeight;
    float capHeight;
    float underlineThickness;
    float underlinePosition;
    float strikeoutThickness;
    float strikeoutPosition;
} skiac_sk_font_metrics_t;

// SkImage
skiac_sk_image_t* skiac_sk_surface_make_image_snapshot(skiac_sk_surface_t* surface);
void skiac_sk_image_unref(skiac_sk_image_t* image);

// SkFont
skiac_sk_font_t* skiac_sk_font_create_default(float size);
skiac_sk_font_t* skiac_sk_font_create_from_file(const char* path, float size);
void skiac_sk_font_unref(skiac_sk_font_t* font);
void skiac_sk_font_set_size(skiac_sk_font_t* font, float size);
float skiac_sk_font_get_size(const skiac_sk_font_t* font);
float skiac_sk_font_measure_text_width_utf8(const skiac_sk_font_t* font, const char* text);
void skiac_sk_canvas_draw_text(skiac_sk_canvas_t* canvas, const char* text, float x, float y, const skiac_sk_font_t* font, const skiac_sk_paint_t* paint);
void skiac_sk_font_set_edging(skiac_sk_font_t* font, skiac_sk_font_edging_t edging);
skiac_sk_font_edging_t skiac_sk_font_get_edging(const skiac_sk_font_t* font);
void skiac_sk_font_set_hinting(skiac_sk_font_t* font, skiac_sk_font_hinting_t hinting);
skiac_sk_font_hinting_t skiac_sk_font_get_hinting(const skiac_sk_font_t* font);
void skiac_sk_font_set_subpixel(skiac_sk_font_t* font, bool subpixel);
void skiac_sk_font_set_linear_metrics(skiac_sk_font_t* font, bool linear);
void skiac_sk_font_set_embolden(skiac_sk_font_t* font, bool embolden);
void skiac_sk_font_set_baseline_snap(skiac_sk_font_t* font, bool snap);
float skiac_sk_font_get_spacing(const skiac_sk_font_t* font);
float skiac_sk_font_get_metrics(const skiac_sk_font_t* font, skiac_sk_font_metrics_t* out_metrics_or_null);
int   skiac_sk_font_text_to_glyphs_utf8(const skiac_sk_font_t* font, const char* text, uint16_t* out_glyphs_or_null, int max_glyphs);

// SkData + Image decode
skiac_sk_data_t* skiac_sk_data_make_with_copy(const void* ptr, size_t len);
skiac_sk_data_t* skiac_sk_data_make_from_file(const char* path);
void skiac_sk_data_unref(skiac_sk_data_t* data);
skiac_sk_image_t* skiac_sk_image_make_from_encoded(skiac_sk_data_t* data);

// ------------------------------------------------------------------------------------
// Effects and styles
// ------------------------------------------------------------------------------------
typedef enum {
    SK_TILEMODE_CLAMP,
    SK_TILEMODE_REPEAT,
    SK_TILEMODE_MIRROR,
    SK_TILEMODE_DECAL,
} skiac_sk_tile_mode_t;

// Unref helpers
void skiac_sk_shader_unref(skiac_sk_shader_t* shader);
void skiac_sk_color_filter_unref(skiac_sk_color_filter_t* cf);
void skiac_sk_image_filter_unref(skiac_sk_image_filter_t* f);
void skiac_sk_path_effect_unref(skiac_sk_path_effect_t* pe);
void skiac_sk_mask_filter_unref(skiac_sk_mask_filter_t* mf);

// Color filters
skiac_sk_color_filter_t* skiac_sk_color_filter_make_blend(uint32_t rgba, int blend_mode);
skiac_sk_color_filter_t* skiac_sk_color_filter_make_matrix(const float row_major_20[20], bool clamp);

// Image filters (simple)
skiac_sk_image_filter_t* skiac_sk_image_filter_make_blur(float sigma_x, float sigma_y);
skiac_sk_image_filter_t* skiac_sk_image_filter_make_color_filter(skiac_sk_color_filter_t* cf);

// Shaders
skiac_sk_shader_t* skiac_sk_shader_make_solid_color(uint32_t rgba);
skiac_sk_shader_t* skiac_sk_shader_make_linear_gradient(float x0, float y0, float x1, float y1,
                                                       uint32_t c0, uint32_t c1,
                                                       skiac_sk_tile_mode_t tile_mode);

// Path effects
skiac_sk_path_effect_t* skiac_sk_path_effect_make_dash(const float* intervals, int count, float phase);
skiac_sk_path_effect_t* skiac_sk_path_effect_make_corner(float radius);
skiac_sk_path_effect_t* skiac_sk_path_effect_make_discrete(float seg_length, float dev);

// Mask filters
skiac_sk_mask_filter_t* skiac_sk_mask_filter_make_blur(int style, float sigma);

// Paint setters
void skiac_sk_paint_set_shader(skiac_sk_paint_t* paint, const skiac_sk_shader_t* shader);
void skiac_sk_paint_set_color_filter(skiac_sk_paint_t* paint, const skiac_sk_color_filter_t* cf);
void skiac_sk_paint_set_image_filter(skiac_sk_paint_t* paint, const skiac_sk_image_filter_t* f);
void skiac_sk_paint_set_path_effect(skiac_sk_paint_t* paint, const skiac_sk_path_effect_t* pe);
void skiac_sk_paint_set_mask_filter(skiac_sk_paint_t* paint, const skiac_sk_mask_filter_t* mf);

// Runtime shader (SkSL)
skiac_sk_runtime_effect_t* skiac_runtime_effect_make_for_shader(const char* sksl);
void skiac_runtime_effect_unref(skiac_sk_runtime_effect_t* e);
size_t skiac_runtime_effect_uniform_size(const skiac_sk_runtime_effect_t* e);
skiac_sk_shader_t* skiac_runtime_effect_make_shader(const skiac_sk_runtime_effect_t* e, const skiac_sk_data_t* uniforms_or_null);

// SkColor
uint32_t skiac_sk_color_set_argb(uint8_t a, uint8_t r, uint8_t g, uint8_t b);


#ifdef __cplusplus
}
#endif

#endif // SKIAC_H
