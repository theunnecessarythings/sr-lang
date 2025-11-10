#include "skiac.h"
#include <GLFW/glfw3.h>
#include <stdio.h>
#include <stdlib.h>

static void fatal(const char *msg) {
  fprintf(stderr, "Fatal: %s\n", msg);
  fflush(stderr);
  exit(1);
}

static GrGLFuncPtr glfw_get_proc_address(void *ctx, const char *name) {
  (void)ctx;
  return (GrGLFuncPtr)glfwGetProcAddress(name);
}

int main() {
  if (!glfwInit()) {
    fatal("glfwInit failed");
  }

  glfwWindowHint(GLFW_CONTEXT_VERSION_MAJOR, 3);
  glfwWindowHint(GLFW_CONTEXT_VERSION_MINOR, 3);
  glfwWindowHint(GLFW_OPENGL_PROFILE, GLFW_OPENGL_CORE_PROFILE);

  GLFWwindow *window =
      glfwCreateWindow(800, 600, "Skia + GLFW (C)", NULL, NULL);
  if (!window) {
    fatal("glfwCreateWindow failed");
  }

  glfwMakeContextCurrent(window);
  glfwSwapInterval(1); // vsync

  const GrGLInterface *gl_interface =
      skiac_gr_gl_make_assembled_interface(NULL, glfw_get_proc_address);
  if (!gl_interface) {
    fatal("skiac_gr_gl_make_assembled_interface failed");
  }

  skiac_gr_direct_context_t *dctx =
      skiac_gr_direct_context_make_gl(gl_interface);
  if (!dctx) {
    fatal("skiac_gr_direct_context_make_gl failed");
  }

  int fb_w, fb_h;
  glfwGetFramebufferSize(window, &fb_w, &fb_h);

  skiac_gr_backend_render_target_t *target =
      skiac_gr_backend_render_target_make_gl(fb_w, fb_h, 1, 8, 0, 0x8058);
  skiac_sk_color_space_t *color_space = skiac_sk_color_space_make_srgb();
  skiac_sk_surface_props_t *props =
      skiac_sk_surface_props_create(0, 1); // kUnknown_SkPixelGeometry

  skiac_sk_surface_t *surface = skiac_sk_surface_wrap_backend_render_target(
      dctx, target, GR_SURFACE_ORIGIN_BOTTOM_LEFT, SK_COLOR_TYPE_N32,
      color_space, props);

  if (!surface) {
    fatal("skiac_sk_surface_wrap_backend_render_target failed");
  }

  while (!glfwWindowShouldClose(window)) {
    glfwPollEvents();

    skiac_sk_canvas_t *canvas = skiac_sk_surface_get_canvas(surface);

    skiac_sk_canvas_clear(canvas, skiac_sk_color_set_argb(255, 0, 0, 0));

    skiac_sk_paint_t *paint = skiac_sk_paint_create();
    skiac_sk_paint_set_anti_alias(paint, true);
    skiac_sk_paint_set_color(
        paint, skiac_sk_color_set_argb(255, 66, 133, 244)); // Google Blue
    skiac_sk_canvas_draw_circle(canvas, fb_w * 0.5f, fb_h * 0.5f,
                                (fb_w < fb_h ? fb_w : fb_h) * 0.25f, paint);

    skiac_sk_paint_set_color(
        paint, skiac_sk_color_set_argb(255, 52, 168, 83)); // Google Green
    skiac_sk_paint_set_stroke_width(paint, 8);
    skiac_sk_paint_set_style(paint, SK_PAINT_STYLE_STROKE);
    skiac_rect_t rect = {40, 40, fb_w - 80.0f, fb_h - 80.0f};
    skiac_sk_canvas_draw_rect(canvas, &rect, paint);

    skiac_sk_paint_unref(paint);

    skiac_gr_direct_context_flush_and_submit(dctx);

    glfwSwapBuffers(window);
  }

  skiac_sk_surface_unref(surface);
  skiac_sk_surface_props_unref(props);
  skiac_sk_color_space_unref(color_space);
  skiac_gr_backend_render_target_unref(target);
  skiac_gr_direct_context_unref(dctx);
  skiac_gr_gl_interface_unref(gl_interface);

  glfwDestroyWindow(window);
  glfwTerminate();

  return 0;
}
