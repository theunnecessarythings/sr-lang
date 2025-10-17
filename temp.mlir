#di_basic_type = #llvm.di_basic_type<tag = DW_TAG_base_type, name = "i32", sizeInBits = 32, encoding = DW_ATE_signed>
#di_file = #llvm.di_file<"main.sr" in "../anim-sr">
#distinct = distinct[0]<"cu_0">
#distinct1 = distinct[1]<"sp_1">
#di_compile_unit = #llvm.di_compile_unit<id = #distinct, sourceLanguage = DW_LANG_C11, file = #di_file, producer = "sr-lang", isOptimized = false, emissionKind = Full>
#di_subroutine_type = #llvm.di_subroutine_type<types = #di_basic_type>
#di_subprogram = #llvm.di_subprogram<recId = distinct[2]<>, id = #distinct1, compileUnit = #di_compile_unit, scope = #di_file, name = "main", linkageName = "main", file = #di_file, line = 4, scopeLine = 4, subprogramFlags = Definition, type = #di_subroutine_type>
module attributes {llvm.data_layout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128", llvm.dbg.cu = [#di_compile_unit], llvm.ident = ["sr-lang compiler"], llvm.module.flags = [#llvm.mlir.module_flag<warning, "Debug Info Version", 3 : i32>, #llvm.mlir.module_flag<max, "Dwarf Version", 5 : i32>], llvm.target_triple = "x86_64-unknown-linux-gnu"} {
  llvm.mlir.global internal @int() {addr_space = 0 : i32, sym_visibility = "private"} : !llvm.ptr
  llvm.mlir.global internal @Vector2() {addr_space = 0 : i32, sym_visibility = "private"} : !llvm.ptr
  llvm.mlir.global internal @Vector3() {addr_space = 0 : i32, sym_visibility = "private"} : !llvm.ptr
  llvm.mlir.global internal @Vector4() {addr_space = 0 : i32, sym_visibility = "private"} : !llvm.ptr
  llvm.mlir.global internal @Quaternion() {addr_space = 0 : i32, sym_visibility = "private"} : !llvm.ptr
  llvm.mlir.global internal @Matrix() {addr_space = 0 : i32, sym_visibility = "private"} : !llvm.ptr
  llvm.mlir.global internal @Color() {addr_space = 0 : i32, sym_visibility = "private"} : !llvm.ptr
  llvm.mlir.global internal @Rectangle() {addr_space = 0 : i32, sym_visibility = "private"} : !llvm.ptr
  llvm.mlir.global internal @Image() {addr_space = 0 : i32, sym_visibility = "private"} : !llvm.ptr
  llvm.mlir.global internal @Texture() {addr_space = 0 : i32, sym_visibility = "private"} : !llvm.ptr
  llvm.mlir.global internal @Texture2D() {addr_space = 0 : i32, sym_visibility = "private"} : !llvm.ptr
  llvm.mlir.global internal @TextureCubemap() {addr_space = 0 : i32, sym_visibility = "private"} : !llvm.ptr
  llvm.mlir.global internal @RenderTexture() {addr_space = 0 : i32, sym_visibility = "private"} : !llvm.ptr
  llvm.mlir.global internal @RenderTexture2D() {addr_space = 0 : i32, sym_visibility = "private"} : !llvm.ptr
  llvm.mlir.global internal @NPatchInfo() {addr_space = 0 : i32, sym_visibility = "private"} : !llvm.ptr
  llvm.mlir.global internal @GlyphInfo() {addr_space = 0 : i32, sym_visibility = "private"} : !llvm.ptr
  llvm.mlir.global internal @Font() {addr_space = 0 : i32, sym_visibility = "private"} : !llvm.ptr
  llvm.mlir.global internal @Camera3D() {addr_space = 0 : i32, sym_visibility = "private"} : !llvm.ptr
  llvm.mlir.global internal @Camera() {addr_space = 0 : i32, sym_visibility = "private"} : !llvm.ptr
  llvm.mlir.global internal @Camera2D() {addr_space = 0 : i32, sym_visibility = "private"} : !llvm.ptr
  llvm.mlir.global internal @Mesh() {addr_space = 0 : i32, sym_visibility = "private"} : !llvm.ptr
  llvm.mlir.global internal @Shader() {addr_space = 0 : i32, sym_visibility = "private"} : !llvm.ptr
  llvm.mlir.global internal @MaterialMap() {addr_space = 0 : i32, sym_visibility = "private"} : !llvm.ptr
  llvm.mlir.global internal @Material() {addr_space = 0 : i32, sym_visibility = "private"} : !llvm.ptr
  llvm.mlir.global internal @Transform() {addr_space = 0 : i32, sym_visibility = "private"} : !llvm.ptr
  llvm.mlir.global internal @BoneInfo() {addr_space = 0 : i32, sym_visibility = "private"} : !llvm.ptr
  llvm.mlir.global internal @Model() {addr_space = 0 : i32, sym_visibility = "private"} : !llvm.ptr
  llvm.mlir.global internal @ModelAnimation() {addr_space = 0 : i32, sym_visibility = "private"} : !llvm.ptr
  llvm.mlir.global internal @Ray() {addr_space = 0 : i32, sym_visibility = "private"} : !llvm.ptr
  llvm.mlir.global internal @RayCollision() {addr_space = 0 : i32, sym_visibility = "private"} : !llvm.ptr
  llvm.mlir.global internal @BoundingBox() {addr_space = 0 : i32, sym_visibility = "private"} : !llvm.ptr
  llvm.mlir.global internal @Wave() {addr_space = 0 : i32, sym_visibility = "private"} : !llvm.ptr
  llvm.mlir.global internal @AudioStream() {addr_space = 0 : i32, sym_visibility = "private"} : !llvm.ptr
  llvm.mlir.global internal @Sound() {addr_space = 0 : i32, sym_visibility = "private"} : !llvm.ptr
  llvm.mlir.global internal @Music() {addr_space = 0 : i32, sym_visibility = "private"} : !llvm.ptr
  llvm.mlir.global internal @VrDeviceInfo() {addr_space = 0 : i32, sym_visibility = "private"} : !llvm.ptr
  llvm.mlir.global internal @VrStereoConfig() {addr_space = 0 : i32, sym_visibility = "private"} : !llvm.ptr
  llvm.mlir.global internal @FilePathList() {addr_space = 0 : i32, sym_visibility = "private"} : !llvm.ptr
  llvm.mlir.global internal @ConfigFlags() {addr_space = 0 : i32, sym_visibility = "private"} : !llvm.ptr
  llvm.mlir.global internal @ShaderUniformDataType() {addr_space = 0 : i32, sym_visibility = "private"} : !llvm.ptr
  llvm.mlir.global internal @KeyboardKey() {addr_space = 0 : i32, sym_visibility = "private"} : !llvm.ptr
  llvm.mlir.global internal @MouseButton() {addr_space = 0 : i32, sym_visibility = "private"} : !llvm.ptr
  llvm.mlir.global internal @PixelFormat() {addr_space = 0 : i32, sym_visibility = "private"} : !llvm.ptr
  llvm.mlir.global internal @WHITE() {addr_space = 0 : i32, sym_visibility = "private"} : !llvm.struct<(i8, i8, i8, i8)>
  llvm.mlir.global internal @BLACK() {addr_space = 0 : i32, sym_visibility = "private"} : !llvm.struct<(i8, i8, i8, i8)>
  llvm.mlir.global internal @RED() {addr_space = 0 : i32, sym_visibility = "private"} : !llvm.struct<(i8, i8, i8, i8)>
  llvm.mlir.global internal @GREEN() {addr_space = 0 : i32, sym_visibility = "private"} : !llvm.struct<(i8, i8, i8, i8)>
  llvm.mlir.global internal @BLUE() {addr_space = 0 : i32, sym_visibility = "private"} : !llvm.struct<(i8, i8, i8, i8)>
  llvm.mlir.global internal @YELLOW() {addr_space = 0 : i32, sym_visibility = "private"} : !llvm.struct<(i8, i8, i8, i8)>
  llvm.mlir.global internal @LIGHTGRAY() {addr_space = 0 : i32, sym_visibility = "private"} : !llvm.struct<(i8, i8, i8, i8)>
  llvm.mlir.global internal @GRAY() {addr_space = 0 : i32, sym_visibility = "private"} : !llvm.struct<(i8, i8, i8, i8)>
  llvm.mlir.global internal @RAYWHITE() {addr_space = 0 : i32, sym_visibility = "private"} : !llvm.struct<(i8, i8, i8, i8)>
  llvm.func @SetConfigFlags(i32) attributes {sym_visibility = "private"}
  llvm.func @InitWindow(i64, i64, i64) attributes {sym_visibility = "private"}
  llvm.func @CloseWindow() attributes {sym_visibility = "private"}
  llvm.func @WindowShouldClose() -> i1 attributes {sym_visibility = "private"}
  llvm.func @IsWindowReady() -> i1 attributes {sym_visibility = "private"}
  llvm.func @IsWindowFullscreen() -> i1 attributes {sym_visibility = "private"}
  llvm.func @IsWindowHidden() -> i1 attributes {sym_visibility = "private"}
  llvm.func @IsWindowMinimized() -> i1 attributes {sym_visibility = "private"}
  llvm.func @IsWindowMaximized() -> i1 attributes {sym_visibility = "private"}
  llvm.func @IsWindowFocused() -> i1 attributes {sym_visibility = "private"}
  llvm.func @IsWindowResized() -> i1 attributes {sym_visibility = "private"}
  llvm.func @IsWindowState(i32) -> i1 attributes {sym_visibility = "private"}
  llvm.func @SetWindowState(i32) attributes {sym_visibility = "private"}
  llvm.func @ClearWindowState(i32) attributes {sym_visibility = "private"}
  llvm.func @ToggleFullscreen() attributes {sym_visibility = "private"}
  llvm.func @ToggleBorderlessWindowed() attributes {sym_visibility = "private"}
  llvm.func @MaximizeWindow() attributes {sym_visibility = "private"}
  llvm.func @MinimizeWindow() attributes {sym_visibility = "private"}
  llvm.func @RestoreWindow() attributes {sym_visibility = "private"}
  llvm.func @SetWindowIcon(!llvm.ptr {llvm.align = 8 : i64, llvm.byval = !llvm.struct<(ptr, i64, i64, i64, i64)>}) attributes {sym_visibility = "private"}
  llvm.func @SetWindowIcons(!llvm.ptr, i64) attributes {sym_visibility = "private"}
  llvm.func @SetWindowTitle(i64) attributes {sym_visibility = "private"}
  llvm.func @SetWindowPosition(i64, i64) attributes {sym_visibility = "private"}
  llvm.func @SetWindowMonitor(i64) attributes {sym_visibility = "private"}
  llvm.func @SetWindowMinSize(i64, i64) attributes {sym_visibility = "private"}
  llvm.func @SetWindowMaxSize(i64, i64) attributes {sym_visibility = "private"}
  llvm.func @SetWindowSize(i64, i64) attributes {sym_visibility = "private"}
  llvm.func @SetWindowOpacity(f32) attributes {sym_visibility = "private"}
  llvm.func @SetWindowFocused() attributes {sym_visibility = "private"}
  llvm.func @GetWindowHandle() -> !llvm.ptr attributes {sym_visibility = "private"}
  llvm.func @GetScreenWidth() -> i64 attributes {sym_visibility = "private"}
  llvm.func @GetScreenHeight() -> i64 attributes {sym_visibility = "private"}
  llvm.func @GetRenderWidth() -> i64 attributes {sym_visibility = "private"}
  llvm.func @GetRenderHeight() -> i64 attributes {sym_visibility = "private"}
  llvm.func @GetMonitorCount() -> i64 attributes {sym_visibility = "private"}
  llvm.func @GetCurrentMonitor() -> i64 attributes {sym_visibility = "private"}
  llvm.func @GetMonitorPosition(i64) -> vector<2xf32> attributes {sym_visibility = "private"}
  llvm.func @GetMonitorWidth(i64) -> i64 attributes {sym_visibility = "private"}
  llvm.func @GetMonitorHeight(i64) -> i64 attributes {sym_visibility = "private"}
  llvm.func @SetTargetFPS(i64) attributes {sym_visibility = "private"}
  llvm.func @GetFrameTime() -> f32 attributes {sym_visibility = "private"}
  llvm.func @IsKeyPressed(i64) -> i1 attributes {sym_visibility = "private"}
  llvm.func @IsKeyPressedRepeat(i64) -> i1 attributes {sym_visibility = "private"}
  llvm.func @IsKeyDown(i64) -> i1 attributes {sym_visibility = "private"}
  llvm.func @IsKeyReleased(i64) -> i1 attributes {sym_visibility = "private"}
  llvm.func @IsKeyUp(i64) -> i1 attributes {sym_visibility = "private"}
  llvm.func @GetKeyPressed() -> i64 attributes {sym_visibility = "private"}
  llvm.func @GetCharPressed() -> i64 attributes {sym_visibility = "private"}
  llvm.func @GetKeyName(i64) -> !llvm.ptr attributes {sym_visibility = "private"}
  llvm.func @SetExitKey(i64) attributes {sym_visibility = "private"}
  llvm.func @BeginDrawing() attributes {sym_visibility = "private"}
  llvm.func @EndDrawing() attributes {sym_visibility = "private"}
  llvm.func @ClearBackground(i32) attributes {sym_visibility = "private"}
  llvm.func @DrawText(i64, i64, i64, i64, i32) attributes {sym_visibility = "private"}
  llvm.func @DrawTriangleLines(vector<2xf32>, vector<2xf32>, vector<2xf32>, i32) attributes {sym_visibility = "private"}
  llvm.func @DrawCircleLines(i64, i64, f32, i32) attributes {sym_visibility = "private"}
  llvm.func @LoadTexture(!llvm.ptr {llvm.align = 8 : i64, llvm.sret = !llvm.struct<(i32, i64, i64, i64, i64)>}, !llvm.ptr) attributes {sym_visibility = "private"}
  llvm.func @UnloadTexture(!llvm.ptr {llvm.align = 8 : i64, llvm.byval = !llvm.struct<(i32, i64, i64, i64, i64)>}) attributes {sym_visibility = "private"}
  llvm.func @DrawTexture(!llvm.ptr {llvm.align = 8 : i64, llvm.byval = !llvm.struct<(i32, i64, i64, i64, i64)>}, i64, i64, i32) attributes {sym_visibility = "private"}
  llvm.func @LoadImage(!llvm.ptr {llvm.align = 8 : i64, llvm.sret = !llvm.struct<(ptr, i64, i64, i64, i64)>}, !llvm.ptr) attributes {sym_visibility = "private"}
  llvm.func @UnloadImage(!llvm.ptr {llvm.align = 8 : i64, llvm.byval = !llvm.struct<(ptr, i64, i64, i64, i64)>}) attributes {sym_visibility = "private"}
  llvm.func @ImageFormat(!llvm.ptr, i64) attributes {sym_visibility = "private"}
  llvm.func @ExportImage(!llvm.ptr {llvm.align = 8 : i64, llvm.byval = !llvm.struct<(ptr, i64, i64, i64, i64)>}, !llvm.ptr) -> i1 attributes {sym_visibility = "private"}
  llvm.func @IsMouseButtonPressed(i64) -> i1 attributes {sym_visibility = "private"}
  llvm.func @IsMouseButtonDown(i64) -> i1 attributes {sym_visibility = "private"}
  llvm.func @IsMouseButtonReleased(i64) -> i1 attributes {sym_visibility = "private"}
  llvm.func @IsMouseButtonUp(i64) -> i1 attributes {sym_visibility = "private"}
  llvm.func @GetMouseX() -> i64 attributes {sym_visibility = "private"}
  llvm.func @GetMouseY() -> i64 attributes {sym_visibility = "private"}
  llvm.func @GetMousePosition() -> vector<2xf32> attributes {sym_visibility = "private"}
  llvm.func @GetMouseDelta() -> vector<2xf32> attributes {sym_visibility = "private"}
  llvm.func @SetMousePosition(i64, i64) attributes {sym_visibility = "private"}
  llvm.func @SetMouseOffset(i64, i64) attributes {sym_visibility = "private"}
  llvm.func @SetMouseScale(f32, f32) attributes {sym_visibility = "private"}
  llvm.func @GetMouseWheelMove() -> f32 attributes {sym_visibility = "private"}
  llvm.func @GetMouseWheelMoveV() -> vector<2xf32> attributes {sym_visibility = "private"}
  llvm.func @SetMouseCursor(i64) attributes {sym_visibility = "private"}
  llvm.func @GetTouchX() -> i64 attributes {sym_visibility = "private"}
  llvm.func @GetTouchY() -> i64 attributes {sym_visibility = "private"}
  llvm.func @GetTouchPosition(i64) -> vector<2xf32> attributes {sym_visibility = "private"}
  llvm.func @GetTouchPointId(i64) -> i64 attributes {sym_visibility = "private"}
  llvm.func @GetTouchPointCount() -> i64 attributes {sym_visibility = "private"}
  llvm.func @SetGesturesEnabled(i32) attributes {sym_visibility = "private"}
  llvm.func @IsGestureDetected(i32) -> i1 attributes {sym_visibility = "private"}
  llvm.func @GetGestureDetected() -> i64 attributes {sym_visibility = "private"}
  llvm.func @GetGestureHoldDuration() -> f32 attributes {sym_visibility = "private"}
  llvm.func @GetGestureDragVector() -> vector<2xf32> attributes {sym_visibility = "private"}
  llvm.func @GetGestureDragAngle() -> f32 attributes {sym_visibility = "private"}
  llvm.func @GetGesturePinchVector() -> vector<2xf32> attributes {sym_visibility = "private"}
  llvm.func @GetGesturePinchAngle() -> f32 attributes {sym_visibility = "private"}
  llvm.func @LoadFont(!llvm.ptr {llvm.align = 8 : i64, llvm.sret = !llvm.struct<(i64, i64, i64, struct<(i32, i64, i64, i64, i64)>, ptr, ptr)>}, !llvm.ptr) attributes {sym_visibility = "private"}
  llvm.func @LoadFontEx(!llvm.ptr {llvm.align = 8 : i64, llvm.sret = !llvm.struct<(i64, i64, i64, struct<(i32, i64, i64, i64, i64)>, ptr, ptr)>}, !llvm.ptr, i64, !llvm.ptr, i64) attributes {sym_visibility = "private"}
  llvm.func @UnloadFont(!llvm.ptr {llvm.align = 8 : i64, llvm.byval = !llvm.struct<(i64, i64, i64, struct<(i32, i64, i64, i64, i64)>, ptr, ptr)>}) attributes {sym_visibility = "private"}
  llvm.func @DrawTextEx(!llvm.ptr {llvm.align = 8 : i64, llvm.byval = !llvm.struct<(i64, i64, i64, struct<(i32, i64, i64, i64, i64)>, ptr, ptr)>}, !llvm.ptr, vector<2xf32>, f32, f32, i32) attributes {sym_visibility = "private"}
  llvm.func @MeasureText(!llvm.ptr, i64) -> i64 attributes {sym_visibility = "private"}
  llvm.func @MeasureTextEx(!llvm.ptr {llvm.align = 8 : i64, llvm.byval = !llvm.struct<(i64, i64, i64, struct<(i32, i64, i64, i64, i64)>, ptr, ptr)>}, !llvm.ptr, f32, f32) -> vector<2xf32> attributes {sym_visibility = "private"}
  llvm.func @GetGlyphIndex(!llvm.ptr {llvm.align = 8 : i64, llvm.byval = !llvm.struct<(i64, i64, i64, struct<(i32, i64, i64, i64, i64)>, ptr, ptr)>}, i64) -> i64 attributes {sym_visibility = "private"}
  llvm.func @GetGlyphInfo(!llvm.ptr {llvm.align = 8 : i64, llvm.sret = !llvm.struct<(i64, i64, i64, i64, struct<(ptr, i64, i64, i64, i64)>)>}, !llvm.ptr {llvm.align = 8 : i64, llvm.byval = !llvm.struct<(i64, i64, i64, struct<(i32, i64, i64, i64, i64)>, ptr, ptr)>}, i64) attributes {sym_visibility = "private"}
  llvm.func @GetGlyphAtlasRec(!llvm.ptr {llvm.align = 4 : i64, llvm.sret = !llvm.struct<(f32, f32, f32, f32)>}, !llvm.ptr {llvm.align = 8 : i64, llvm.byval = !llvm.struct<(i64, i64, i64, struct<(i32, i64, i64, i64, i64)>, ptr, ptr)>}, i64) attributes {sym_visibility = "private"}
  llvm.func @DrawPixel(i64, i64, i32) attributes {sym_visibility = "private"}
  llvm.func @DrawLine(i64, i64, i64, i64, i32) attributes {sym_visibility = "private"}
  llvm.func @DrawRectangle(i64, i64, i64, i64, i32) attributes {sym_visibility = "private"}
  llvm.func @DrawCircle(i64, i64, f32, i32) attributes {sym_visibility = "private"}
  llvm.func @BeginMode2D(!llvm.ptr {llvm.align = 4 : i64, llvm.byval = !llvm.struct<(struct<(f32, f32)>, struct<(f32, f32)>, f32, f32)>}) attributes {sym_visibility = "private"}
  llvm.func @EndMode2D() attributes {sym_visibility = "private"}
  llvm.func @UpdateCamera(!llvm.ptr, i64) attributes {sym_visibility = "private"}
  llvm.func @UpdateCameraPro(!llvm.ptr, !llvm.ptr {llvm.align = 4 : i64, llvm.byval = !llvm.struct<(f32, f32, f32)>}, !llvm.ptr {llvm.align = 4 : i64, llvm.byval = !llvm.struct<(f32, f32, f32)>}, f32) attributes {sym_visibility = "private"}
  llvm.func @InitAudioDevice() attributes {sym_visibility = "private"}
  llvm.func @CloseAudioDevice() attributes {sym_visibility = "private"}
  llvm.func @IsAudioDeviceReady() -> i1 attributes {sym_visibility = "private"}
  llvm.func @LoadSound(!llvm.ptr {llvm.align = 8 : i64, llvm.sret = !llvm.struct<(struct<(ptr, ptr, i32, i32, i32)>, i32)>}, !llvm.ptr) attributes {sym_visibility = "private"}
  llvm.func @UnloadSound(!llvm.ptr {llvm.align = 8 : i64, llvm.byval = !llvm.struct<(struct<(ptr, ptr, i32, i32, i32)>, i32)>}) attributes {sym_visibility = "private"}
  llvm.func @PlaySound(!llvm.ptr {llvm.align = 8 : i64, llvm.byval = !llvm.struct<(struct<(ptr, ptr, i32, i32, i32)>, i32)>}) attributes {sym_visibility = "private"}
  llvm.func @LoadModel(!llvm.ptr {llvm.align = 8 : i64, llvm.sret = !llvm.struct<(struct<(f32, f32, f32, f32, f32, f32, f32, f32, f32, f32, f32, f32, f32, f32, f32, f32)>, i64, i64, ptr, ptr, ptr, i64, ptr, ptr)>}, !llvm.ptr) attributes {sym_visibility = "private"}
  llvm.func @UnloadModel(!llvm.ptr {llvm.align = 8 : i64, llvm.byval = !llvm.struct<(struct<(f32, f32, f32, f32, f32, f32, f32, f32, f32, f32, f32, f32, f32, f32, f32, f32)>, i64, i64, ptr, ptr, ptr, i64, ptr, ptr)>}) attributes {sym_visibility = "private"}
  llvm.func @DrawModel(!llvm.ptr {llvm.align = 8 : i64, llvm.byval = !llvm.struct<(struct<(f32, f32, f32, f32, f32, f32, f32, f32, f32, f32, f32, f32, f32, f32, f32, f32)>, i64, i64, ptr, ptr, ptr, i64, ptr, ptr)>}, !llvm.ptr {llvm.align = 4 : i64, llvm.byval = !llvm.struct<(f32, f32, f32)>}, f32, i32) attributes {sym_visibility = "private"}
  llvm.func @DrawModelEx(!llvm.ptr {llvm.align = 8 : i64, llvm.byval = !llvm.struct<(struct<(f32, f32, f32, f32, f32, f32, f32, f32, f32, f32, f32, f32, f32, f32, f32, f32)>, i64, i64, ptr, ptr, ptr, i64, ptr, ptr)>}, !llvm.ptr {llvm.align = 4 : i64, llvm.byval = !llvm.struct<(f32, f32, f32)>}, !llvm.ptr {llvm.align = 4 : i64, llvm.byval = !llvm.struct<(f32, f32, f32)>}, f32, !llvm.ptr {llvm.align = 4 : i64, llvm.byval = !llvm.struct<(f32, f32, f32)>}, i32) attributes {sym_visibility = "private"}
  llvm.func @LoadShader(i64, i64, i64) -> !llvm.struct<(i64, i64)> attributes {sym_visibility = "private"}
  llvm.func @UnloadShader(i64, i64) attributes {sym_visibility = "private"}
  llvm.func @GetShaderLocation(i64, i64, i64) -> i64 attributes {sym_visibility = "private"}
  llvm.func @SetShaderValue(i64, i64, i64, !llvm.ptr, i32) attributes {sym_visibility = "private"}
  llvm.func @SetShaderValueMatrix(i64, i64, i64, !llvm.ptr {llvm.align = 4 : i64, llvm.byval = !llvm.struct<(f32, f32, f32, f32, f32, f32, f32, f32, f32, f32, f32, f32, f32, f32, f32, f32)>}) attributes {sym_visibility = "private"}
  llvm.func @SetShaderValueTexture(i64, i64, i64, !llvm.ptr {llvm.align = 8 : i64, llvm.byval = !llvm.struct<(i32, i64, i64, i64, i64)>}) attributes {sym_visibility = "private"}
  llvm.func @BeginShaderMode(i64, i64) attributes {sym_visibility = "private"}
  llvm.func @EndShaderMode() attributes {sym_visibility = "private"}
  llvm.func @FileExists(!llvm.ptr) -> i1 attributes {sym_visibility = "private"}
  llvm.func @DirectoryExists(!llvm.ptr) -> i1 attributes {sym_visibility = "private"}
  llvm.func @IsFileExtension(!llvm.ptr, !llvm.ptr) -> i1 attributes {sym_visibility = "private"}
  llvm.func @GetFileExtension(!llvm.ptr) -> !llvm.ptr attributes {sym_visibility = "private"}
  llvm.func @GetFileName(!llvm.ptr) -> !llvm.ptr attributes {sym_visibility = "private"}
  llvm.func @GetFileNameWithoutExt(!llvm.ptr) -> !llvm.ptr attributes {sym_visibility = "private"}
  llvm.func @GetDirectoryPath(!llvm.ptr) -> !llvm.ptr attributes {sym_visibility = "private"}
  llvm.func @GetPrevDirectoryPath(!llvm.ptr) -> !llvm.ptr attributes {sym_visibility = "private"}
  llvm.func @GetWorkingDirectory() -> !llvm.ptr attributes {sym_visibility = "private"}
  llvm.func @GetApplicationDirectory() -> !llvm.ptr attributes {sym_visibility = "private"}
  llvm.func @ChangeDirectory(!llvm.ptr) -> i1 attributes {sym_visibility = "private"}
  llvm.func @IsPathFile(!llvm.ptr) -> i1 attributes {sym_visibility = "private"}
  llvm.func @LoadFileData(!llvm.ptr, !llvm.ptr) -> !llvm.ptr attributes {sym_visibility = "private"}
  llvm.func @UnloadFileData(!llvm.ptr) attributes {sym_visibility = "private"}
  llvm.func @SaveFileData(!llvm.ptr, !llvm.ptr, i64) -> i1 attributes {sym_visibility = "private"}
  llvm.func @ExportDataAsCode(!llvm.ptr, i64, !llvm.ptr) -> i1 attributes {sym_visibility = "private"}
  llvm.func @LoadFileText(!llvm.ptr) -> !llvm.ptr attributes {sym_visibility = "private"}
  llvm.func @UnloadFileText(!llvm.ptr) attributes {sym_visibility = "private"}
  llvm.func @SaveFileText(!llvm.ptr, !llvm.ptr) -> i1 attributes {sym_visibility = "private"}
  llvm.func @LoadDroppedFiles() -> !llvm.struct<(i64, i64)> attributes {sym_visibility = "private"}
  llvm.func @UnloadDroppedFiles(i64, i64) attributes {sym_visibility = "private"}
  llvm.func @GetFileModTime(!llvm.ptr) -> i64 attributes {sym_visibility = "private"}
  llvm.func @MemAlloc(i32) -> !llvm.ptr attributes {sym_visibility = "private"}
  llvm.func @MemRealloc(!llvm.ptr, i32) -> !llvm.ptr attributes {sym_visibility = "private"}
  llvm.func @MemFree(!llvm.ptr) attributes {sym_visibility = "private"}
  llvm.func @CompressData(!llvm.ptr, i64, !llvm.ptr) -> !llvm.ptr attributes {sym_visibility = "private"}
  llvm.func @DecompressData(!llvm.ptr, i64, !llvm.ptr) -> !llvm.ptr attributes {sym_visibility = "private"}
  llvm.func @EncodeDataBase64(!llvm.ptr, i64, !llvm.ptr) -> !llvm.ptr attributes {sym_visibility = "private"}
  llvm.func @DecodeDataBase64(!llvm.ptr, !llvm.ptr) -> !llvm.ptr attributes {sym_visibility = "private"}
  llvm.func @ComputeCRC32(!llvm.ptr, i64) -> i32 attributes {sym_visibility = "private"}
  llvm.func @ComputeMD5(!llvm.ptr, i64) -> !llvm.ptr attributes {sym_visibility = "private"}
  llvm.func @ComputeSHA1(!llvm.ptr, i64) -> !llvm.ptr attributes {sym_visibility = "private"}
  llvm.func @LoadUTF8(!llvm.ptr, i64) -> !llvm.ptr attributes {sym_visibility = "private"}
  llvm.func @UnloadUTF8(!llvm.ptr) attributes {sym_visibility = "private"}
  llvm.func @LoadCodepoints(!llvm.ptr, !llvm.ptr) -> !llvm.ptr attributes {sym_visibility = "private"}
  llvm.func @UnloadCodepoints(!llvm.ptr) attributes {sym_visibility = "private"}
  llvm.func @GetCodepointCount(!llvm.ptr) -> i64 attributes {sym_visibility = "private"}
  llvm.func @GetCodepoint(!llvm.ptr, !llvm.ptr) -> i64 attributes {sym_visibility = "private"}
  llvm.func @GetCodepointNext(!llvm.ptr, !llvm.ptr) -> i64 attributes {sym_visibility = "private"}
  llvm.func @GetCodepointPrevious(!llvm.ptr, !llvm.ptr) -> i64 attributes {sym_visibility = "private"}
  llvm.func @CodepointToUTF8(i64, !llvm.ptr) -> !llvm.ptr attributes {sym_visibility = "private"}
  llvm.func @TextCopy(!llvm.ptr, !llvm.ptr) -> i64 attributes {sym_visibility = "private"}
  llvm.func @TextIsEqual(!llvm.ptr, !llvm.ptr) -> i1 attributes {sym_visibility = "private"}
  llvm.func @TextLength(i64) -> i32 attributes {sym_visibility = "private"}
  llvm.func @TextFormat(i64, ...) -> !llvm.ptr attributes {sym_visibility = "private"}
  llvm.func @TextSubtext(i64, i64, i64) -> !llvm.ptr attributes {sym_visibility = "private"}
  llvm.func @TextReplace(!llvm.ptr, !llvm.ptr, !llvm.ptr) -> !llvm.ptr attributes {sym_visibility = "private"}
  llvm.func @TextInsert(!llvm.ptr, !llvm.ptr, i64) -> !llvm.ptr attributes {sym_visibility = "private"}
  llvm.func @TextJoin(!llvm.ptr, i64, !llvm.ptr) -> !llvm.ptr attributes {sym_visibility = "private"}
  llvm.func @TextSplit(!llvm.ptr, i8, !llvm.ptr) -> !llvm.ptr attributes {sym_visibility = "private"}
  llvm.func @TextAppend(!llvm.ptr, !llvm.ptr, !llvm.ptr) attributes {sym_visibility = "private"}
  llvm.func @TextFindIndex(!llvm.ptr, !llvm.ptr) -> i64 attributes {sym_visibility = "private"}
  llvm.func @TextToUpper(!llvm.ptr) -> !llvm.ptr attributes {sym_visibility = "private"}
  llvm.func @TextToLower(!llvm.ptr) -> !llvm.ptr attributes {sym_visibility = "private"}
  llvm.func @TextToPascal(!llvm.ptr) -> !llvm.ptr attributes {sym_visibility = "private"}
  llvm.func @GetRandomValue(i64, i64) -> i64 attributes {sym_visibility = "private"}
  llvm.mlir.global internal @KEY_NULL(0 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_APOSTROPHE(39 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_COMMA(44 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_MINUS(45 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_PERIOD(46 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_SLASH(47 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_ZERO(48 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_ONE(49 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_TWO(50 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_THREE(51 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_FOUR(52 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_FIVE(53 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_SIX(54 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_SEVEN(55 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_EIGHT(56 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_NINE(57 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_SEMICOLON(59 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_EQUAL(61 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_A(65 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_B(66 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_C(67 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_D(68 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_E(69 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_F(70 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_G(71 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_H(72 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_I(73 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_J(74 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_K(75 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_L(76 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_M(77 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_N(78 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_O(79 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_P(80 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_Q(81 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_R(82 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_S(83 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_T(84 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_U(85 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_V(86 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_W(87 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_X(88 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_Y(89 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_Z(90 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_LEFT_BRACKET(91 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_BACKSLASH(92 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_RIGHT_BRACKET(93 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_GRAVE(96 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_SPACE(32 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_ESCAPE(256 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_ENTER(257 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_TAB(258 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_BACKSPACE(259 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_INSERT(260 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_DELETE(261 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_RIGHT(262 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_LEFT(263 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_DOWN(264 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_UP(265 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_PAGE_UP(266 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_PAGE_DOWN(267 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_HOME(268 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_END(269 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_CAPS_LOCK(280 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_SCROLL_LOCK(281 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_NUM_LOCK(282 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_PRINT_SCREEN(283 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_PAUSE(284 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_F1(290 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_F2(291 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_F3(292 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_F4(293 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_F5(294 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_F6(295 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_F7(296 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_F8(297 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_F9(298 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_F10(299 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_F11(300 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_F12(301 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_LEFT_SHIFT(340 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_LEFT_CONTROL(341 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_LEFT_ALT(342 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_LEFT_SUPER(343 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_RIGHT_SHIFT(344 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_RIGHT_CONTROL(345 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_RIGHT_ALT(346 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_RIGHT_SUPER(347 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_KB_MENU(348 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_KP_0(320 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_KP_1(321 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_KP_2(322 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_KP_3(323 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_KP_4(324 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_KP_5(325 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_KP_6(326 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_KP_7(327 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_KP_8(328 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_KP_9(329 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_KP_DECIMAL(330 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_KP_DIVIDE(331 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_KP_MULTIPLY(332 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_KP_SUBTRACT(333 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_KP_ADD(334 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_KP_ENTER(335 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_KP_EQUAL(336 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_BACK(4 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_MENU(5 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_VOLUME_UP(24 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @KEY_VOLUME_DOWN(25 : i64) {addr_space = 0 : i32, sym_visibility = "private"} : i64
  llvm.mlir.global internal @rl() {addr_space = 0 : i32, sym_visibility = "private"} : !llvm.ptr
  func.func public @main() -> i32 attributes {llvm.di.subprogram = #di_subprogram} {
    %0 = llvm.mlir.constant(800 : i64) : i64
    %1 = llvm.mlir.constant(450 : i64) : i64
    %2 = llvm.mlir.zero : !llvm.struct<(i1, ptr)>
    %3 = llvm.mlir.constant(false) : i1
    %4 = llvm.insertvalue %3, %2[0] : !llvm.struct<(i1, ptr)> 
    %5 = llvm.mlir.addressof @__str_46b213ced705f245 : !llvm.ptr
    %6 = llvm.getelementptr %5[0, 0] : (!llvm.ptr) -> !llvm.ptr, !llvm.array<10 x i8>
    %7 = llvm.mlir.constant(9 : i64) : i64
    %8 = llvm.mlir.undef : !llvm.struct<(ptr, i64)>
    %9 = llvm.insertvalue %6, %8[0] : !llvm.struct<(ptr, i64)> 
    %10 = llvm.insertvalue %7, %9[1] : !llvm.struct<(ptr, i64)> 
    %11 = llvm.mlir.constant(1 : i64) : i64
    %12 = llvm.alloca %11 x !llvm.struct<(i1, ptr)> {alignment = 1 : i64} : (i64) -> !llvm.ptr
    llvm.store %4, %12 : !llvm.struct<(i1, ptr)>, !llvm.ptr
    %13 = llvm.load %12 : !llvm.ptr -> i64
    %14 = llvm.mlir.constant(8 : i64) : i64
    %15 = llvm.getelementptr %12[%14] : (!llvm.ptr, i64) -> !llvm.ptr, i8
    %16 = llvm.load %15 : !llvm.ptr -> i64
    %17 = llvm.mlir.constant(1 : i64) : i64
    %18 = llvm.alloca %17 x !llvm.struct<(ptr, i64)> {alignment = 1 : i64} : (i64) -> !llvm.ptr
    llvm.store %10, %18 : !llvm.struct<(ptr, i64)>, !llvm.ptr
    %19 = llvm.load %18 : !llvm.ptr -> i64
    %20 = llvm.call @LoadShader(%13, %16, %19) : (i64, i64, i64) -> !llvm.struct<(i64, i64)>
    %21 = llvm.extractvalue %20[0] : !llvm.struct<(i64, i64)> 
    %22 = llvm.extractvalue %20[1] : !llvm.struct<(i64, i64)> 
    %23 = llvm.mlir.undef : !llvm.struct<(i32, ptr)>
    %24 = llvm.mlir.constant(1 : i64) : i64
    %25 = llvm.alloca %24 x !llvm.struct<(i32, ptr)> {alignment = 1 : i64} : (i64) -> !llvm.ptr
    llvm.store %23, %25 : !llvm.struct<(i32, ptr)>, !llvm.ptr
    llvm.store %21, %25 : i64, !llvm.ptr
    %26 = llvm.mlir.constant(8 : i64) : i64
    %27 = llvm.getelementptr %25[%26] : (!llvm.ptr, i64) -> !llvm.ptr, i8
    llvm.store %22, %27 : i64, !llvm.ptr
    %28 = llvm.load %25 : !llvm.ptr -> !llvm.struct<(i32, ptr)>
    %29 = llvm.mlir.addressof @__str_232c1e13c13df5af : !llvm.ptr
    %30 = llvm.getelementptr %29[0, 0] : (!llvm.ptr) -> !llvm.ptr, !llvm.array<11 x i8>
    %31 = llvm.mlir.constant(10 : i64) : i64
    %32 = llvm.mlir.undef : !llvm.struct<(ptr, i64)>
    %33 = llvm.insertvalue %30, %32[0] : !llvm.struct<(ptr, i64)> 
    %34 = llvm.insertvalue %31, %33[1] : !llvm.struct<(ptr, i64)> 
    %35 = llvm.mlir.constant(1 : i64) : i64
    %36 = llvm.alloca %35 x !llvm.struct<(i32, ptr)> {alignment = 1 : i64} : (i64) -> !llvm.ptr
    llvm.store %28, %36 : !llvm.struct<(i32, ptr)>, !llvm.ptr
    %37 = llvm.load %36 : !llvm.ptr -> i64
    %38 = llvm.mlir.constant(8 : i64) : i64
    %39 = llvm.getelementptr %36[%38] : (!llvm.ptr, i64) -> !llvm.ptr, i8
    %40 = llvm.load %39 : !llvm.ptr -> i64
    %41 = llvm.mlir.constant(1 : i64) : i64
    %42 = llvm.alloca %41 x !llvm.struct<(ptr, i64)> {alignment = 1 : i64} : (i64) -> !llvm.ptr
    llvm.store %34, %42 : !llvm.struct<(ptr, i64)>, !llvm.ptr
    %43 = llvm.load %42 : !llvm.ptr -> i64
    %44 = llvm.call @GetShaderLocation(%37, %40, %43) : (i64, i64, i64) -> i64
    %45 = llvm.sitofp %0 : i64 to f32
    %46 = llvm.sitofp %1 : i64 to f32
    %47 = llvm.mlir.zero : !llvm.struct<(f32, f32)>
    %48 = llvm.insertvalue %45, %47[0] : !llvm.struct<(f32, f32)> 
    %49 = llvm.insertvalue %46, %48[1] : !llvm.struct<(f32, f32)> 
    %50 = llvm.mlir.constant(60 : i64) : i64
    llvm.call @SetTargetFPS(%50) : (i64) -> ()
    cf.br ^bb1
  ^bb1:  // 2 preds: ^bb0, ^bb2
    %51 = llvm.call @WindowShouldClose() : () -> i1
    %52 = llvm.mlir.constant(true) : i1
    %53 = arith.xori %51, %52 : i1
    cf.cond_br %53, ^bb2, ^bb3
  ^bb2:  // pred: ^bb1
    %54 = llvm.mlir.constant(1 : i64) : i64
    %55 = llvm.alloca %54 x !llvm.struct<(f32, f32)> : (i64) -> !llvm.ptr
    llvm.store %49, %55 : !llvm.struct<(f32, f32)>, !llvm.ptr
    %56 = llvm.getelementptr %55[0] : (!llvm.ptr) -> !llvm.ptr, f32
    %57 = llvm.call @GetScreenWidth() : () -> i64
    %58 = llvm.sitofp %57 : i64 to f32
    llvm.store %58, %56 : f32, !llvm.ptr
    %59 = llvm.getelementptr %55[1] : (!llvm.ptr) -> !llvm.ptr, f32
    %60 = llvm.call @GetScreenHeight() : () -> i64
    %61 = llvm.sitofp %60 : i64 to f32
    llvm.store %61, %59 : f32, !llvm.ptr
    %62 = llvm.mlir.constant(1 : i32) : i32
    %63 = llvm.mlir.constant(1 : i64) : i64
    %64 = llvm.alloca %63 x !llvm.struct<(i32, ptr)> {alignment = 1 : i64} : (i64) -> !llvm.ptr
    llvm.store %28, %64 : !llvm.struct<(i32, ptr)>, !llvm.ptr
    %65 = llvm.load %64 : !llvm.ptr -> i64
    %66 = llvm.mlir.constant(8 : i64) : i64
    %67 = llvm.getelementptr %64[%66] : (!llvm.ptr, i64) -> !llvm.ptr, i8
    %68 = llvm.load %67 : !llvm.ptr -> i64
    %69 = llvm.mlir.constant(1 : i64) : i64
    %70 = llvm.alloca %69 x !llvm.ptr {alignment = 1 : i64} : (i64) -> !llvm.ptr
    llvm.store %55, %70 : !llvm.ptr, !llvm.ptr
    %71 = llvm.load %70 : !llvm.ptr -> !llvm.ptr
    llvm.call @SetShaderValue(%65, %68, %44, %71, %62) : (i64, i64, i64, !llvm.ptr, i32) -> ()
    llvm.call @BeginDrawing() : () -> ()
    %72 = llvm.mlir.constant(0 : i8) : i8
    %73 = llvm.mlir.constant(0 : i8) : i8
    %74 = llvm.mlir.constant(0 : i8) : i8
    %75 = llvm.mlir.constant(-1 : i8) : i8
    %76 = llvm.mlir.zero : !llvm.struct<(i8, i8, i8, i8)>
    %77 = llvm.insertvalue %72, %76[0] : !llvm.struct<(i8, i8, i8, i8)> 
    %78 = llvm.insertvalue %73, %77[1] : !llvm.struct<(i8, i8, i8, i8)> 
    %79 = llvm.insertvalue %74, %78[2] : !llvm.struct<(i8, i8, i8, i8)> 
    %80 = llvm.insertvalue %75, %79[3] : !llvm.struct<(i8, i8, i8, i8)> 
    %81 = llvm.mlir.constant(1 : i64) : i64
    %82 = llvm.alloca %81 x !llvm.struct<(i8, i8, i8, i8)> {alignment = 1 : i64} : (i64) -> !llvm.ptr
    llvm.store %80, %82 : !llvm.struct<(i8, i8, i8, i8)>, !llvm.ptr
    %83 = llvm.load %82 : !llvm.ptr -> i32
    llvm.call @ClearBackground(%83) : (i32) -> ()
    %84 = llvm.mlir.constant(1 : i64) : i64
    %85 = llvm.alloca %84 x !llvm.struct<(i32, ptr)> {alignment = 1 : i64} : (i64) -> !llvm.ptr
    llvm.store %28, %85 : !llvm.struct<(i32, ptr)>, !llvm.ptr
    %86 = llvm.load %85 : !llvm.ptr -> i64
    %87 = llvm.mlir.constant(8 : i64) : i64
    %88 = llvm.getelementptr %85[%87] : (!llvm.ptr, i64) -> !llvm.ptr, i8
    %89 = llvm.load %88 : !llvm.ptr -> i64
    llvm.call @BeginShaderMode(%86, %89) : (i64, i64) -> ()
    %90 = llvm.mlir.constant(0 : i64) : i64
    %91 = llvm.mlir.constant(0 : i64) : i64
    %92 = llvm.mlir.constant(-1 : i8) : i8
    %93 = llvm.mlir.constant(-1 : i8) : i8
    %94 = llvm.mlir.constant(-1 : i8) : i8
    %95 = llvm.mlir.constant(-1 : i8) : i8
    %96 = llvm.mlir.zero : !llvm.struct<(i8, i8, i8, i8)>
    %97 = llvm.insertvalue %92, %96[0] : !llvm.struct<(i8, i8, i8, i8)> 
    %98 = llvm.insertvalue %93, %97[1] : !llvm.struct<(i8, i8, i8, i8)> 
    %99 = llvm.insertvalue %94, %98[2] : !llvm.struct<(i8, i8, i8, i8)> 
    %100 = llvm.insertvalue %95, %99[3] : !llvm.struct<(i8, i8, i8, i8)> 
    %101 = llvm.mlir.constant(1 : i64) : i64
    %102 = llvm.alloca %101 x !llvm.struct<(i8, i8, i8, i8)> {alignment = 1 : i64} : (i64) -> !llvm.ptr
    llvm.store %100, %102 : !llvm.struct<(i8, i8, i8, i8)>, !llvm.ptr
    %103 = llvm.load %102 : !llvm.ptr -> i32
    llvm.call @DrawRectangle(%90, %91, %0, %1, %103) : (i64, i64, i64, i64, i32) -> ()
    llvm.call @EndShaderMode() : () -> ()
    %104 = llvm.mlir.addressof @__str_c0e83eef36af93dc : !llvm.ptr
    %105 = llvm.getelementptr %104[0, 0] : (!llvm.ptr) -> !llvm.ptr, !llvm.array<30 x i8>
    %106 = llvm.mlir.constant(29 : i64) : i64
    %107 = llvm.mlir.undef : !llvm.struct<(ptr, i64)>
    %108 = llvm.insertvalue %105, %107[0] : !llvm.struct<(ptr, i64)> 
    %109 = llvm.insertvalue %106, %108[1] : !llvm.struct<(ptr, i64)> 
    %110 = llvm.mlir.constant(10 : i64) : i64
    %111 = llvm.mlir.constant(10 : i64) : i64
    %112 = llvm.mlir.constant(20 : i64) : i64
    %113 = llvm.mlir.constant(-11 : i8) : i8
    %114 = llvm.mlir.constant(-11 : i8) : i8
    %115 = llvm.mlir.constant(-11 : i8) : i8
    %116 = llvm.mlir.constant(-1 : i8) : i8
    %117 = llvm.mlir.zero : !llvm.struct<(i8, i8, i8, i8)>
    %118 = llvm.insertvalue %113, %117[0] : !llvm.struct<(i8, i8, i8, i8)> 
    %119 = llvm.insertvalue %114, %118[1] : !llvm.struct<(i8, i8, i8, i8)> 
    %120 = llvm.insertvalue %115, %119[2] : !llvm.struct<(i8, i8, i8, i8)> 
    %121 = llvm.insertvalue %116, %120[3] : !llvm.struct<(i8, i8, i8, i8)> 
    %122 = llvm.mlir.constant(1 : i64) : i64
    %123 = llvm.alloca %122 x !llvm.struct<(ptr, i64)> {alignment = 1 : i64} : (i64) -> !llvm.ptr
    llvm.store %109, %123 : !llvm.struct<(ptr, i64)>, !llvm.ptr
    %124 = llvm.load %123 : !llvm.ptr -> i64
    %125 = llvm.mlir.constant(1 : i64) : i64
    %126 = llvm.alloca %125 x !llvm.struct<(i8, i8, i8, i8)> {alignment = 1 : i64} : (i64) -> !llvm.ptr
    llvm.store %121, %126 : !llvm.struct<(i8, i8, i8, i8)>, !llvm.ptr
    %127 = llvm.load %126 : !llvm.ptr -> i32
    llvm.call @DrawText(%124, %110, %111, %112, %127) : (i64, i64, i64, i64, i32) -> ()
    llvm.call @EndDrawing() : () -> ()
    cf.br ^bb1
  ^bb3:  // pred: ^bb1
    %128 = llvm.mlir.undef : !llvm.ptr
    %129 = llvm.mlir.constant(0 : i64) : i64
    %130 = llvm.trunc %129 : i64 to i32
    cf.br ^bb4(%130 : i32)
  ^bb4(%131: i32):  // pred: ^bb3
    return %131 : i32
  }
  llvm.mlir.global internal constant @__str_46b213ced705f245("frag.glsl\00") {addr_space = 0 : i32}
  llvm.mlir.global internal constant @__str_232c1e13c13df5af("resolution\00") {addr_space = 0 : i32}
  llvm.mlir.global internal constant @__str_c0e83eef36af93dc("SDF Circle with raylib shader\00") {addr_space = 0 : i32}
}
