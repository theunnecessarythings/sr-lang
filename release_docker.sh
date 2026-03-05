#!/usr/bin/env bash
set -euo pipefail

LLVM_COMMIT_DEFAULT="a992f29451b9e140424f35ac5e20177db4afbdc0"
LLVM_COMMIT="${1:-$LLVM_COMMIT_DEFAULT}"

IMAGE_TAG="${2:-sr-lang-release:ubuntu22.04}"
BUILD_TARGET="${3:-native}" # native or wasm (emscripten) or wasm-wasi

ZIG_VERSION="${ZIG_VERSION:-0.15.2}"
ZIG_URL="${ZIG_URL:-https://ziglang.org/download/$ZIG_VERSION/zig-x86_64-linux-$ZIG_VERSION.tar.xz}"

LLVM_DIR="/work/_llvm/llvm-project"
if [ "$BUILD_TARGET" == "wasm" ]; then
  BUILD_DIR="/work/_llvm/build-wasm-emscripten-${LLVM_COMMIT}"
elif [ "$BUILD_TARGET" == "wasm-wasi" ]; then
  BUILD_DIR="/work/_llvm/build-wasm-wasi-${LLVM_COMMIT}"
else
  BUILD_DIR="/work/_llvm/build-${LLVM_COMMIT}"
fi
MARKER="${BUILD_DIR}/.installed"

TTY_FLAGS="-i"
if [ -t 0 ] && [ -t 1 ]; then
  TTY_FLAGS="-it"
fi

exec docker run --rm $TTY_FLAGS \
  -v "${PWD}":/work -w /work \
  -e LLVM_COMMIT="${LLVM_COMMIT}" \
  -e LLVM_DIR="${LLVM_DIR}" \
  -e BUILD_DIR="${BUILD_DIR}" \
  -e MARKER="${MARKER}" \
  -e ZIG_VERSION="${ZIG_VERSION}" \
  -e ZIG_URL="${ZIG_URL}" \
  -e BUILD_TARGET="${BUILD_TARGET}" \
  "${IMAGE_TAG}" bash -lc '
    set -euxo pipefail

    ZIG_URL="${ZIG_URL:-https://ziglang.org/download/$ZIG_VERSION/zig-x86_64-linux-$ZIG_VERSION.tar.xz}"
    ZIG_DIR="/work/_zig/zig-$ZIG_VERSION"
    if [ ! -x "$ZIG_DIR/zig" ]; then
      mkdir -p /work/_zig
      echo "Downloading Zig from $ZIG_URL"
      curl -fL -o /tmp/zig.tar.xz "$ZIG_URL"
      tar -C /work/_zig -xf /tmp/zig.tar.xz
      set +o pipefail
      EXTRACTED_DIR="$(tar -tf /tmp/zig.tar.xz | head -1 | cut -d/ -f1)"
      set -o pipefail
      if [ -z "$EXTRACTED_DIR" ]; then
        echo "Failed to determine Zig extract dir" >&2
        exit 1
      fi
      rm -rf "$ZIG_DIR"
      mv "/work/_zig/$EXTRACTED_DIR" "$ZIG_DIR"
      ls -la "$ZIG_DIR"
    else
      echo "Using cached Zig at $ZIG_DIR"
    fi

    if [ ! -d "$LLVM_DIR" ]; then
      git clone https://github.com/llvm/llvm-project "$LLVM_DIR"
    fi
    cd "$LLVM_DIR"
    git fetch --all --tags
    git reset --hard "$LLVM_COMMIT"

    if [ ! -f "$MARKER" ]; then
      if [ "$BUILD_TARGET" == "wasm" ]; then
        # Install Emscripten
        EMSDK_DIR="/work/_emsdk"
        if [ ! -d "$EMSDK_DIR" ]; then
            git clone https://github.com/emscripten-core/emsdk.git "$EMSDK_DIR"
            cd "$EMSDK_DIR"
            ./emsdk install latest
            ./emsdk activate latest
        fi
        cd "$EMSDK_DIR"
        source ./emsdk_env.sh
        EMSDK_SYSROOT="${EMSDK_DIR}/upstream/emscripten/cache/sysroot"

        # We still need native tblgen tools
        NATIVE_BUILD_DIR="/work/_llvm/build-${LLVM_COMMIT}"
        if [ ! -f "$NATIVE_BUILD_DIR/.installed" ]; then
          echo "Building Native LLVM first for tools..."
          mkdir -p "$NATIVE_BUILD_DIR"
          cd "$NATIVE_BUILD_DIR"
          cmake -G Ninja "$LLVM_DIR/llvm" \
            -DLLVM_ENABLE_PROJECTS="mlir;llvm" \
            -DLLVM_TARGETS_TO_BUILD="Native;NVPTX;AMDGPU" \
            -DCMAKE_BUILD_TYPE=Release \
            -DLLVM_ENABLE_ASSERTIONS=ON \
            -DCMAKE_C_COMPILER=clang \
            -DCMAKE_CXX_COMPILER=clang++ \
            -DLLVM_ENABLE_LLD=ON \
            -DCMAKE_INSTALL_PREFIX=/usr/local
          ninja install
          touch "$NATIVE_BUILD_DIR/.installed"
        fi

        echo "Building WASM LLVM with Emscripten..."
        mkdir -p "$BUILD_DIR"
        cd "$BUILD_DIR"
        
        # Emscripten CMake configuration
        emcmake cmake -G Ninja "$LLVM_DIR/llvm" \
            -DLLVM_ENABLE_PROJECTS="mlir;llvm" \
            -DLLVM_TARGETS_TO_BUILD="WebAssembly" \
            -DCMAKE_BUILD_TYPE=Release \
            -DLLVM_ENABLE_ASSERTIONS=OFF \
            -DLLVM_HOST_TRIPLE=wasm32-unknown-emscripten \
            -DLLVM_ENABLE_THREADS=OFF \
            -DLLVM_ENABLE_ZLIB=OFF \
            -DLLVM_ENABLE_ZSTD=OFF \
            -DLLVM_ENABLE_TERMINFO=OFF \
            -DLLVM_INCLUDE_BENCHMARKS=OFF \
            -DLLVM_INCLUDE_TESTS=OFF \
            -DLLVM_INCLUDE_EXAMPLES=OFF \
            -DLLVM_TABLEGEN="$NATIVE_BUILD_DIR/bin/llvm-tblgen" \
            -DMLIR_TABLEGEN="$NATIVE_BUILD_DIR/bin/mlir-tblgen" \
            -DLLVM_NATIVE_TOOL_DIR="$NATIVE_BUILD_DIR/bin" \
            -DCMAKE_INSTALL_PREFIX="$BUILD_DIR/install"
        
        ninja -j8
        ninja install
      elif [ "$BUILD_TARGET" == "wasm-wasi" ]; then
        # We still need native tblgen tools
        NATIVE_BUILD_DIR="/work/_llvm/build-${LLVM_COMMIT}"
        if [ ! -f "$NATIVE_BUILD_DIR/.installed" ]; then
          echo "Building Native LLVM first for tools..."
          mkdir -p "$NATIVE_BUILD_DIR"
          cd "$NATIVE_BUILD_DIR"
          cmake -G Ninja "$LLVM_DIR/llvm" \
            -DLLVM_ENABLE_PROJECTS="mlir;llvm" \
            -DLLVM_TARGETS_TO_BUILD="Native;NVPTX;AMDGPU" \
            -DCMAKE_BUILD_TYPE=Release \
            -DLLVM_ENABLE_ASSERTIONS=ON \
            -DCMAKE_C_COMPILER=clang \
            -DCMAKE_CXX_COMPILER=clang++ \
            -DLLVM_ENABLE_LLD=ON \
            -DCMAKE_INSTALL_PREFIX=/usr/local
          ninja install
          touch "$NATIVE_BUILD_DIR/.installed"
        fi

        echo "Building WASI LLVM with Zig..."
        cat > /work/_tmp_zig_cc.sh << "EOF"
#!/usr/bin/env bash
exec /work/_zig/zig-${ZIG_VERSION}/zig cc "$@"
EOF
        cat > /work/_tmp_zig_cxx.sh << "EOF"
#!/usr/bin/env bash
exec /work/_zig/zig-${ZIG_VERSION}/zig c++ "$@"
EOF
        chmod +x /work/_tmp_zig_cc.sh /work/_tmp_zig_cxx.sh
        mkdir -p "$BUILD_DIR"
        cd "$BUILD_DIR"
        cmake -G Ninja "$LLVM_DIR/llvm" \
            -DLLVM_ENABLE_PROJECTS="mlir;llvm" \
            -DLLVM_TARGETS_TO_BUILD="WebAssembly" \
            -DCMAKE_BUILD_TYPE=Release \
            -DCMAKE_BUILD_WITH_INSTALL_RPATH=ON \
            -DLLVM_ENABLE_ASSERTIONS=OFF \
            -DLLVM_ENABLE_THREADS=OFF \
            -DLLVM_ENABLE_ZLIB=OFF \
            -DLLVM_ENABLE_ZSTD=OFF \
            -DLLVM_ENABLE_TERMINFO=OFF \
            -DLLVM_INCLUDE_BENCHMARKS=OFF \
            -DLLVM_INCLUDE_TESTS=OFF \
            -DLLVM_INCLUDE_EXAMPLES=OFF \
            -DLLVM_INCLUDE_TOOLS=OFF \
            -DLLVM_BUILD_TOOLS=OFF \
            -DLLVM_BUILD_UTILS=OFF \
            -DLLVM_BUILD_LLVM_DYLIB=OFF \
            -DLLVM_LINK_LLVM_DYLIB=OFF \
            -DLLVM_ENABLE_LTO=OFF \
            -DMLIR_INCLUDE_TOOLS=OFF \
            -DMLIR_ENABLE_BINDINGS_PYTHON=OFF \
            -DMLIR_ENABLE_BINDINGS_PYTHON_API=OFF \
            -DHAVE_ENDIAN_H=0 \
            -DHAVE_SYS_ENDIAN_H=0 \
            -DHAVE_MACHINE_ENDIAN_H=0 \
            -DLLVM_TABLEGEN="$NATIVE_BUILD_DIR/bin/llvm-tblgen" \
            -DMLIR_TABLEGEN="$NATIVE_BUILD_DIR/bin/mlir-tblgen" \
            -DLLVM_NATIVE_TOOL_DIR="$NATIVE_BUILD_DIR/bin" \
            -DCMAKE_INSTALL_PREFIX="$BUILD_DIR/install" \
            -DCMAKE_C_COMPILER=/work/_tmp_zig_cc.sh \
            -DCMAKE_C_COMPILER_TARGET=wasm32-wasi \
            -DCMAKE_CXX_COMPILER=/work/_tmp_zig_cxx.sh \
            -DCMAKE_CXX_COMPILER_TARGET=wasm32-wasi
        ninja -j8
        ninja install
      else
        mkdir -p "$BUILD_DIR"
        cd "$BUILD_DIR"
        cmake -G Ninja "$LLVM_DIR/llvm" \
          -DLLVM_ENABLE_PROJECTS="mlir;llvm" \
          -DLLVM_TARGETS_TO_BUILD="Native;NVPTX;AMDGPU" \
          -DCMAKE_BUILD_TYPE=Release \
          -DLLVM_ENABLE_ASSERTIONS=ON \
          -DCMAKE_C_COMPILER=clang \
          -DCMAKE_CXX_COMPILER=clang++ \
          -DLLVM_ENABLE_LLD=ON \
          -DCMAKE_INSTALL_PREFIX=/usr/local
        ninja install
      fi
      touch "$MARKER"
    else
      echo "LLVM/MLIR already built for $LLVM_COMMIT ($BUILD_TARGET)"
    fi

    cd /work
    if command -v clang-18 >/dev/null 2>&1; then
      export CC=clang-18
      export CXX=clang++-18
      ln -sf "$(command -v clang-18)" /usr/local/bin/clang
      ln -sf "$(command -v clang++-18)" /usr/local/bin/clang++
    fi
    rm -rf zig-out
    if [ ! -e /usr/lib/libstdc++.so.6 ] && [ -e /usr/lib/x86_64-linux-gnu/libstdc++.so.6 ]; then
      ln -s /usr/lib/x86_64-linux-gnu/libstdc++.so.6 /usr/lib/libstdc++.so.6
    fi
    
    # Setup includes for Zig build
    if [ ! -f /usr/local/include/mlir-c/IR.h ]; then
      if [ "$BUILD_TARGET" == "wasm" ] || [ "$BUILD_TARGET" == "wasm-wasi" ]; then
         INCLUDE_BASE="$BUILD_DIR/install"
      else
         INCLUDE_BASE="$BUILD_DIR"
      fi
      INCLUDE_FALLBACKS=("$INCLUDE_BASE/include" "$INCLUDE_BASE/tools/mlir/include" "$LLVM_DIR/mlir/include" "$LLVM_DIR/llvm/include" "/usr/local/include")
      INCLUDE_PATHS=""
      for p in "${INCLUDE_FALLBACKS[@]}"; do
        if [ -d "$p" ]; then
          INCLUDE_PATHS="${INCLUDE_PATHS:+$INCLUDE_PATHS:}$p"
        fi
      done
      if [ -n "$INCLUDE_PATHS" ]; then
        export C_INCLUDE_PATH="$INCLUDE_PATHS${C_INCLUDE_PATH:+:$C_INCLUDE_PATH}"
        export CPATH="$INCLUDE_PATHS${CPATH:+:$CPATH}"
      fi
    fi

    rm -rf sr-lang-0.1.0 zig-out
    if [ "$BUILD_TARGET" == "wasm" ]; then
        LLVM_LIB_DIR="$BUILD_DIR/install/lib"
        EMSDK_DIR="/work/_emsdk"
        if [ -f "$EMSDK_DIR/emsdk_env.sh" ]; then
          source "$EMSDK_DIR/emsdk_env.sh"
        fi
        EMSDK_SYSROOT="${EMSDK_DIR}/upstream/emscripten/cache/sysroot"
        EMSDK_LLVM_DIR="${EMSDK_SYSROOT}/llvm"
        mkdir -p "$EMSDK_LLVM_DIR"
        ln -sfn "$LLVM_LIB_DIR" "$EMSDK_LLVM_DIR/lib"
        LIBC_CONF="/work/_tmp_emscripten.libc.conf"
        cat > "$LIBC_CONF" << EOF
include_dir=${EMSDK_SYSROOT}/include
sys_include_dir=${EMSDK_SYSROOT}/include
crt_dir=${EMSDK_SYSROOT}/lib/wasm32-emscripten
msvc_lib_dir=
kernel32_lib_dir=
gcc_dir=
EOF
        export C_INCLUDE_PATH="${EMSDK_SYSROOT}/include${C_INCLUDE_PATH:+:$C_INCLUDE_PATH}"
        export CPLUS_INCLUDE_PATH="${EMSDK_SYSROOT}/include/c++/v1${CPLUS_INCLUDE_PATH:+:$CPLUS_INCLUDE_PATH}"
        export LIBRARY_PATH="${EMSDK_SYSROOT}/lib/wasm32-emscripten${LIBRARY_PATH:+:$LIBRARY_PATH}"
        # We need to use emscripten to build the final artifact if we link against emscripten-built LLVM.
        # But the Zig build system might not easily wrap emcc. 
        # Alternatively, we can use Zig to cross-compile to wasm32-emscripten if we point it to the right sysroot.
        # Since we just built LLVM with emcc, we should try to use zig build with -Dtarget=wasm32-emscripten.
        
        "$ZIG_DIR/zig" build -Doptimize=ReleaseFast -Dtarget=wasm32-emscripten --sysroot "$EMSDK_SYSROOT" --libc "$LIBC_CONF" -Dllvm_home="$LLVM_LIB_DIR" -Dllvm_link_dir=/llvm/lib -Dwasm_browser=true -Dsr_lang_src=/work

        PKG_BUILD_DIR="/work/_build/sr-lang-0.1.0"
        rm -rf "$PKG_BUILD_DIR" /work/sr-lang-0.1.0
        mkdir -p "$PKG_BUILD_DIR"
        cp -a zig-out/. "$PKG_BUILD_DIR/"
        cp -a /work/examples /work/docs "$PKG_BUILD_DIR/"
        mkdir -p "$PKG_BUILD_DIR/assets/vendor"
        curl -fL -o "$PKG_BUILD_DIR/assets/vendor/jquery.min.js" https://cdnjs.cloudflare.com/ajax/libs/jquery/3.7.1/jquery.min.js
        curl -fL -o "$PKG_BUILD_DIR/assets/vendor/jstree.min.js" https://cdnjs.cloudflare.com/ajax/libs/jstree/3.3.17/jstree.min.js
        curl -fL -o "$PKG_BUILD_DIR/assets/vendor/jstree.min.css" https://cdnjs.cloudflare.com/ajax/libs/jstree/3.3.17/themes/default/style.min.css
        curl -fL -o "$PKG_BUILD_DIR/assets/vendor/32px.png" https://cdnjs.cloudflare.com/ajax/libs/jstree/3.3.17/themes/default/32px.png
        curl -fL -o "$PKG_BUILD_DIR/assets/vendor/throbber.gif" https://cdnjs.cloudflare.com/ajax/libs/jstree/3.3.17/themes/default/throbber.gif
        python3 - << "PY"
import json
from pathlib import Path

root = Path("/work/examples")
paths = []
if root.exists():
    for p in sorted(root.rglob("*.sr")):
        paths.append(p.relative_to("/work").as_posix())
out = Path("/work/_build/sr-lang-0.1.0/examples.json")
out.write_text(json.dumps(paths, indent=2))
PY
        cat > "$PKG_BUILD_DIR/index.html" << "EOF"
<!doctype html>
<html lang="en">
  <head>
    <meta charset="utf-8" />
    <meta name="viewport" content="width=device-width, initial-scale=1" />
    <title>sr-lang wasm</title>
    <link rel="preconnect" href="https://fonts.googleapis.com" />
    <link rel="preconnect" href="https://fonts.gstatic.com" crossorigin />
    <link href="https://fonts.googleapis.com/css2?family=IBM+Plex+Sans:wght@400;500;600&family=Fira+Code:wght@400;500;600&display=swap" rel="stylesheet" />
    <script src="https://cdn.jsdelivr.net/npm/monaco-editor@0.45.0/min/vs/loader.js"></script>
    <link rel="stylesheet" href="https://cdn.jsdelivr.net/npm/xterm@5.3.0/css/xterm.css" />
    <link rel="stylesheet" href="./assets/vendor/jstree.min.css" />
    <style>
      *, *::before, *::after {
        box-sizing: border-box;
      }
      :root {
        color-scheme: dark;
        --vscode-bg: #1e1e1e;
        --vscode-surface: #252526;
        --vscode-sidebar: #252526;
        --vscode-panel: #1f1f1f;
        --vscode-border: #3c3c3c;
        --vscode-muted: #9da0a6;
        --vscode-text: #d4d4d4;
        --vscode-accent: #0e639c;
        --vscode-accent-soft: #1177bb;
        --vscode-tab: #2d2d2d;
        --vscode-tab-active: #1e1e1e;
        --vscode-green: #89d185;
        --vscode-red: #f14c4c;
      }
      html, body {
        height: 100%;
      }
      body {
        margin: 0;
        overflow: hidden;
        font-family: "IBM Plex Sans", "Segoe UI", system-ui, -apple-system, sans-serif;
        background: var(--vscode-bg);
        color: var(--vscode-text);
      }
      .mono {
        font-family: "Fira Code", ui-monospace, SFMono-Regular, Menlo, Monaco, Consolas, "Liberation Mono", "Courier New", monospace;
      }
      #app {
        height: 100vh;
        display: grid;
        grid-template-rows: 32px minmax(0, 1fr) minmax(180px, 32vh) 24px;
      }
      .titlebar {
        display: flex;
        align-items: center;
        justify-content: space-between;
        padding: 0 12px;
        background: #2b2b2b;
        border-bottom: 1px solid var(--vscode-border);
        font-size: 12px;
        letter-spacing: 0.04em;
        text-transform: uppercase;
        color: var(--vscode-muted);
      }
      .title-left {
        display: flex;
        align-items: center;
        gap: 10px;
      }
      .window-dots {
        display: inline-flex;
        gap: 6px;
      }
      .window-dots span {
        width: 9px;
        height: 9px;
        border-radius: 50%;
        background: #444;
      }
      .window-dots span:nth-child(1) { background: #ff5f56; }
      .window-dots span:nth-child(2) { background: #ffbd2e; }
      .window-dots span:nth-child(3) { background: #27c93f; }
      .workspace {
        display: grid;
        grid-template-columns: 48px 260px minmax(0, 1fr);
        min-height: 0;
      }
      .activitybar {
        background: #333333;
        border-right: 1px solid var(--vscode-border);
        display: flex;
        flex-direction: column;
        align-items: center;
        padding: 10px 0;
        gap: 8px;
      }
      .activity-btn {
        width: 32px;
        height: 32px;
        border: none;
        border-radius: 6px;
        background: transparent;
        color: var(--vscode-muted);
        font-size: 12px;
        font-weight: 600;
        cursor: pointer;
      }
      .activity-btn.active {
        color: #fff;
        background: #1f1f1f;
        box-shadow: inset 0 0 0 1px var(--vscode-border);
      }
      .sidebar {
        background: var(--vscode-sidebar);
        border-right: 1px solid var(--vscode-border);
        display: flex;
        flex-direction: column;
        min-height: 0;
      }
      .sidebar-header {
        padding: 10px 14px;
        font-size: 12px;
        letter-spacing: 0.08em;
        text-transform: uppercase;
        color: var(--vscode-muted);
        border-bottom: 1px solid var(--vscode-border);
      }
      .sidebar-section {
        padding: 10px 10px 16px;
        overflow: auto;
      }
      .section-title {
        font-size: 11px;
        letter-spacing: 0.08em;
        text-transform: uppercase;
        color: var(--vscode-muted);
        margin: 6px 0 8px;
      }
      #file-tree {
        font-size: 12px;
        color: var(--vscode-text);
      }
      #file-tree .jstree-anchor {
        color: var(--vscode-text);
        font-size: 12px;
        line-height: 1.8;
      }
      #file-tree .jstree-wholerow {
        border-radius: 6px;
      }
      #file-tree .jstree-clicked {
        background: #094771 !important;
        color: #fff !important;
      }
      #file-tree .jstree-clicked .jstree-anchor {
        color: #fff !important;
      }
      #file-tree .jstree-wholerow-clicked {
        background: #094771 !important;
      }
      #file-tree .jstree-hovered {
        background: #2a2d2e !important;
        color: #fff !important;
      }
      #file-tree .jstree-wholerow-hovered {
        background: #2a2d2e !important;
      }
      .editor-area {
        display: flex;
        flex-direction: column;
        min-width: 0;
        min-height: 0;
        background: var(--vscode-bg);
      }
      .editor-top {
        display: flex;
        align-items: center;
        justify-content: space-between;
        background: var(--vscode-tab);
        border-bottom: 1px solid var(--vscode-border);
        padding: 0 12px;
        height: 36px;
        gap: 12px;
      }
      .tabs-wrap {
        display: flex;
        align-items: stretch;
        gap: 4px;
        flex: 1;
        min-width: 0;
      }
      .tabs-nav {
        width: 24px;
        border: 1px solid var(--vscode-border);
        background: #1f1f1f;
        color: var(--vscode-text);
        border-radius: 4px;
        cursor: pointer;
        display: flex;
        align-items: center;
        justify-content: center;
        padding: 0;
        font-size: 12px;
        line-height: 1;
      }
      .tabs-nav:disabled {
        opacity: 0.4;
        cursor: default;
      }
      .tabs {
        display: flex;
        align-items: flex-end;
        gap: 2px;
        overflow-x: auto;
        overflow-y: hidden;
        white-space: nowrap;
        flex: 1;
        min-width: 0;
        scrollbar-width: none;
      }
      .tabs::-webkit-scrollbar {
        height: 0;
      }
      .tab {
        background: var(--vscode-tab);
        color: var(--vscode-muted);
        padding: 6px 12px;
        border-radius: 6px 6px 0 0;
        font-size: 12px;
        border: 1px solid transparent;
        cursor: pointer;
      }
      .tab:hover {
        background: #333333;
      }
      .tab.active {
        color: var(--vscode-text);
        background: var(--vscode-tab-active);
        border: 1px solid var(--vscode-border);
        border-bottom: none;
      }
      .tab .close {
        margin-left: 8px;
        border: none;
        background: transparent;
        color: inherit;
        cursor: pointer;
        font-size: 12px;
        line-height: 1;
        opacity: 0.7;
      }
      .tab .close:hover {
        opacity: 1;
      }
      .editor-actions {
        display: flex;
        align-items: center;
        gap: 8px;
      }
      .editor-actions {
        flex-wrap: wrap;
        justify-content: flex-end;
      }
      .select-wrap {
        display: flex;
        align-items: center;
        gap: 6px;
        color: var(--vscode-muted);
        font-size: 11px;
        text-transform: uppercase;
        letter-spacing: 0.06em;
      }
      .select-wrap select {
        background: #1f1f1f;
        color: var(--vscode-text);
        border: 1px solid var(--vscode-border);
        border-radius: 4px;
        padding: 4px 6px;
        font-size: 12px;
      }
      .btn {
        background: #1f1f1f;
        color: var(--vscode-text);
        border: 1px solid var(--vscode-border);
        border-radius: 4px;
        padding: 5px 10px;
        font-size: 12px;
        cursor: pointer;
      }
      .btn.primary {
        background: var(--vscode-accent);
        border-color: var(--vscode-accent);
        color: #fff;
      }
      .btn.is-disabled {
        opacity: 0.6;
        cursor: not-allowed;
      }
      #editor {
        flex: 1 1 auto;
        min-height: 0;
      }
      .panel {
        background: var(--vscode-panel);
        border-top: 1px solid var(--vscode-border);
        display: flex;
        flex-direction: column;
        min-height: 0;
      }
      .panel-header {
        height: 28px;
        display: flex;
        align-items: center;
        padding: 0 12px;
        font-size: 11px;
        letter-spacing: 0.08em;
        text-transform: uppercase;
        color: var(--vscode-muted);
        border-bottom: 1px solid var(--vscode-border);
        background: #222;
      }
      .panel-body {
        flex: 1 1 auto;
        min-height: 0;
      }
      #terminal {
        height: 100%;
      }
      #terminal .xterm-screen {
        padding: 10px;
      }
      .statusbar {
        display: flex;
        align-items: center;
        justify-content: space-between;
        padding: 0 12px;
        background: var(--vscode-accent);
        color: #fff;
        font-size: 12px;
      }
      .status {
        font-weight: 500;
      }
      .status.status-ok {
        color: #fff;
      }
      .status.status-error {
        color: #ffe6e6;
      }
      @media (max-width: 900px) {
        #app {
          grid-template-rows: 32px minmax(0, 1fr) minmax(160px, 30vh) 24px;
        }
        .workspace {
          grid-template-columns: 1fr;
          grid-template-rows: minmax(140px, 28vh) minmax(0, 1fr);
        }
        .activitybar {
          display: none;
        }
        .sidebar {
          border-right: none;
          border-bottom: 1px solid var(--vscode-border);
        }
        .editor-top {
          height: auto;
          padding: 6px 8px;
          flex-wrap: wrap;
          align-items: flex-start;
          gap: 6px;
        }
        .tabs-wrap {
          width: 100%;
        }
        .editor-actions {
          width: 100%;
          justify-content: flex-start;
        }
      }
      @media (max-width: 600px) {
        .titlebar {
          font-size: 10px;
          padding: 0 8px;
        }
        .sidebar-header, .section-title {
          font-size: 10px;
        }
        .select-wrap select, .btn {
          font-size: 11px;
        }
        .tab {
          font-size: 11px;
        }
      }
    </style>
  </head>
  <body>
    <div id="app">
      <header class="titlebar">
        <div class="title-left">
          <div class="window-dots">
            <span></span>
            <span></span>
            <span></span>
          </div>
          <div>sr-lang — wasm</div>
        </div>
        <div>Playground</div>
      </header>

      <section class="workspace">
        <nav class="activitybar">
          <button class="activity-btn active" title="Explorer">E</button>
        </nav>

        <aside class="sidebar">
          <div class="sidebar-header">Explorer</div>
          <div class="sidebar-section">
            <div class="section-title">SR-LANG EXAMPLES</div>
            <div id="file-tree"></div>
          </div>
        </aside>

        <main class="editor-area">
          <div class="editor-top">
            <div class="tabs-wrap">
              <button id="tabs-left" class="tabs-nav" aria-label="Scroll tabs left">‹</button>
              <div id="tabs" class="tabs"></div>
              <button id="tabs-right" class="tabs-nav" aria-label="Scroll tabs right">›</button>
            </div>
            <div class="editor-actions">
              <label class="select-wrap">
                <span>Mode</span>
                <select id="mode">
                  <option value="run" selected>run</option>
                  <option value="mlir">mlir</option>
                  <option value="llvm-ir">llvm-ir</option>
                </select>
              </label>
              <button id="run" class="btn primary">Run</button>
              <button id="clear" class="btn">Clear</button>
            </div>
          </div>
          <div id="editor"></div>
        </main>
      </section>

      <section class="panel">
        <div class="panel-header">Output</div>
        <div id="terminal" class="mono panel-body"></div>
      </section>

      <footer class="statusbar">
        <div>sr-lang wasm</div>
        <div id="status" class="status">Loading...</div>
      </footer>
    </div>
    <script>
      window.__amdDefine = window.define;
      window.__amdRequire = window.require;
      window.define = undefined;
      window.require = undefined;
    </script>
    <script src="./assets/vendor/jquery.min.js"></script>
    <script src="./assets/vendor/jstree.min.js"></script>
    <script>
      window.define = window.__amdDefine;
      window.require = window.__amdRequire;
    </script>
    <script type="module" src="./app.js"></script>
  </body>
</html>
EOF
        cat > "$PKG_BUILD_DIR/app.js" << "EOF"
const statusEl = document.getElementById("status");
const terminalEl = document.getElementById("terminal");
const fileTreeEl = document.getElementById("file-tree");
const tabsEl = document.getElementById("tabs");
const tabsLeft = document.getElementById("tabs-left");
const tabsRight = document.getElementById("tabs-right");
const runBtn = document.getElementById("run");
const clearBtn = document.getElementById("clear");
const modeEl = document.getElementById("mode");

let editor = null;
let worker = null;
let running = false;
let tabs = [];
let activeTabId = null;

const setStatus = (text, tone = "idle") => {
  statusEl.textContent = text;
  statusEl.className = "status";
  if (tone === "ok") statusEl.classList.add("status-ok");
  else if (tone === "error") statusEl.classList.add("status-error");
};

const { Terminal } = await import("https://cdn.jsdelivr.net/npm/xterm@5.3.0/+esm");
const { FitAddon } = await import("https://cdn.jsdelivr.net/npm/xterm-addon-fit@0.8.0/+esm");
const fitAddon = new FitAddon();
const term = new Terminal({
  convertEol: true,
  fontFamily: "\"Fira Code\", ui-monospace, Menlo, Monaco, Consolas, \"Liberation Mono\", \"Courier New\", monospace",
  fontSize: 13,
  theme: {
    background: "#1e1e1e",
    foreground: "#d4d4d4",
    black: "#000000",
    red: "#cd3131",
    green: "#0dbc79",
    yellow: "#e5e510",
    blue: "#2472c8",
    magenta: "#bc3fbc",
    cyan: "#11a8cd",
    white: "#e5e5e5",
    brightBlack: "#666666",
    brightRed: "#f14c4c",
    brightGreen: "#23d18b",
    brightYellow: "#f5f543",
    brightBlue: "#3b8eea",
    brightMagenta: "#d670d6",
    brightCyan: "#29b8db",
    brightWhite: "#ffffff",
  },
});
term.loadAddon(fitAddon);
term.open(terminalEl);
fitAddon.fit();
window.addEventListener("resize", () => fitAddon.fit());

const appendOutput = (text) => {
  const str = String(text);
  if (str.endsWith("\n")) {
    term.write(str.replace(/\n$/, "\r\n"));
  } else {
    term.write(str + "\r\n");
  }
};

const clearOutput = () => {
  term.reset();
};

const getTabLabel = (id) => id.split("/").pop();

const updateTabNav = () => {
  if (!tabsEl || !tabsLeft || !tabsRight) return;
  const maxScroll = tabsEl.scrollWidth - tabsEl.clientWidth;
  tabsLeft.disabled = tabsEl.scrollLeft <= 0;
  tabsRight.disabled = tabsEl.scrollLeft >= maxScroll - 1;
};

const scrollTabsBy = (delta) => {
  if (!tabsEl) return;
  tabsEl.scrollBy({ left: delta, behavior: "smooth" });
};

if (tabsLeft && tabsRight) {
  tabsLeft.addEventListener("click", () => scrollTabsBy(-200));
  tabsRight.addEventListener("click", () => scrollTabsBy(200));
  tabsEl.addEventListener("scroll", updateTabNav);
  window.addEventListener("resize", updateTabNav);
}

const renderTabs = () => {
  if (!tabsEl) return;
  tabsEl.innerHTML = "";
  for (const tab of tabs) {
    const btn = document.createElement("button");
    btn.type = "button";
    btn.className = "tab" + (tab.id === activeTabId ? " active" : "");
    btn.addEventListener("click", () => setActiveTab(tab.id));

    const label = document.createElement("span");
    label.textContent = tab.label;
    btn.appendChild(label);

    if (tabs.length > 1) {
      const close = document.createElement("button");
      close.type = "button";
      close.className = "close";
      close.setAttribute("aria-label", "Close tab");
      close.textContent = "×";
      close.addEventListener("click", (ev) => {
        ev.stopPropagation();
        closeTab(tab.id);
      });
      btn.appendChild(close);
    }

    tabsEl.appendChild(btn);
  }
  updateTabNav();
};

const setActiveTab = (id) => {
  const tab = tabs.find((t) => t.id === id);
  if (!tab || !editor) return;
  activeTabId = id;
  editor.setValue(tab.content);
  renderTabs();
  const activeEl = tabsEl.querySelector(".tab.active");
  if (activeEl) activeEl.scrollIntoView({ behavior: "smooth", inline: "nearest", block: "nearest" });
};

const openTab = (id, content) => {
  let tab = tabs.find((t) => t.id === id);
  if (tab) {
    tab.content = content;
  } else {
    tab = { id, label: getTabLabel(id), content };
    tabs.push(tab);
  }
  setActiveTab(id);
};

const closeTab = (id) => {
  if (tabs.length <= 1) return;
  const idx = tabs.findIndex((t) => t.id === id);
  if (idx === -1) return;
  const wasActive = tabs[idx].id === activeTabId;
  tabs.splice(idx, 1);
  if (wasActive) {
    const next = tabs[idx] || tabs[idx - 1];
    if (next) setActiveTab(next.id);
  } else {
    renderTabs();
  }
};

const bootWorker = () => {
  if (worker) worker.terminate();
  worker = new Worker("./worker.js", { type: "module" });
  worker.onmessage = (ev) => {
    const { type, msg } = ev.data || {};
    if (type === "ready") {
      if (!running) {
        setStatus("Compiler ready", "ok");
        runBtn.disabled = false;
        runBtn.classList.remove("is-disabled");
      }
      return;
    }
    if (type === "log") appendOutput(msg);
    if (type === "err") appendOutput(msg);
    if (type === "done") {
      running = false;
      runBtn.disabled = false;
      runBtn.classList.remove("is-disabled");
      setStatus("Done", "ok");
    }
  };
  worker.onerror = (ev) => {
    running = false;
    runBtn.disabled = false;
    runBtn.classList.remove("is-disabled");
    appendOutput(String(ev.message || ev));
    setStatus("Worker error", "error");
  };
};

const runOnce = () => {
  if (!editor || running) return;
  running = true;
  runBtn.disabled = true;
  runBtn.classList.add("is-disabled");
  clearOutput();
  setStatus("Running...", "idle");
  bootWorker();
  const src = editor.getValue();
  const mode = modeEl.value;
  worker.postMessage({ cmd: "run", src, mode });
};

clearBtn.addEventListener("click", clearOutput);
runBtn.addEventListener("click", runOnce);

document.addEventListener("keydown", (ev) => {
  if ((ev.ctrlKey || ev.metaKey) && ev.key === "Enter") {
    ev.preventDefault();
    runOnce();
  }
});

setStatus("Loading compiler...");
runBtn.disabled = true;
runBtn.classList.add("is-disabled");

window.require.config({
  paths: {
    vs: "https://cdn.jsdelivr.net/npm/monaco-editor@0.45.0/min/vs",
  },
});

const fetchExamples = async () => {
  try {
    const res = await fetch("./examples.json");
    if (!res.ok) return;
    const files = await res.json();
    const hasJsTree = window.$ && window.$.fn && window.$.fn.jstree;
    if (!hasJsTree) {
      setStatus("File tree failed to load", "error");
      appendOutput("jsTree not available (check AMD/UMD load).");
      return;
    }
    const nodes = [];
    const seen = new Set();
    const addNode = (id, parent, text, type) => {
      if (seen.has(id)) return;
      seen.add(id);
      nodes.push({ id, parent, text, type });
    };
    addNode("examples", "#", "examples", "folder");
    files.forEach((path) => {
      if (!path.startsWith("examples/")) return;
      const parts = path.split("/");
      let acc = "examples";
      for (let i = 1; i < parts.length; i++) {
        const name = parts[i];
        const isFile = i === parts.length - 1;
        const next = acc + "/" + name;
        addNode(next, acc, name, isFile ? "file" : "folder");
        acc = next;
      }
    });
    if (window.$(fileTreeEl).jstree(true)) {
      window.$(fileTreeEl).jstree(true).destroy();
      fileTreeEl.textContent = "";
    }
    try {
    window.$(fileTreeEl).jstree({
      core: {
        data: nodes,
        check_callback: true,
        themes: { dots: false, stripes: false },
      },
        types: {
          folder: { icon: "jstree-folder" },
          file: { icon: "jstree-file" },
        },
        plugins: ["types", "wholerow"],
      });
    window.$(fileTreeEl).on("ready.jstree", () => {
      window.$(fileTreeEl).jstree("open_all");
    });
    window.$(fileTreeEl).on("select_node.jstree", async (_ev, data) => {
      const node = data.node;
      if (!node || node.type !== "file") return;
      const res = await fetch("./" + node.id);
        if (!res.ok) return;
        const text = await res.text();
        openTab(node.id, text);
      });
    } catch (err) {
      setStatus("File tree failed to load", "error");
      appendOutput("jsTree init failed: " + String(err));
    }
  } catch (_err) {
    fileTreeEl.textContent = "";
  }
};

const createEditor = () => {
  const defaultFile = "examples/basics/01_hello.sr";
  editor = monaco.editor.create(document.getElementById("editor"), {
    value: "",
    language: "rust",
    theme: "vs-dark",
    minimap: { enabled: false },
    fontFamily: "\"Fira Code\", ui-monospace, Menlo, Monaco, Consolas, \"Liberation Mono\", \"Courier New\", monospace",
    fontSize: 13,
    lineNumbers: "on",
    roundedSelection: true,
    scrollBeyondLastLine: false,
    padding: { top: 16, bottom: 16 },
  });
  tabs = [];
  activeTabId = null;
  renderTabs();
  editor.onDidChangeModelContent(() => {
    const tab = tabs.find((t) => t.id === activeTabId);
    if (tab) tab.content = editor.getValue();
  });
  setStatus("Editor ready", "ok");
  runBtn.disabled = false;
  runBtn.classList.remove("is-disabled");
  fetchExamples();
  fetch("./" + defaultFile).then((res) => {
    if (!res.ok) throw new Error("Default file not found");
    return res.text();
  }).then((text) => {
    openTab(defaultFile, text);
  }).catch((err) => {
    appendOutput(String(err));
    setStatus("Default file failed to load", "error");
  });
};

if (window.monaco && window.monaco.editor) {
  createEditor();
} else {
  window.require(["vs/editor/editor.main"], () => {
    createEditor();
  });
}
EOF
        cat > "$PKG_BUILD_DIR/worker.js" << "EOF"
const post = (type, msg) => postMessage({ type, msg });

let Module = null;

const init = async () => {
  const createModule = (await import("./sr_lang.js")).default;
  Module = await createModule({
    locateFile: (p) => p,
    print: (txt) => post("log", txt),
    printErr: (txt) => post("err", txt),
    noInitialRun: true,
  });
  post("ready");
};

const ready = init();

onmessage = async (ev) => {
  const { cmd, src, mode } = ev.data || {};
  if (cmd !== "run") return;
  await ready;
  try {
    const m = mode || "run";
    const compileMode = m === "run" ? "wasm" : m;
    const path = "/input.sr";
    const args = ["sr_lang", compileMode];
    Module.FS.writeFile(path, src);
    args.push(path);
    Module.callMain(args);
    if (compileMode === "wasm") {
      const wasmPath = "/out/output.wasm";
      if (!Module.FS.analyzePath(wasmPath).exists) {
        throw new Error("output.wasm not found");
      }
      const bytes = Module.FS.readFile(wasmPath, { encoding: "binary" });
      const buf = bytes.buffer.slice(bytes.byteOffset, bytes.byteOffset + bytes.byteLength);
      const memory = new WebAssembly.Memory({ initial: 256 });
      const stackPtrInit = memory.buffer.byteLength - 16;
      const encoder = new TextEncoder();
      const decoder = new TextDecoder("utf-8");
      const toNum = (v) => (typeof v === "bigint" ? Number(v) : v);
      const toU32 = (v) => (toNum(v) >>> 0);
      const readCString = (ptr) => {
        const p = toNum(ptr) >>> 0;
        const bytes = new Uint8Array(memory.buffer);
        let end = p;
        while (bytes[end] !== 0) end++;
        return decoder.decode(bytes.subarray(p, end));
      };
      const writeCString = (ptr, text) => {
        const data = encoder.encode(text + "\0");
        const bytes = new Uint8Array(memory.buffer);
        bytes.set(data, toU32(ptr));
        return data.length - 1;
      };
      const align = (off, a) => (off + (a - 1)) & ~(a - 1);
      const dv = () => new DataView(memory.buffer);
      const readI32 = (off) => dv().getInt32(off, true);
      const readU32 = (off) => dv().getUint32(off, true);
      const readI64 = (off) => Number(dv().getBigInt64(off, true));
      const readU64 = (off) => Number(dv().getBigUint64(off, true));
      const readF64 = (off) => dv().getFloat64(off, true);
      const readStringAt = (ptr, len) => {
        const bytes = new Uint8Array(memory.buffer, toU32(ptr), toU32(len));
        return decoder.decode(bytes);
      };
      let heapPtr = 0;
      const align8 = (n) => (n + 7) & ~7;
      const ensureCapacity = (bytesNeeded) => {
        const need = heapPtr + bytesNeeded;
        const pageSize = 65536;
        while (need > memory.buffer.byteLength) {
          memory.grow(1);
        }
      };
      const initHeap = (inst) => {
        const hb = inst.instance.exports.__heap_base;
        if (hb !== undefined) {
          heapPtr = typeof hb === "object" && hb.value !== undefined ? toU32(hb.value) : toU32(hb);
        } else if (heapPtr === 0) {
          heapPtr = 1024;
        }
        heapPtr = align8(heapPtr);
      };
      const memcmp = (a, b, len) => {
        const bytes = new Uint8Array(memory.buffer);
        for (let i = 0; i < len; i++) {
          const av = bytes[a + i];
          const bv = bytes[b + i];
          if (av !== bv) return av - bv;
        }
        return 0;
      };
      const memset = (dst, value, len) => {
        const bytes = new Uint8Array(memory.buffer);
        bytes.fill(value & 0xff, dst, dst + len);
      };
      const memcpy = (dst, src, len) => {
        const bytes = new Uint8Array(memory.buffer);
        bytes.copyWithin(dst, src, src + len);
      };
      const mapWrite = (outPtr, len, entriesPtr, entriesLen, entriesCap) => {
        const view = dv();
        view.setUint32(outPtr + 0, toU32(len), true);
        view.setUint32(outPtr + 4, toU32(entriesPtr), true);
        view.setUint32(outPtr + 8, toU32(entriesLen), true);
        view.setUint32(outPtr + 12, toU32(entriesCap), true);
      };
      const mapRead = (ptr) => {
        const view = dv();
        return {
          len: view.getUint32(ptr + 0, true),
          entriesPtr: view.getUint32(ptr + 4, true),
          entriesLen: view.getUint32(ptr + 8, true),
          entriesCap: view.getUint32(ptr + 12, true),
        };
      };

      const formatPrintf = (fmtPtr, args) => {
        const fmt = readCString(fmtPtr);
        let out = "";
        let ai = 0;
        for (let i = 0; i < fmt.length; i++) {
          const ch = fmt[i];
          if (ch !== "%") {
            out += ch;
            continue;
          }
          const next = fmt[++i];
          if (next === "%") { out += "%"; continue; }
          const arg = args[ai++];
          switch (next) {
            case "s":
              out += readCString(arg);
              break;
            case "d":
            case "i":
              out += (typeof arg === "bigint" ? arg.toString() : String(arg | 0));
              break;
            case "u":
              out += (typeof arg === "bigint" ? arg.toString() : String(arg >>> 0));
              break;
            case "f":
              out += String(Number(arg));
              break;
            case "c":
              out += String.fromCharCode(Number(arg) & 0xff);
              break;
            default:
              out += "%" + next;
              break;
          }
        }
        return out;
      };
      const env = {
        __linear_memory: memory,
        __indirect_function_table: new WebAssembly.Table({ initial: 256, element: "anyfunc" }),
        __stack_pointer: new WebAssembly.Global({ value: "i32", mutable: true }, stackPtrInit),
        __memory_base: new WebAssembly.Global({ value: "i32", mutable: false }, 0),
        __table_base: new WebAssembly.Global({ value: "i32", mutable: false }, 0),
        abort: () => { throw new Error("wasm abort"); },
        rt_has_percent: (ptr, len) => {
          const bytes = new Uint8Array(memory.buffer, toU32(ptr), toU32(len));
          for (let i = 0; i < bytes.length; i++) {
            if (bytes[i] === 37) return 1;
          }
          return 0;
        },
        rt_print: (ptr, len) => {
          const bytes = new Uint8Array(memory.buffer, toU32(ptr), toU32(len));
          post("log", decoder.decode(bytes));
        },
        rt_eprint: (ptr, len) => {
          const bytes = new Uint8Array(memory.buffer, toU32(ptr), toU32(len));
          post("err", decoder.decode(bytes));
        },
        rt_panic: (ptr, len) => {
          const bytes = new Uint8Array(memory.buffer, toU32(ptr), toU32(len));
          const msg = decoder.decode(bytes);
          post("err", msg);
          throw new Error(msg || "panic");
        },
        rt_abort: () => {
          throw new Error("abort");
        },
        rt_printf_pack: (fmtPtr, argsPtr) => {
          const fmt = readCString(fmtPtr);
          let out = "";
          let off = 0;
          for (let i = 0; i < fmt.length; i++) {
            const ch = fmt[i];
            if (ch !== "%") { out += ch; continue; }
            const next = fmt[++i];
            if (next === "%") { out += "%"; continue; }
            switch (next) {
              case "s": {
                off = align(off, 8);
                const p = readU32(toU32(argsPtr) + off);
                const len = readU64(toU32(argsPtr) + off + 8);
                out += readStringAt(p, len);
                off += 16;
                break;
              }
              case "d":
              case "i": {
                off = align(off, 8);
                const v = readI64(toU32(argsPtr) + off);
                out += String(v);
                off += 8;
                break;
              }
              case "u": {
                off = align(off, 8);
                const v = readU64(toU32(argsPtr) + off);
                out += String(v);
                off += 8;
                break;
              }
              case "f": {
                off = align(off, 8);
                const v = readF64(toU32(argsPtr) + off);
                out += String(v);
                off += 8;
                break;
              }
              case "c": {
                off = align(off, 4);
                const v = readI32(toU32(argsPtr) + off);
                out += String.fromCharCode(v & 0xff);
                off += 4;
                break;
              }
              default:
                out += "%" + next;
                break;
            }
          }
          if (out.length) post("log", out);
          return out.length;
        },
        sprintf: (bufPtr, fmtPtr, ...args) => {
          const out = formatPrintf(fmtPtr, args);
          return writeCString(bufPtr >>> 0, out);
        },
        rt_alloc: (size) => {
          const n = align8(toU32(size));
          const total = n + 8;
          ensureCapacity(total);
          const base = heapPtr;
          heapPtr += total;
          const view = dv();
          view.setUint32(base, n, true);
          return base + 8;
        },
        rt_realloc: (ptr, newSize) => {
          const n = align8(toU32(newSize));
          if (!ptr) return env.rt_alloc(n);
          const p = toU32(ptr);
          const base = p - 8;
          const view = dv();
          const old = view.getUint32(base, true);
          const out = env.rt_alloc(n);
          const copyLen = Math.min(old, n);
          if (copyLen > 0) {
            const bytes = new Uint8Array(memory.buffer);
            bytes.copyWithin(out, p, p + copyLen);
          }
          return out;
        },
        rt_free: (_ptr) => {},
        builtin_map_empty: (outPtr) => {
          mapWrite(toU32(outPtr), 0, 1, 0, 0);
        },
        builtin_map_from_kv: (outPtr, kvPtr, entrySize, count) => {
          const cnt = toU32(count);
          const es = toU32(entrySize);
          if (cnt === 0 || es === 0) {
            mapWrite(toU32(outPtr), 0, toU32(kvPtr), 0, 0);
            return;
          }
          const bytes = es * cnt;
          const dst = env.rt_alloc(bytes);
          memcpy(toU32(dst), toU32(kvPtr), bytes);
          mapWrite(toU32(outPtr), cnt, toU32(dst), cnt, cnt);
        },
        builtin_map_get_or_insert: (mapPtr, keyPtr, keySize, entrySize, valueOffset) => {
          const mp = toU32(mapPtr);
          const kptr = toU32(keyPtr);
          const ksz = toU32(keySize);
          const es = toU32(entrySize);
          const voff = toU32(valueOffset);
          let m = mapRead(mp);
          for (let i = 0; i < m.entriesLen; i++) {
            const entryPtr = m.entriesPtr + i * es;
            if (memcmp(entryPtr, kptr, ksz) === 0) {
              return entryPtr + voff;
            }
          }
          const wantLen = m.entriesLen + 1;
          let newCap = m.entriesCap === 0 ? 4 : m.entriesCap;
          while (newCap < wantLen) newCap *= 2;
          const newBytes = newCap * es;
          let newPtr;
          if (m.entriesCap === 0) {
            newPtr = env.rt_alloc(newBytes);
          } else {
            newPtr = env.rt_realloc(m.entriesPtr, newBytes);
          }
          m.entriesPtr = toU32(newPtr);
          m.entriesCap = newCap;
          m.entriesLen = wantLen;
          m.len = wantLen;
          mapWrite(mp, m.len, m.entriesPtr, m.entriesLen, m.entriesCap);
          const entryPtr = m.entriesPtr + (wantLen - 1) * es;
          memset(entryPtr, 0, es);
          memcpy(entryPtr, kptr, ksz);
          return entryPtr + voff;
        },
        fflush: (_fp) => 0,
        scanf: (_fmtPtr, ..._args) => 0,
      };
      const inst = await WebAssembly.instantiate(buf, { env });
      initHeap(inst);
      if (inst.instance.exports._start) {
        inst.instance.exports._start();
      } else if (inst.instance.exports.main) {
        inst.instance.exports.main();
      }
    }
    postMessage({ type: "done" });
  } catch (err) {
    post("err", String(err));
    postMessage({ type: "done" });
  }
};
EOF
        cp -a "$PKG_BUILD_DIR" /work/sr-lang-0.1.0
        tar -czf /work/sr-lang-0.1.0-wasm32-emscripten.tar.gz -C /work/_build sr-lang-0.1.0
        echo "WASM Build Complete: sr-lang-0.1.0-wasm32-emscripten.tar.gz"
    elif [ "$BUILD_TARGET" == "wasm-wasi" ]; then
        LLVM_LIB_DIR="$BUILD_DIR/install/lib"
        "$ZIG_DIR/zig" build -Doptimize=ReleaseFast -Dtarget=wasm32-wasi -Dllvm_home="$LLVM_LIB_DIR"
        
        mv zig-out sr-lang-0.1.0
        cp -r /work/examples /work/sr-lang-0.1.0/
        cp -r /work/docs /work/sr-lang-0.1.0/
        tar -czf sr-lang-0.1.0-wasm32-wasi.tar.gz sr-lang-0.1.0
        echo "WASM Build Complete: sr-lang-0.1.0-wasm32-wasi.tar.gz"
    else
        LLVM_LIB_DIR="$BUILD_DIR/lib"
        "$ZIG_DIR/zig" build -Doptimize=ReleaseFast -Dllvm_home="$LLVM_LIB_DIR"
        
        mv zig-out sr-lang-0.1.0
        cp -r /work/examples /work/sr-lang-0.1.0/
        cp -r /work/docs /work/sr-lang-0.1.0/
        tar -czf sr-lang-0.1.0-linux-x86_64.tar.gz sr-lang-0.1.0

        cat > /work/_tmp_hello.sr << "EOF"
package main

io :: import "std/io"

main :: proc() {
   io.print("Hello World\\n")
}
EOF
        /work/sr-lang-0.1.0/bin/src run /work/_tmp_hello.sr
    fi
  '
