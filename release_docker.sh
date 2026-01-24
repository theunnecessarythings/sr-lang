#!/usr/bin/env bash
set -euo pipefail

LLVM_COMMIT_DEFAULT="a992f29451b9e140424f35ac5e20177db4afbdc0"
LLVM_COMMIT="${1:-$LLVM_COMMIT_DEFAULT}"

IMAGE_TAG="${2:-sr-lang-release:ubuntu22.04}"
ZIG_VERSION="${ZIG_VERSION:-0.15.2}"
ZIG_URL="${ZIG_URL:-https://ziglang.org/download/$ZIG_VERSION/zig-x86_64-linux-$ZIG_VERSION.tar.xz}"

LLVM_DIR="/work/_llvm/llvm-project"
BUILD_DIR="/work/_llvm/build-${LLVM_COMMIT}"
MARKER="${BUILD_DIR}/.installed"

exec docker run --rm -it \
  -v "${PWD}":/work -w /work \
  -e LLVM_COMMIT="${LLVM_COMMIT}" \
  -e LLVM_DIR="${LLVM_DIR}" \
  -e BUILD_DIR="${BUILD_DIR}" \
  -e MARKER="${MARKER}" \
  -e ZIG_VERSION="${ZIG_VERSION}" \
  -e ZIG_URL="${ZIG_URL}" \
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
    git checkout "$LLVM_COMMIT"

    if [ ! -f "$MARKER" ]; then
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
      touch "$MARKER"
    else
      echo "LLVM/MLIR already built for $LLVM_COMMIT"
    fi

    cd /work
    if command -v clang-18 >/dev/null 2>&1; then
      export CC=clang-18
      export CXX=clang++-18
      ln -sf "$(command -v clang-18)" /usr/local/bin/clang
      ln -sf "$(command -v clang++-18)" /usr/local/bin/clang++
    fi
    if [ ! -e /usr/lib/libstdc++.so.6 ] && [ -e /usr/lib/x86_64-linux-gnu/libstdc++.so.6 ]; then
      ln -s /usr/lib/x86_64-linux-gnu/libstdc++.so.6 /usr/lib/libstdc++.so.6
    fi
    if [ ! -f /usr/local/include/mlir-c/IR.h ]; then
      INCLUDE_FALLBACKS=("$BUILD_DIR/include" "$BUILD_DIR/tools/mlir/include" "$LLVM_DIR/mlir/include" "$LLVM_DIR/llvm/include" "/usr/local/include")
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
    LLVM_LIB_DIR="$BUILD_DIR/lib"
    LLVM_INCLUDE_DIR="$BUILD_DIR/include"
    "$ZIG_DIR/zig" build -Doptimize=ReleaseFast -Dllvm_home="$LLVM_LIB_DIR"
    rm -rf sr-lang-0.1.0
    mv zig-out sr-lang-0.1.0
    tar -czf sr-lang-0.1.0-linux-x86_64.tar.gz sr-lang-0.1.0

    cat > /work/_tmp_hello.sr << "EOF"
package main

io :: import "std/io"

main :: proc() {
   io.print("Hello World\\n")
}
EOF
    /work/sr-lang-0.1.0/bin/src run /work/_tmp_hello.sr
  '
