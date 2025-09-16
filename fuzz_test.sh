#!/bin/bash
zig build
clang++-20 -O1 -g -fsanitize=fuzzer,address,undefined \
  tests/fuzzer.cc zig-out/lib/libfuzzer.a -o zig-out/bin/fuzzer
./zig-out/bin/fuzzer tests/corpus examples/ -seed=43 -print_final_stats=1  -print_corpus_stats=1 -artifact_prefix=crashers/ -timeout=5 -max_total_time=180
kcov --include-path=$(pwd)/src --verify coverage_fuzz ./zig-out/bin/fuzzer tests/corpus/ examples/ -runs=10000
