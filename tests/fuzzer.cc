#include <stddef.h>
#include <stdint.h>
extern "C" void fuzz_lexer(const uint8_t *data, size_t size);
extern "C" void fuzz_parser(const uint8_t *data, size_t size);
extern "C" void fuzz_lower(const uint8_t *data, size_t size);
extern "C" void fuzz_checker(const uint8_t *data, size_t size);
extern "C" void fuzz_infer(const uint8_t *data, size_t size);

extern "C" int LLVMFuzzerTestOneInput(const uint8_t *Data, size_t Size) {
  fuzz_lexer(Data, Size);
  fuzz_parser(Data, Size);
  fuzz_lower(Data, Size);
  fuzz_checker(Data, Size);
  fuzz_infer(Data, Size);
  return 0;
}
