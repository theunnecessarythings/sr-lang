CXX            := clang++
CC             := clang

CXXFLAGS       := -std=c++17 -fPIC
CFLAGS         := -std=c11 

# Linker flags for test executable
LDFLAGS        := -lskia -lglfw -lGLEW -lGL -lpthread -ldl -lm
SKIA_DEPS_LIBS := -lfontconfig -lfreetype -lpng -lz -lharfbuzz -lexpat -ljpeg -licuuc -licui18n -lwebpdemux -lwebp
LDFLAGS += $(SKIA_DEPS_LIBS)

# Linker flags for shared library
SO_LDFLAGS     := -lskia
SO_LDFLAGS += $(SKIA_DEPS_LIBS)

C_TARGET       := test_c
SO_TARGET      := libskiac.so

C_SRC          := test.c
SKIAC_SRC      := skiac.cpp

SKIAC_OBJ      := $(SKIAC_SRC:.cpp=.o)
C_OBJ          := $(C_SRC:.c=.o)

.PHONY: all clean run run_c shared

all: $(C_TARGET) shared

shared: $(SO_TARGET)

$(SO_TARGET): $(SKIAC_OBJ) skiac.h
	$(CXX) $(CXXFLAGS) -shared -o $@ $< $(SO_LDFLAGS)

$(C_TARGET): $(C_OBJ) $(SKIAC_OBJ)
	$(CXX) $(CXXFLAGS) -o $@ $^ $(LDFLAGS)

run_c: $(C_TARGET)
	./$(C_TARGET)

$(SKIAC_OBJ): $(SKIAC_SRC) skiac.h
	$(CXX) $(CXXFLAGS) -c -o $@ $<

$(C_OBJ): $(C_SRC) skiac.h
	$(CC) $(CFLAGS) -c -o $@ $<

clean: 
	rm -f $(C_TARGET) $(SO_TARGET) $(SKIAC_OBJ) $(C_OBJ)