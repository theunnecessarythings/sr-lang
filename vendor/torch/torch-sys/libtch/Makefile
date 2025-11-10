# Makefile for torch_api

# Path to libtorch. Must be set as an environment variable.
ifndef LIBTORCH
    $(error LIBTORCH is not set. Please set it to the root of your libtorch installation)
endif

CXX := g++
CXXFLAGS := -fPIC -I$(LIBTORCH)/include -I$(LIBTORCH)/include/torch/csrc/api/include -I.
LDFLAGS := -shared -L$(LIBTORCH)/lib -ltorch -ltorch_cpu -lc10

TARGET := libtorch_api.so
OBJECTS := torch_api_generated.o torch_api.o

all: $(TARGET)

$(TARGET): $(OBJECTS)
	$(CXX) $(LDFLAGS) -o $@ $(OBJECTS)

%.o: %.cpp
	$(CXX) $(CXXFLAGS) -c $< -o $@

clean:
	rm -f $(TARGET) $(OBJECTS)