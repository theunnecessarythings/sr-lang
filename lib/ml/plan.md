# Plan for `lib/ml`: A PyTorch-like ML Library in Sr

## 1. Goals and Philosophy

The primary goal is to develop a machine learning library in the Sr language, with an API inspired by PyTorch. The library, `lib/ml`, will be designed for high performance by leveraging MLIR for its computational backend from the outset.

Key principles:
- **Idiomatic Sr:** The library should use Sr's features like `comptime`, generics, and `mlir` blocks to create a clean and powerful API.
- **High Performance by Default:** Computationally intensive operations (e.g., matrix multiplication, element-wise ops) will be implemented in MLIR from the start using dialects like `tensor`, `linalg`, and `vector`.
- **Ease of Use:** The API should be familiar to users of PyTorch, enabling a smooth transition.
- **Automatic Differentiation:** A core feature will be a robust automatic differentiation engine.

## 2. Core Components

The library will be structured into several key modules:

### a. `Tensor`

The `Tensor` will be the central data structure, built on top of the native `tensor` type.

- **Definition:** A wrapper around a native `tensor` to associate it with gradient information.
  ```sr
  Tensor :: fn(comptime T: type, comptime Rank: int) type {
      return struct {
          data: tensor(T, Rank), // Native tensor for storage and ops
          requires_grad: bool,
          grad: ?*Tensor(T, Rank),
          grad_fn: ?*proc(*Tensor(T, Rank)), 
      }
  }
  ```
- **API:**
    - **Constructors:** `ml.new(shape, data)`, `ml.ones(shape)`, `ml.zeros(shape)`, `ml.rand(shape)`. These will create `Tensor` structs containing MLIR-generated constants or results.
    - **Element-wise Ops:** Overloaded operators `+`, `-`, `*`, `/`. Implemented via `mlir op` blocks.
    - **Reductions:** `sum()`, `mean()`. Implemented via MLIR.
    - **Linear Algebra:** `matmul()`. Implemented with `linalg.matmul` in an `mlir op` block.
    - **Manipulation:** `reshape()`, `transpose()`.

### b. `autograd` Engine

This engine will track operations to compute gradients automatically.

- **Mechanism:** When an operation is performed on a `Tensor` with `requires_grad = true`, a computational graph is built. Each new `Tensor` produced will have a `grad_fn` that points to a function for computing the gradient for the operation.
- **`backward()` method:** Calling `tensor.backward()` will trigger a reverse-mode traversal of the graph, accumulating gradients in the `.grad` field of the leaf tensors.

### c. `nn` Module

This module will provide building blocks for neural networks, similar to `torch.nn`.

- **`Module` concept:** A base component for all neural network layers. It will provide methods like `parameters()` to retrieve all learnable weights.
- **Layers:**
    - `nn.Linear`: A fully connected layer.
    - `nn.Conv2d`: A 2D convolution layer.
- **Activation Functions:**
    - `nn.ReLU`
    - `nn.Sigmoid`
    - `nn.Softmax`
- **Loss Functions:**
    - `nn.MSELoss` (Mean Squared Error)
    - `nn.CrossEntropyLoss`

### d. `optim` Module

This module will contain optimization algorithms.

- **`Optimizer` concept:** A base for all optimizers.
- **Algorithms:**
    - `optim.SGD`: Stochastic Gradient Descent.
    - `optim.Adam`: Adam optimizer.
- **API:**
    - `optimizer.step()`: Updates the model parameters based on the computed gradients.
    - `optimizer.zero_grad()`: Resets the gradients of all parameters.

## 3. Step-by-Step Implementation Plan

### Phase 1: Core `Tensor` with MLIR Ops

1.  **File:** `lib/ml/tensor.sr`
2.  **Tasks:**
    - Define the `Tensor` wrapper struct.
    - Implement constructors (`new`, `ones`, `zeros`) using `mlir op` blocks to generate `arith.constant` with tensor types.
    - Implement element-wise arithmetic operators (`+`, `-`, `*`, `/`) directly using MLIR kernels (e.g., with `linalg.generic`).
    - Implement `matmul` using `linalg.matmul`.
    - Write unit tests for all `Tensor` functionality, verifying the results of the MLIR operations.

### Phase 2: Automatic Differentiation

1.  **File:** `lib/ml/autograd.sr`
2.  **Tasks:**
    - Augment the `Tensor` struct with `requires_grad`, `grad`, and `grad_fn` fields.
    - For each MLIR-based operation, define its corresponding backward function. The backward function will also be an MLIR kernel.
    - When an operation is performed, create a `grad_fn` closure that captures the inputs and the backward function.
    - Implement the `backward()` method on `Tensor` to perform the reverse-pass and accumulate gradients.
    - Write tests to verify gradient correctness.

### Phase 3: Neural Network (`nn`) Module

1.  **File:** `lib/ml/nn.sr`
2.  **Tasks:**
    - Define a `Module` concept/struct that can track parameters.
    - Implement the `Linear` layer. Its forward pass will use `ml.matmul`.
    - Implement the `ReLU` activation function using MLIR.
    - Implement `MSELoss`.
    - Write tests for the `Linear` layer and loss functions.

### Phase 4: Optimizer (`optim`) Module

1.  **File:** `lib/ml/optim.sr`
2.  **Tasks:**
    - Define an `Optimizer` concept.
    - Implement the `SGD` optimizer. The `step()` method will use MLIR kernels to update tensor values.
    - Write tests to ensure the optimizer correctly updates parameters.

### Phase 5: End-to-End Example

1.  **File:** `examples/ml_train_mlp.sr`
2.  **Tasks:**
    - Create a simple dataset.
    - Build a small Multi-Layer Perceptron (MLP) using the `nn` module.
    - Write a training loop:
        - Forward pass.
        - Compute loss.
        - `backward()` pass.
        - Optimizer `step()`.
    - This example will serve as a demonstration of the library's capabilities and as an integration test.