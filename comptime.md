lex -> parse -> lower -> checker -> lower_tir -> mlir -> execute
                            |                               |
                            <--------------------------------                                  
- Checker
  comptime_nodes = set()

  collect comptime nodes during checking

- Comptime eval
  - compute dependenciees of collected nodes
  - topological sort
  - create new main function with calls to  wrap each comptime node into a fn in order
  - lower to tir, mlir, execute
  - get results back to checker
  - replace comptime nodes with results
  - go back to checker and until no more comptime nodes


- Computing Dependencies
  - direct dependencies: function calls, variable uses
  - indirect dependencies: if a function calls another function that is comptime, it is also comptime
  - handle cycles: report error if there is a cycle in comptime dependencies

- Topological Sort
  - use Kahn's algorithm or DFS to sort comptime nodes based on dependencies
  - ensure that all dependencies of a node are computed before the node itself


- Wrapping Comptime Nodes
  - for each comptime node, create a function that computes its value
  - ensure that the function has no side effects and only depends on its inputs
  - return type will be the type of the comptime node
  - arguments will be the dependencies of the comptime node
