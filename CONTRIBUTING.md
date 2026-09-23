# Contribution Guide

## Contributions

You can contribute this to collection by either
1. implementing a program and proving its correctness and its desired time complexity using the API provided at [Instrumentation.lean](./VeriQuick/Instrumentation.lean), or
2. enhance the instrumentation feature at [Instrumentation.lean](./VeriQuick/Instrumentation.lean).

Both contributions are highly welcome.
Any bug reports are also welcome.

## Guideline

### Implementation and Proof

For the program implementation and proof, please send us a PR to this GitHub repository.
The PR should include
- `Algorithms/<AlgoName>/Complexity.lean`
- `Algorithms/<AlgoName>/Correctness.lean`
- `Algorithms/<AlgoName>/Impl.lean`

Please refer to the examples at [MergeSort](./Algorithms/MergeSort) and [Euclidean](./Algorithms/Euclidean).

### Instrumentation

We provide instrumentation to automatically convert a computable Lean function to have a time tick, to abstractly represent the execution time.
The instrumentation feature is highly experimental. However, the feature should support the followings:
1. Instrument any computable Lean functions.
   If you find any lean functions that cannot be instrumented,
   please report and its fix. You should be able to explain what was the bottleneck.
2. Provide a proof that the instrumentation does not alter the semantics of the original program.
   For example, for a function `f`, this should generate `f_timed_value : ∀ args, TimeM.value (f_timed args) = f args`.
   Here, `f_timed` is the instrumented function, and
   `TimeM.value` extracts the computed value from the instrumented function.

## Recommended List of Algorithms and Data Structures

- [x] [BinarySearch](https://en.wikipedia.org/wiki/Binary_search) - PR [#2](https://github.com/prosyslab/veriquick/pull/2)
- [ ] [Heap](https://en.wikipedia.org/wiki/Heap_(data_structure))
- [ ] [UnionFind](https://en.wikipedia.org/wiki/Disjoint-set_data_structure)
- [ ] [RBTree](https://en.wikipedia.org/wiki/Red%E2%80%93black_tree)
- [ ] [MaxSubarray](https://en.wikipedia.org/wiki/Maximum_subarray_problem)
- [ ] [ModExp](https://en.wikipedia.org/wiki/Modular_exponentiation#Right-to-left_binary_method)
- [ ] [KMP](https://en.wikipedia.org/wiki/Knuth%E2%80%93Morris%E2%80%93Pratt_algorithm)
- [ ] [DFS](https://en.wikipedia.org/wiki/Depth-first_search)
- [ ] [BFS](https://en.wikipedia.org/wiki/Breadth-first_search)
- [ ] [Dijkstra](https://en.wikipedia.org/wiki/Dijkstra%27s_algorithm)
- [ ] [Kruskal](https://en.wikipedia.org/wiki/Kruskal%27s_algorithm)
- [ ] [TopoSort](https://en.wikipedia.org/wiki/Topological_sorting)
- [ ] [ConvexHull](https://en.wikipedia.org/wiki/Convex_hull_algorithms)
- [ ] [FloydWarshall](https://en.wikipedia.org/wiki/Floyd%E2%80%93Warshall_algorithm)
- [ ] [MaxFlow](https://en.wikipedia.org/wiki/Maximum_flow_problem)
- [ ] [RodCutting](https://go.algorithmexamples.com/web/dynamic-programming/rod-cutting.html)
- [ ] [Select](https://en.wikipedia.org/wiki/Selection_algorithm)
- [ ] [ActivitySelection](https://en.wikipedia.org/wiki/Activity_selection_problem)
- [ ] [LCS](https://en.wikipedia.org/wiki/Longest_common_subsequence)
- [ ] [MatrixChain](https://en.wikipedia.org/wiki/Matrix_chain_multiplication)

