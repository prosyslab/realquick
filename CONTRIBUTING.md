# Contribution Guide

## Contributions

You can contribute this to collection by either
1. implementing a program and proving its correctness and its desired time complexity using the API provided at [Instrumentation.lean](./RealQuick/Instrumentation.lean), or
2. enhance the instrumentation feature at [Instrumentation.lean](./RealQuick/Instrumentation.lean).

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
