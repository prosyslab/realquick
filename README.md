# Real Quick Benchmark

`RealQuick` is a collection of real-quick programs.
"Real quick" is an informal term meaning "very fast" in American English.
Here, we presents programs that are
really (that is mathematically proven) quick (performant).

## Cost Model

To show a program is fast, we define a cost model,
similar to the technique in time complexity analysis.

In our cost model, a program has an additional tick state.
A tick is a natural number (`Nat` in Lean),
and it starts from zero at the beginning of the program execution.
Then, each primitive operation (arithmetic operation, comparison, etc.)
increases the tick by a predefined amount.
At the end of the execution, the program will return the execution result as well as
the final tick.

To realize this method in Lean, we use `TimeM` monad.
A monad is a way of representing extra state of the original program.
Formally, if a program returns a value of type `α`, our `TimeM` monad will add
the extra state of tick: `α ✕ Nat`.
Here, we refer to a program that returns `α ✕ Nat` as 'timed' program.

This method is widely used in other projects too.
Refer the following code and paper:
- [Time Monad Definition in the CSLib](https://github.com/leanprover/cslib/blob/main/Cslib/Algorithms/Lean/TimeM.lean)
- [Lightweight semiformal time complexity analysis for purely functional data structures (Danielsson, 2008)](https://dl.acm.org/doi/10.1145/1328897.1328457)

## Instrumentation

Performance proofs, including time complexity analysis, are dependent on what costs are being measured:
Comparisons? Arithmetic Operations? Memory Read and Writes? Each person can decide whatever they want.
This can worsen the trustworthiness of each proof.
To truly believe the proof is legitimate, we need to inspect how the code is written
and what costs are measured.

To alleviate this burden, we offer an instrumentation tool
that automatically converts a function into a 'timed' function.
The instrumentation ensures that the timed function to increase
the tick for every comparison, arithmetic operation, and memory operation.

If you find this tool limited for the program of your interest,
you can send a PR to improve the instrumentation.

### Example

```lean
def linearSearch (x: Nat) (xs : List Nat) : Bool :=
  match xs with
  | [] => false
  | hd :: tl =>
    if x = hd then true
    else linearSearch x tl

#instrument linearSearch as linearSearch_timed
-- Lean 4: Instrumented `linearSearch` as `linearSearch_timed`; value theorem: `linearSearch_timed_value`
```

Here, `#instrument` generates the followings:
- the timed function (`linearSearch_timed`) for the input program,
- the proof that the timed function returns the same value as the original function does
  (`linearSearch_timed_value`).

## Target Programs

We set here target programs for performance analysis.
1. algorithms and data structures: this is the primary focus at the moment,
2. real-world programs: how do we ensure that an optimized program is really optimized? this is the next goal.
