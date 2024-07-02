
/-! # Code to ---

This file provides functions to generate partial matroids for testing. Would likely be used to
generate the remaining options for the vamos matroids.

## Main definitions

* `combinations`: returns all combinations (without repeat) of n elements of size m
-/

/--takes in two natural numbers n and k and returns a series of lists containing every combination
of length k containing elements in n. -/
def combinations : Nat → Nat → List (List Nat)
  | _, 0 => [[]]
  | 0, _ + 1 => []
  | n + 1, k + 1 => (combinations n (k + 1)) ++ ((combinations n k).map (· ++ [n]))
