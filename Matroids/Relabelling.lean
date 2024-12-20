import Matroids.PartialMatroid
import Matroids.Count
import Mathlib.Util.Time

/-! # Code to group check for repeat PartialMatroids based on permutations

This file provides functions to check if there are any duplicate partial matroids in each bucket.
Because different buckets indicates a different series of connections, we assume that different
buckets indicate a different partial matroid.

## Main definitions

* `permutation`: allows us to get all permutations of magnitude n (should be number of points)
* `relabelling`: allows us to apply conditions to the partial matroids (minus remaining options)
* `sameUpToRelabelling`: check if a permutation of B is the same as A based on relabelling; utilizes
  `relabelling`
* `any`: applies a condition to each lement in a list and returns true if there is at least one true
* `permutationsComparison`: checks if two partial matroids are the same; utilizes `any`,
  `permutation`, and `sameUpToRelabelling`
* `pruning`: sees if there are any repeats in a list of partial matroids and eliminates repeat
  partial matroids; utilizes `permutationsComparison`
* `sizeOfPrunedBucket`: gives us the length of each pruned bucket. We input matroids already
already separated by bucket to save computational power; utilizes `Pruning`
-/


instance : Mul (List (Nat → Nat)) where
  mul (l1 l2) := (l1.product l2).map (Function.uncurry Function.comp)

open Equiv in
/-- Function that generates permutations of a given magnitude (in the input)-/
def permutation : Nat → List (Nat → Nat)
  | 0 => [id]
  | n + 1 => (List.range (n + 1)).map (swapCore n) * permutation n

open Equiv in
/-- The 64 permutations of {0, 1, ... 7} which are automorphisms of the Vamos matroid. -/
def specialPermutation : List (Nat → Nat) :=
  [id, swapCore 0 1] * [id, swapCore 2 3] * [id, swapCore 4 5] * [id, swapCore 6 7]
    * [id, swapCore 0 2 ∘ swapCore 1 3] * [id, swapCore 4 6 ∘ swapCore 5 7]

/-- This allows us to relabel individual elements in a list of list of natural numbers. We have to
specify the function for relabellinging the original elements to new elements. We have to specify
the function that defines how to relabel. --/
def relabelling (A : List (List Nat)) (g : Nat → Nat) : List (List Nat) :=
  (A.map) ( fun (B : List Nat) ↦ (B.map) g)

/-- Takes in two partial matroids. The output produces a boolean. True if there are repeats.
False if not the same. When getting relabelled, the function also sorts the list and the elements of
the list. Both the lists within the lists and the natural numbers within that list are sorted.
Numbers are sorted by size. Lists are sorted by size of the first values. We sort both the
relabelled partial matroid and the partial matroid being comapred to. Only looks at one permutation
by only relabelling one partial matroid once and comparing it to the first partial matroid to see if
it is a match. The permutation is applied to the second partial matroid. It is a boolean statement
within the function. --/
def sameUpToRelabelling (A B : List (List Nat)) (g : Nat → Nat) : Bool :=
  ((relabelling B g).map List.sort).sort = (A.map List.sort).sort


/--Takes the magnitude of permutations we want to apply. Takes the partial matroids we want to apply
the permutations to. We use the any function to see if there are any repeat partial matroids. If
there are repeats, that means that thse are the same partial matroid. It compares two partial
matroids but evaluates every single permutation of the second partial matroid and compares it to the
first. --/
def permutationsComparison (n : Nat) (A B : List (List Nat)) : Bool :=
  List.any (permutation n) (sameUpToRelabelling A B)

def specialPermutationsComparison (A B : List (List Nat)) : Bool :=
  List.any specialPermutation (sameUpToRelabelling A B)

/-- Checks for any repeat partial matroids in a list of partial matroids starting with the list
of special permutations. Repeat partial matroids referring to partial matroids that are same after
evaluating permutations. We start from the end of the list of partial matroids.
If the second to last partial matroid is a permutation of the last partial matroid, we eliminate
the second to last partial matroid. If it is different, we keep it. Then we move on to the third to
last partial matroid and compare it with the partial matroids that were just analyzed and kept.
We repeat this process until we have reached the first partial matroid-/
def pruning : List PartialMatroid → List PartialMatroid
  | [] => []
  | h :: t =>
  let T := pruning t
  if (List.any (T.map PartialMatroid.matroid) (specialPermutationsComparison h.matroid)) then
    T
  else if (List.any (T.map PartialMatroid.matroid) (permutationsComparison 8 h.matroid)) then
    T
  else
    h :: T

/--NOT USED IN FINAL COMPUTATION. We begin with the list of partial matroids separated into a list
of lists and the lists are categorized by buckets. We apply the pruning to each of the buckets
based on the idea that different buckets cannot contain the same matroid because the set of
paths/connections are different. As a result, Lean would only have to check for similarities in
the buckets (reducing computational power)and prune from there. We only care about the number of
partial matroids so we want to see the length of each bucket-/
def sizeOfPrunedBucket (l : List PartialMatroid) : Nat := (pruning l).length
