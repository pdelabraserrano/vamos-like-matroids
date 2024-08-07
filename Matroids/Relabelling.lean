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
* `Any`: applies a condition to each lement in a list and returns true if there is at least one true
* `permutationsComparison`: checks if two partial matroids are the same; utilizes `any`,
  `permutation`, and `sameUpToRelabelling`
* `Pruning`: sees if there are any repeats in a list of partial matroids and eliminates repeat
  partial matroids; utilizes `permutationsComparison`
* `sizeOfPrunedBucket`: gives us the length of each pruned bucket. We input matroids already
already separated by bucket to save computational power; utilizes `Pruning`
-/


/-- Function that generates permutations of a given magnitude (in the input)-/
def permutation : Nat → List (Nat → Nat)
  | 0 => [id]
  | n + 1 => ((List.range (n + 1)).map (fun i => (permutation n).map (Function.comp (Equiv.swapCore i n)))).join

open Equiv in
def specialPermutation : List (Nat → Nat) :=
  let c (l1 l2 : List (Nat → Nat)) : List (Nat → Nat) := (l1.product l2).map (fun (a, b) ↦ a ∘ b)
  c (c (c (c (c [id, swap 0 1] [id, swap 2 3]) [id, swap 4 5]) [id, swap 6 7]) [id, swap 0 2 ∘ swap 1 3]) [id, swap 4 6 ∘ swap 5 7]

#eval specialPermutation.map (fun f ↦ (List.range 8).map (fun i ↦ f i)) |>.length

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

/--Takes a list of elements. Evaluates the list of elements and compares each element to a
condition and creates a list of booleans. Fulfilling the condition would give a true, not fulfilling
would give a false. If any of the elements contains a true boolean, then it returns true. If there
are no true booleans, then it returns false--/
def any : List α -> (α → Bool) -> Bool
  | [], _ => false
  | h :: t, p => p h || any t p

def specialPermutationsComparison (A B : List (List Nat)) : Bool :=
  any specialPermutation (sameUpToRelabelling A B)

/--Takes the magnitude of permutations we want to apply. Takes the partial matroids we want to apply
the permutations to. We use the any function to see if there are any repeat partial matroids. If
there are repeats, that means that thse are the same partial matroid. It compares two partial
matroids but evaluates every single permutation of the second partial matroid and compares it to the
first. --/
def permutationsComparison (n : Nat) (A B : List (List Nat)) : Bool :=
  any (permutation n) (sameUpToRelabelling A B)

/-- checks for any repeat partial matroids in a list of partial matroids. Repeat partial matroids
referring to partial matroids that are same after evaluating permutations. We start from the end of
the list of partial matroids. If the second to last partial matroid is a permutation of the last
partial matroid, we eliminate the second to last partial matroid. If it is different, we keep it.
Then we move on to the third to last partial matroid and compare it with the partial matroids that
were just analyzed and kept. We repeat this process until we have reached the first partial
matroid-/
def pruning : List PartialMatroid → List PartialMatroid
  | [] => []
  | h :: t =>
  let T := pruning t
  if (any (T.map PartialMatroid.matroid) (specialPermutationsComparison h.matroid)) then
    T
  else if (any (T.map PartialMatroid.matroid) (permutationsComparison 8 h.matroid)) then
    T
  else
    h :: T

/--we begin with the list of partial matroids separated into a list of lists and the lists are
categorized by buckets. We apply the pruning to each of the buckets based on the idea that different
buckets cannot contain the same matroid because the set of paths/connections are different. As a
result, Lean would only have to check for similarities in the buckets (reducing computational power)
and prune from there. We only care about the number of partial matroids so we want to see the length
of each bucket-/
def sizeOfPrunedBucket (l : List PartialMatroid) : Nat := (pruning l).length
