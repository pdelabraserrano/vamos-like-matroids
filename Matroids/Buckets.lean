import Matroids.PartialMatroid
import Matroids.Count

/-! # Code to group PartialMatroids by their basic combinatorial statistics

This file provides functions to group ("bucket") sparse paving matroids by their basic combinatorial
statistics: how many vertices there are touched by one, two, three, etc. circuit-hyperplanes.

## Main definitions

* `findBucket`: counts the number of figures touched by each point and sorts them (by counting how
   many times each point appears)
* `countBuckets`: counts the number of distinct `findBucket` combos (sorted)
* `groupByBucket`: allows us to sort partial matroids by their distinct bucket (i.e. category bucket
   1, bucket 2, etc.); utilizes `groupByValue` and `findBucket`
-/

namespace PartialMatroid

/-- Function that shows us the bucket each partial matroid belongs to.
sort allows the bucket to be sorted, so that [1,2,3] is the same as [1,3,2]
count allows us to look at the number of figures each point touches-/
def findBucket (A: PartialMatroid) : List Nat := count A.matroid.join.sort

/-- We sort based on bucket, and then every time the bucket changes, we create a new list. It is
ordered based on bucket, but we display the original partial matroid from which the bucket was
derived. -/
def groupByBucket (A: List PartialMatroid) : List (List PartialMatroid) :=
   groupByValue (A.mergeSort (fun l1 l2 => findBucket l1 < findBucket l2)) findBucket

/-- NOT USED IN FINAL COMPUTATION. Shows us the number of each distinct bucket. -/
def countBuckets (A: List PartialMatroid) : List Nat :=
   count ((A.map findBucket).sort)

def List.pairs : List α → List (List α)
  /- All elements of the empty list are vacuously pairwise related. -/
  | [] => []
  /- `a :: l` is `Pairwise R` if `a` `R`-relates to every element of `l`,
  and `l` is `Pairwise R`. -/
  | a :: l => (l.map fun b ↦ [a, b]) ++ pairs l
