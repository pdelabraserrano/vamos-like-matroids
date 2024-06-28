import Matroids.AllPossibilities

/-! # Code to group PartialMatroids by their basic combinatorial statistics

This file provides functions to group ("bucket") sparse paving matroids by their basic combinatorial
statistics: how many vertices there are touched by one, two, three, etc. circuit-hyperplanes.

## Main definitions

* `findBucket`:
* `countBuckets`
* `groupByBucket`

-/
namespace PartialMatroid

/-- Function that shows us the bucket each partial matroid belongs to.
sort allows the bucket to be sorted, so that [1,2,3] is the same as [1,3,2]
count allows us to look at the number of figures each point touches-/
def findBucket (A: PartialMatroid) : List Nat := count A.matroid.join.sort

-- shws us the number of each distinct bucket
def countBuckets (A: List PartialMatroid) : List Nat :=
   count ((A.map findBucket).sort)

--we sort based on bucket, and then every time the bucket changes, we create a new list
--it is ordered based on bucket, but we display the original partial matroid from which the bucket was derived
def groupByBucket (A: List PartialMatroid) : List (List PartialMatroid) :=
   groupByValue (A.mergeSort (fun l1 l2 => findBucket l1 < findBucket l2)) findBucket
