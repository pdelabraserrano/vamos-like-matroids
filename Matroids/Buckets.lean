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

def List.pairs : List α → List (List α)
  /- All elements of the empty list are vacuously pairwise related. -/
  | [] => []
  /- `a :: l` is `Pairwise R` if `a` `R`-relates to every element of `l`,
  and `l` is `Pairwise R`. -/
  | a :: l => (l.map fun b ↦ [a, b]) ++ pairs l

/-- The use of sort allows the bucket to be sorted, so that [1,2,3] is the same as [1,3,2]
count allows us to look at the number of figures each point touches -/
def invariant1 (A: PartialMatroid) : List Nat := count A.matroid.join.sort

/-- Takes in ****** and gives out a list of all the possible pairs
 of natural numbers in it-/
def renameMe (A: List (List Nat)) : List Nat := count (((((A.map)) (List.pairs)).join).sort)

/-- Takes in the matroid part of a partial matroid and gives out a list of all the possible pairs
 of natural numbers in it-/
def invariant2 (A: PartialMatroid) : List Nat := renameMe A.matroid

def isMember (i : Nat) : (List Nat) → Bool
  | [] => false
  | h :: t =>
    if i == h then true
    else
    isMember i t

def complementAux  (l₁ : List Nat) : List Nat → List Nat
  | [] => []
  | h :: t =>
    if isMember h l₁ then
      complementAux l₁ t
    else
      h :: complementAux l₁ t

def complement ( A : List (List Nat) ) : List (List Nat) :=
  A.map (complementAux · [0,1,2,3,4,5,6,7])


/-- Takes in the matroid part of a partial matroid and gives out a list of all the possible pairs
 of natural numbers in it-/
def invariant3 (A: PartialMatroid) : List Nat := renameMe (complement A.matroid)

/-- NEED TO WRITE -/
def groupByFirstInvariant (A: List PartialMatroid) : List (List PartialMatroid) :=
   groupByValue (A.mergeSort (fun l1 l2 => invariant1 l1 < invariant1 l2)) invariant1

/-- NEED TO WRITE -/
def groupBySecondInvariant (A: List PartialMatroid) : List (List PartialMatroid) :=
   groupByValue (A.mergeSort (fun l1 l2 => invariant2 l1 < invariant2 l2)) invariant2

def groupByThirdInvariant (A: List PartialMatroid) : List (List PartialMatroid) :=
   groupByValue (A.mergeSort (fun l1 l2 => invariant3 l1 < invariant3 l2)) invariant3

/-Function that shows us the bucket each partial matroid belongs to by applying `invariant1`
followed by `invariant2`-/
def groupByBucket (A: List PartialMatroid) : List (List PartialMatroid) :=
   (((((groupByFirstInvariant A).map) (groupBySecondInvariant)).join).map (groupByThirdInvariant)).join

/-- NOT USED IN FINAL COMPUTATION. Shows us the number of each distinct bucket. -/
def countBuckets (A: List PartialMatroid) : List Nat :=
   (groupByBucket A).map (List.length)
