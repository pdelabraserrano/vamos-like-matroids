import Matroids.PartialMatroid
import Mathlib.Data.List.Sort
import Matroids.Count
import Init.Data.Ord


#eval [1,1,1,2,2,2,3] < [1,1,2,2,2,2]
#eval [1,1,2,2,2,2] < [2,2,2,2,2,2]

namespace PartialMatroid

/-- all the partial matroids which can be obtained by adding one triangle to the
partial matroid A -/
def augmentations (A : PartialMatroid) : List PartialMatroid := A.remainingOptions.map  (augment · A)

#eval D1
#eval augmentations D1

#check List.concat

def augmentationsTwo (A : PartialMatroid) : List PartialMatroid :=
  ((augmentations A).map augmentations).join

def augmentationsThree (A : PartialMatroid) : List PartialMatroid :=
   ((augmentations A).map augmentationsTwo).join
--

def augmentationsFour (A : PartialMatroid) : List PartialMatroid :=
   ((augmentations A).map augmentationsThree).join

def augmentationsFive (A : PartialMatroid) : List PartialMatroid :=
   ((augmentations A).map augmentationsFour).join


#eval augmentationsTwo D1
#eval augmentationsThree D1
#eval augmentationsFour D1
#eval augmentationsFive D1


def augmentationsFinal : Nat → PartialMatroid → List PartialMatroid
   | 0, A => [A]
   | n + 1, A =>
      let addNEdges : PartialMatroid → List PartialMatroid := augmentationsFinal n
      ((augmentations A).map addNEdges).join

-- def augmentationsFinal (n : Nat) (A : PartialMatroid) : List PartialMatroid :=
--    match n, A with
--    | 0, A => [A]
--    | n + 1, A =>
--       let addNEdges : PartialMatroid → List PartialMatroid := augmentationsFinal n
--       ((augmentations A).map addNEdges).join

#eval (augmentationsFinal 3 E1)
-- #eval augmentationsFour D1
#eval (augmentationsFinal 4 A73)

#eval (augmentationsFinal 4 A63)

#eval (augmentationsFinal 4 A73)

#eval (augmentationsFinal 2 A84).length

#eval (augmentationsFinal 4 A63)


#eval D1.matroid.join

def fact : Nat → Nat
   | 0 => 1
   |n + 1 => (n +1)* fact n
#eval fact 7

-- countBuckets does the same thing we did here, in a single function
def findBucket (A: PartialMatroid) : List Nat := count A.matroid.join.sort

abbrev A73Bucket := (augmentationsFinal 4 A73).map findBucket

#eval A73Bucket

abbrev A73BucketSorted := A73Bucket.sort

#eval count A73BucketSorted

#eval A73BucketSorted

#eval ((augmentationsFinal 4 A73).map findBucket)

def countBuckets (A: List PartialMatroid) : List Nat :=
   count ((A.map findBucket).sort)

#eval countBuckets (augmentationsFinal 2 A84)

-- (augmentationsFinal 4 A73) -> How many combinations of 4 triangles (3) can we make with seven points
#eval countBuckets (augmentationsFinal 4 A73)

#eval countBuckets (augmentationsFinal 5 A73)

def groupByBucket (A: List PartialMatroid) : List (List PartialMatroid) :=
   groupByValue (A.mergeSort (fun l1 l2 => findBucket l1 < findBucket l2)) findBucket

-- A.sort((A.map findBucket).sort)


-- def list_length (l : List Nat) : List Nat :=
--   count l.sort

-- def compare_lists_by_length : List Nat → List Nat → Ordering
-- | l1, l2 =>
--   if list_length l1 < list_length l2 then Ordering.lt
--   else if list_length l1 = list_length l2 then Ordering.eq
--   else Ordering.gt

-- def sort_lists_by_length (l : List (List ℕat)) : List (List Nat) :=
--   list.sort (λ l1 l2↦ compare_lists_by_length l1 l2) l

#eval [[1,2,3],[1,2],[1]]

--#eval groupByBucket (augmentationsFinal 4 A73)

#eval groupByValue ((augmentationsFinal 4 A73).mergeSort (fun l1 l2 => findBucket l1 < findBucket l2)) findBucket
#eval countBuckets (augmentationsFinal 4 A73)

#eval groupByBucket (augmentationsFinal 4 A73)
