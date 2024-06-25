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

-- allows us to see all the partial matroids possible when we want to add x figures
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

-- shows us the bucket each partial matroid belongs to
-- sort allows the bucket to be sorted, so that [1,2,3] is the same as [1,3,2]
-- count allows us to look at the number of figures each point touches.
def findBucket (A: PartialMatroid) : List Nat := count A.matroid.join.sort

abbrev A73Bucket := (augmentationsFinal 4 A73).map findBucket

#eval A73Bucket

abbrev A73BucketSorted := A73Bucket.sort

#eval count A73BucketSorted

#eval A73BucketSorted

#eval ((augmentationsFinal 4 A73).map findBucket)

-- shws us the number of each distinct bucket
def countBuckets (A: List PartialMatroid) : List Nat :=
   count ((A.map findBucket).sort)

#eval countBuckets (augmentationsFinal 2 A84)

-- (augmentationsFinal 4 A73) -> How many combinations of 4 triangles (3) can we make with seven points
#eval countBuckets (augmentationsFinal 4 A73)

#eval countBuckets (augmentationsFinal 5 A73)

--we sort based on bucket, and then every time the bucket changes, we create a new list
--it is ordered based on bucket, but we display the original partial matroid from which the bucket was derived
def groupByBucket (A: List PartialMatroid) : List (List PartialMatroid) :=
   groupByValue (A.mergeSort (fun l1 l2 => findBucket l1 < findBucket l2)) findBucket

#eval [[1,2,3],[1,2],[1]]

--#eval groupByBucket (augmentationsFinal 4 A73)

#eval groupByValue ((augmentationsFinal 4 A73).mergeSort (fun l1 l2 => findBucket l1 < findBucket l2)) findBucket
#eval countBuckets (augmentationsFinal 4 A73)

-- To find where a list begins and ends simply cmd + f "}]"
#eval groupByBucket (augmentationsFinal 4 A73)


-- Test with six points, 4 triangles
abbrev A63Bucket := (augmentationsFinal 4 A63).map findBucket
#eval A63Bucket

abbrev A63BucketSorted := A63Bucket.sort

#eval count A63BucketSorted

#eval A63BucketSorted

#eval groupByBucket (augmentationsFinal 4 A63)

#eval groupByBucket (augmentationsFinal 5 Vamos)

#eval countBuckets (augmentationsFinal 8 Vamos)--2
#eval countBuckets (augmentationsFinal 7 Vamos)--16
#eval countBuckets (augmentationsFinal 6 Vamos) -- 8,8,8,32
#eval countBuckets (augmentationsFinal 5 Vamos) --32,32,64
#eval countBuckets (augmentationsFinal 4 Vamos) -- 8, 8, 16, 16, 16, 32, 32, 36, 64
#eval countBuckets (augmentationsFinal 3 Vamos) --32, 32, 144
#eval countBuckets (augmentationsFinal 2 Vamos) --8, 8, 8, 16, 16, 32
#eval countBuckets (augmentationsFinal 1 Vamos) --16
#eval countBuckets (augmentationsFinal 0 Vamos) --1

abbrev Vamos7 := groupByBucket (augmentationsFinal 7 Vamos)
