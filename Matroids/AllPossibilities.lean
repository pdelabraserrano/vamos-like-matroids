import Matroids.PartialMatroid
import Mathlib.Data.List.Sort
import Matroids.Count
import Init.Data.Ord

namespace PartialMatroid

/-- all the partial matroids which can be obtained by adding one triangle to the
partial matroid A -/
def augmentations (A : PartialMatroid) : List PartialMatroid := A.remainingOptions.map  (augment · A)


#check List.concat

def augmentationsTwo (A : PartialMatroid) : List PartialMatroid :=
  ((augmentations A).map augmentations).join

def augmentationsThree (A : PartialMatroid) : List PartialMatroid :=
   ((augmentations A).map augmentationsTwo).join

def augmentationsFour (A : PartialMatroid) : List PartialMatroid :=
   ((augmentations A).map augmentationsThree).join

def augmentationsFive (A : PartialMatroid) : List PartialMatroid :=
   ((augmentations A).map augmentationsFour).join


-- Function that allows us to see all the partial matroids possible when we want to add x figures
def augmentationsFinal : Nat → PartialMatroid → List PartialMatroid
   | 0, A => [A]
   | n + 1, A =>
      let addNEdges : PartialMatroid → List PartialMatroid := augmentationsFinal n
      ((augmentations A).map addNEdges).join


/-- Function that calculates the factorial of a given number-/
def fact : Nat → Nat
   | 0 => 1
   |n + 1 => (n +1)* fact n


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
