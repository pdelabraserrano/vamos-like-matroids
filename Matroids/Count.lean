import Mathlib.Data.List.Sort
import Mathlib.Data.List.Lex

variable {X : Type*} [LT X] [DecidableRel ((·:X) < · )] [BEq X ]

/-! # Code to ---

This file provides functions that provides the framework to find and group by buckets later on.
`count` makes sure that we can identify buckets, `List.sort` makes sure that we do not put the same bucket
into different categories because the quantity of different elements appears in different orders.
`groupByValue

## Main definitions

* `List.sort`: allows us to sort a list based on the magnitude of the first elements. The list with
that contains a larger number earliest in the list is considered greater.
* `countAux`: counts the number of times each element appears in a list
* `count`: sorts the list that contains the number of times each element appears in a list. That
way, [1,2,3] is the same as [3,2,1]. It does not matter the order or the type of elements that
appear, but rather the frequency of different elements. Utilizes `countAux`
* `groupByValueAux`: allows us to categorize partial matroids by similar characteristics.
* `groupByValue`: it allows us to group. Primary purpose is to group partial matroids by buckets the
`count` function returns. Buckets are important because they represent different sets of paths/
connections.
-/

/-- Function that sorts, outside PartialMatroid namespace. It will sort lists by dtermining which
list is greater. Its criteria for determining the greater list is whichever list generates a greater
number first-/
def List.sort (l :  List X) : List X :=
   l.mergeSort (· < · )


/-- Function to count the number of ocurrences of a specific elements in a sorted list. We first
sort the list. Then we count the number of consecutive things that occur. Once something different
from the last item pops up, we start a new count. -/
def countAux : List X → Nat × List Nat
   | [] => (0, []) -- check
   | [_] => (1, []) -- check
   | a :: b :: t =>
      let (c, finishedCount) := countAux (b :: t)
      if a == b then
         ((c + 1), finishedCount)
      else
         (1, c :: finishedCount)

/--It sorts the counted appearance of each element. That way, it is not differentiated by the
permutations of elements that get counted but rather by the quantity of different elements. -/
def count (l: List X) : List Nat  :=
   let (c, finishedCount) := countAux l
   (c::finishedCount).sort

/--sorts a series of partial matroids (with the same original partial matroid and remaining options)
by their characteristic obtained from running them through a mapping function. It sorts it by
looking for partial matroids that returns the same value through the function and puts them into
a list. If another partial matroid returns a different vlue through the function, then a new list is
created-/
def groupByValueAux (f: PartialMatroid → X) : List PartialMatroid → (List PartialMatroid) × List (List PartialMatroid)
   | [] => ([], []) -- check
   | [pm] => ([pm], []) -- check
   | a :: b :: t =>
      let (c, finishedCount) := groupByValueAux f (b :: t)
      if f a == f b then
         (a :: c, finishedCount)
      else
         ([a], c :: finishedCount)


/--Puts the list differentiated by category togethr into a list of lists. In the end, it becomes
a list of list of partil matroids. -/
def groupByValue (l: List PartialMatroid) (f: PartialMatroid → X): List (List PartialMatroid) :=
   let (c, finishedCount) := groupByValueAux f l
   (c::finishedCount)
