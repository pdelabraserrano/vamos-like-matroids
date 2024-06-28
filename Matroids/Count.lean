import Mathlib.Data.List.Sort

variable {X : Type*} [LT X] [DecidableRel ((·:X) < · )] [BEq X ]

-- Function that sorts, outside PartialMatroid namespace
def List.sort (l :  List X) : List X :=
   l.mergeSort (· < · )


-- Function to count the number of ocurrences of a specific numbre in a sorted list
def countAux : List X → Nat × List Nat
   | [] => (0, []) -- check
   | [_] => (1, []) -- check
   | a :: b :: t =>
      let (c, finishedCount) := countAux (b :: t)
      if a == b then
         ((c + 1), finishedCount)
      else
         (1, c :: finishedCount)


def count (l: List X) : List Nat  :=
   let (c, finishedCount) := countAux l
   (c::finishedCount).sort


def groupByValueAux (f: PartialMatroid → X) : List PartialMatroid → (List PartialMatroid) × List (List PartialMatroid)
   | [] => ([], []) -- check
   | [pm] => ([pm], []) -- check
   | a :: b :: t =>
      let (c, finishedCount) := groupByValueAux f (b :: t)
      if f a == f b then
         (a :: c, finishedCount)
      else
         ([a], c :: finishedCount)


def groupByValue (l: List PartialMatroid) (f: PartialMatroid → X): List (List PartialMatroid) :=
   let (c, finishedCount) := groupByValueAux f l
   (c::finishedCount)
