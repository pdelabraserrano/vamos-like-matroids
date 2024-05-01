import Mathlib.Data.List.Sort


variable {X : Type*} [LT X] [DecidableRel ((·:X) < · )] [BEq X ]


-- Function that sorts, outside PartialMatroid namespace
def List.sort (l :  List X) : List X :=
   l.mergeSort (· < · )


#eval [0,1,3,0,2,5,1,2,3].sort

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

#eval countAux [0,0,1,1,2,2,2,3,4,5,5]
#eval countAux [1,1,1,1,1,3,3,3,3,5,5,7,7,8,9,9,9,9]

def count (l: List X) : List Nat  :=
   let (c, finishedCount) := countAux l
   (c::finishedCount).sort

#eval count [0,0,1,1,2,2,2,3,4,5,5]
