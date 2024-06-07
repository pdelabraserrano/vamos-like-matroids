import Matroids.PartialMatroid
--import data.char
import Init.Prelude
-- import tactic.rename_var

variable  (A : List (List Nat))
#check List.map _ A



def relabelling (A : List (List Nat)) (g : Nat → Nat) : List (List Nat) :=
  (A.map) ( fun (B : List Nat) ↦ (B.map) g)


#eval relabelling [[1,2,3],[4,5,6]] (· + 1)


-- i.e. function f swaps 1 to 0 and leaves everything else the same
-- A: [[1,2,3],[4,5,6]]
-- Output: [[0,2,3],[4,5,6]]

--i.e. suppose function adds one to everything and 6 goes to 0, function f
-- A: same as earlier
-- Output: [[2,3,4],[5,6,0]]


def addOne : List Nat → List Nat
  | [] => []
  | head :: tail =>
    (head + 96) :: addOne (tail)
