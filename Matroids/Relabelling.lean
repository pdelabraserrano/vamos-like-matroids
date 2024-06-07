import Matroids.PartialMatroid
--import data.char
import Init.Prelude
-- import tactic.rename_var
import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Perm



open Equiv

#check Perm (Fin 8)
--#eval @Finset.univ (Perm (Fin 3)) _
def convertToNatFunction (p : Perm (Fin 8)) (i : Nat) : Nat :=
  if h : i < 8 then
    p ⟨i, h⟩
  else
    i

variable  (A : List (List Nat))
#check List.map _ A

def relabelling (A : List (List Nat)) (g : Nat → Nat) : List (List Nat) :=
  (A.map) ( fun (B : List Nat) ↦ (B.map) g)


#eval relabelling [[1,2,3],[4,5,6]] (· + 1)


def relabellingByPerm (A : List (List Nat)) (g : Perm (Fin 8)) :  List (List Nat) :=
  relabelling A (convertToNatFunction g)

def sameUpToRelabelling (A B : PartialMatroid) (g : Perm (Fin 8)) : Bool :=
  sorry
 -- Take the B and relabel it using relabellingByPerm function and permutation g
 -- Sorting (which one?)
 -- See if it agrees with A (true if it agrees, false if it does not)

-- i.e. function f swaps 1 to 0 and leaves everything else the same
-- A: [[1,2,3],[4,5,6]]
-- Output: [[0,2,3],[4,5,6]]

--i.e. suppose function adds one to everything and 6 goes to 0, function f
-- A: same as earlier
-- Output: [[2,3,4],[5,6,0]]

-- What we want
-- a function that takes in two partial matroids (A, B of type partial matroid)
-- output should be a boolean

def addOne : List Nat → List Nat
  | [] => []
  | head :: tail =>
    (head + 96) :: addOne (tail)
