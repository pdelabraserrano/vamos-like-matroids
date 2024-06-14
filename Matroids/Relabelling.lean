import Matroids.PartialMatroid
import Matroids.Count
--import data.char
import Init.Prelude
-- import tactic.rename_var
import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.GroupTheory.Perm.Cycle.Concrete



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

--this allows us to map individual elements in a list of list of natural numbers
--we have to specify the function for mapping the original elements to new elements
--we have to specify the function to which we want to relabel
def relabelling (A : List (List Nat)) (g : Nat → Nat) : List (List Nat) :=
  (A.map) ( fun (B : List Nat) ↦ (B.map) g)


#eval relabelling [[1,2,3],[4,5,6]] (· + 1)

--we use the relabelling function earlier and specify the function perm
--perm is already an established function
--perm is used to find all the permutations starting from 0 to n-1
--relabeling by perm allows us to find all the combbinations of permutations
def relabellingByPerm (A : List (List Nat)) (g : Perm (Fin 8)) :  List (List Nat) :=
  relabelling A (convertToNatFunction g)

#check relabellingByPerm [[1,2,3,4,5,6,7,8]]
--#eval c[(1 : Fin 8), 2, 3]
#eval relabellingByPerm [[0,2,3],[0,4,6],[1,2,7]] c[0,1,2]
#eval (relabellingByPerm [[0,2,3],[0,4,6],[1,2,7]] c[0,1,2]).map List.sort
#eval ((relabellingByPerm [[0,2,3],[0,4,6],[1,2,7]] c[0,1,2]).map List.sort).sort

--produces a boolean
--true if there are repeats
--?should stop if it finds a true?
--false if there are none
--when getting relabelled, the function also sorts the list and the elements of the list
--because the original partial matroids are sorted from least to greatest
--both the lists within the lists and the natural numbers within that list are sorted
--it is a boolean statemen within the function
def sameUpToRelabelling (A B : PartialMatroid) (g : Perm (Fin 8)) : Bool :=
  ((relabellingByPerm B.matroid g).map List.sort).sort = A.matroid

#eval Nat.factorial 2
#eval @Finset.univ (Perm (Fin 2)) _

--#eval paa vamos @Finset.univ (Perm (Fin 8)) _

def permutationsComparison (A B : PartialMatroid) : Bool :=
  | [A.matroid.join], [] => (false)
  | [A.matroid.join], [(relabellingByPerm B.matroid).join] =>
      if A.matroid.join = (relabellingByPerm B.matroid).join then
        (true)
      else
        sameUpToRelabelling A, B

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
