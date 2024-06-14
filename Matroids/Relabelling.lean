import Matroids.PartialMatroid
import Matroids.Count
--import data.char
import Init.Prelude
-- import tactic.rename_var
import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.Logic.Equiv.Basic
import Mathlib.Util.Time

def permutation : Nat → List (Nat → Nat)
  | 0 => [id]
  | n + 1 => ((List.range (n + 1)).map (fun i => (permutation n).map (Function.comp (Equiv.swapCore i n)))).join

#eval (permutation 3).map (fun f ↦ (List.range 3).map f)
#eval (List.range 8).map (permutation 8).head!

#check List.all

def all : List α → (α → Bool) → Bool
  | [], _ => true
  | h :: t, p => p h && all t p



def Even' (N : Nat) : Bool :=
  N % 2 == 0

#eval all [0, 2, 10] Even'


open Equiv

#check Perm (Fin 8)
--#eval @Finset.univ (Perm (Fin 3)) _



variable  (A : List (List Nat))
#check List.map _ A

--this allows us to map individual elements in a list of list of natural numbers
--we have to specify the function for mapping the original elements to new elements
--we have to specify the function to which we want to relabel
def relabelling (A : List (List Nat)) (g : Nat → Nat) : List (List Nat) :=
  (A.map) ( fun (B : List Nat) ↦ (B.map) g)


#eval relabelling [[1,2,3],[4,5,6]] (· + 1)





--produces a boolean
--true if there are repeats
--false if not the same
--when getting relabelled, the function also sorts the list and the elements of the list
--because the original partial matroids are sorted from least to greatest
--both the lists within the lists and the natural numbers within that list are sorted
--only looks at one permutation
--it is a boolean statemen within the function
def sameUpToRelabelling (A B : PartialMatroid) (g : Nat → Nat) : Bool :=
  ((relabelling B.matroid g).map List.sort).sort = A.matroid

#eval Nat.factorial 2
#eval @Finset.univ (Perm (Fin 2)) _
#eval (permutation 8).head! 0

#eval sameUpToRelabelling PartialMatroid.paa PartialMatroid.Vamos (permutation 8).head!

def any : List α -> (α → Bool) -> Bool
  | [], _ => false
  | h :: t, p => p h || any t p

def permutationsComparison (n : Nat) (A B : PartialMatroid) : Bool :=
  any (permutation n) (sameUpToRelabelling A B)

abbrev pa1 : PartialMatroid where
  matroid:= [[0,1,2],[1,2,3]]
  remainingOptions := []

abbrev pa2 : PartialMatroid where
  matroid:= [[0,2,3],[1,2,3]]
  remainingOptions := []

#eval permutationsComparison 4 pa1 pa2

--#time
-- #eval permutationsComparison 8 PartialMatroid.paa PartialMatroid.Vamos

def pruning : List PartialMatroid → List PartialMatroid
  | [] => sorry
  | h :: t => sorry
  --use permutationsComparison

def pruning' (A : List PartialMatroid) : List PartialMatroid :=
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
