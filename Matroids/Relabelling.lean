import Matroids.PartialMatroid
import Matroids.Count
import Init.Prelude
import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.Logic.Equiv.Basic
import Mathlib.Util.Time

-- Function that generates permutations of a list
def permutation : Nat → List (Nat → Nat)
  | 0 => [id]
  | n + 1 => ((List.range (n + 1)).map (fun i => (permutation n).map (Function.comp (Equiv.swapCore i n)))).join

#check List.all

def all : List α → (α → Bool) → Bool
  | [], _ => true
  | h :: t, p => p h && all t p


def Even' (N : Nat) : Bool :=
  N % 2 == 0


open Equiv

#check Perm (Fin 8)
--#eval @Finset.univ (Perm (Fin 3)) _

variable  (A : List (List Nat))
#check List.map _ A

/-- Function that allows us to map individual elements in a list of list of natural numbers.
We have to specify the function for mapping the original elements to new elements and the
function to which we want to relabel-/
def relabelling (A : List (List Nat)) (g : Nat → Nat) : List (List Nat) :=
  (A.map) ( fun (B : List Nat) ↦ (B.map) g)


/-- Function that produces a boolean. True if there are repeats & false if not the same.
When getting relabelled, the function also sorts the list and the elements of the list
(because the original partial matroids are sorted from least to greatest).
Both the lists within the lists and the natural numbers within that list are sorted.
The function only looks at one permutation. It is a boolean statemen within the function-/
def sameUpToRelabelling (A B : PartialMatroid) (g : Nat → Nat) : Bool :=
  ((relabelling B.matroid g).map List.sort).sort = A.matroid


def any : List α -> (α → Bool) -> Bool
  | [], _ => false
  | h :: t, p => p h || any t p

def permutationsComparison (n : Nat) (A B : PartialMatroid) : Bool :=
  any (permutation n) (sameUpToRelabelling A B)


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
