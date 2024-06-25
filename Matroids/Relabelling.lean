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
  | [] => []
  | h :: t =>
  if (permutationsComparison 8 h (t.head)) then pruning t
  else h :: pruning t
