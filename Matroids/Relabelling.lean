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


variable  (A : List (List Nat))
#check List.map _ A

/-- This allows us to relabel individual elements in a list of list of natural numbers. We have to
specify the function for relabellinging the original elements to new elements. We have to specify
the function that defines how to relabel. --/
def relabelling (A : List (List Nat)) (g : Nat → Nat) : List (List Nat) :=
  (A.map) ( fun (B : List Nat) ↦ (B.map) g)


/-- Takes in two partial matroids. The output produces a boolean. True if there are repeats.
False if not the same. When getting relabelled, the function also sorts the list and the elements of
the list. Both the lists within the lists and the natural numbers within that list are sorted.
Numbers are sorted by size. Lists are sorted by size of the first values. We sort both the
relabelled partial matroid and the partial matroid being comapred to. Only looks at one permutation
by only relabelling one partial matroid once and comparing it to the first partial matroid to see if
it is a match. The permutation is applied to the second partial matroid. It is a boolean statement
within the function. --/
def sameUpToRelabelling (A B : PartialMatroid) (g : Nat → Nat) : Bool :=
  ((relabelling B.matroid g).map List.sort).sort = ((A.matroid).map List.sort).sort

/--Takes a list of elements. Evaluates the list of elements and compares each element to a
condition and creates a list of booleans. Fulfilling the condition would give a true, not fulfilling
would give a false. If any of the elements contains a true boolean, then it returns true. If there
are no true booleans, then it returns false--/
def any : List α -> (α → Bool) -> Bool
  | [], _ => false
  | h :: t, p => p h || any t p

/--Takes the number of permutes we want to permutate. Takes the partial matroids we want to apply
the permutations to. We use the any function to see if there are any repeat partial matroids. If
there are repeats, that means that thse are the same partial matroid. It compares two partial
matroids but evaluates every single permutation of the second partial matroid and compares it to the
first. --/
def permutationsComparison (n : Nat) (A B : PartialMatroid) : Bool :=
  any (permutation n) (sameUpToRelabelling A B)

/-- checks for any repeat partial matroids in a list of partial matroids. Repeat partial matroids
referring to partial matroids that are same after evaluating permutations. We start from the end of
the list of partial matroids. If the second to last partial matroid is a permutation of the last
partial matroid, we eliminate the second to last partial matroid. If it is different, we keep it.
Then we move on to the third to last partial matroid and compare it with the partial matroids that
were just analyzed and kept. We repeat this process until we have reached the first partial
matroid-/
def pruning : List PartialMatroid → List PartialMatroid
  | [] => []
  | h :: t => let T := pruning t
  if (any (T) (permutationsComparison 8 h)) then
    T
  else
    h :: T

def sizeOfPrunedBucket (l : List PartialMatroid) : Nat := (pruning l).length
