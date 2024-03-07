import Matroids.MatroidComputations

structure PartialMatroid where
  matroid : List (List Nat)
  remainingOptions : List (List Nat)
  deriving Repr

namespace PartialMatroid

-- eventually we want to make this fail if l does not belong to remainingOptions
def augment (l : List Nat) (M : PartialMatroid) : PartialMatroid :=
  -- if !(l ∈ M.remainingOptions) then fail "can't add this" else
  { matroid := l :: M.matroid, remainingOptions := elimNearlySame l M.remainingOptions }


-- Initial list of possible combinations
abbrev A : PartialMatroid where
  matroid := []
  remainingOptions := combinations 7 3


#eval A

abbrev B1 : PartialMatroid := augment [0, 1, 2] A
abbrev C1 : PartialMatroid := augment [0, 3, 4] B1
abbrev D1 : PartialMatroid := augment [1, 3, 5] C1
abbrev E1 := augment [2, 4, 5] D1

#eval D1
#eval D1.remainingOptions
#eval D1.remainingOptions.map (augment · D1)
