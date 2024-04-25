import Matroids.MatroidComputations

structure PartialMatroid where
  matroid : List (List Nat)
  remainingOptions : List (List Nat)
  deriving Repr

namespace PartialMatroid

def elimSmaller (l : List Nat) : List (List Nat) → List (List Nat)
  | [] => []
  | h1 :: t1 =>
    if h1 > l then
      elimSmaller l t1
    else
      h1 :: elimSmaller l t1

-- eventually we want to make this fail if l does not belong to remainingOptions
def augment (l : List Nat) (M : PartialMatroid) : PartialMatroid :=
  -- if !(l ∈ M.remainingOptions) then fail "can't add this" else
  { matroid := l :: M.matroid, remainingOptions := elimSmaller l (elimNearlySame l M.remainingOptions) }

-- old version with duplication
  -- { matroid := l :: M.matroid, remainingOptions := elimNearlySame l M.remainingOptions }


-- Initial list of possible combinations
abbrev A73 : PartialMatroid where
  matroid := []
  remainingOptions := combinations 7 3

#eval A73

abbrev A53 : PartialMatroid where
  matroid := []
  remainingOptions := combinations 5 3

abbrev A63 : PartialMatroid where
  matroid := []
  remainingOptions := combinations 6 3

abbrev A74 : PartialMatroid where
  matroid := []
  remainingOptions := combinations 7 4

abbrev A84 : PartialMatroid where
  matroid := []
  remainingOptions := combinations 8 4

abbrev B1 : PartialMatroid := augment [0, 1, 2] A73
abbrev C1 : PartialMatroid := augment [0, 3, 4] B1
abbrev D1 : PartialMatroid := augment [1, 3, 5] C1
abbrev E1 := augment [2, 4, 5] D1

#eval E1
#eval augment [2, 3, 6] E1
#eval D1
#eval D1.remainingOptions
#eval D1.remainingOptions.map (augment · D1)


#eval [1, 0, 2] < [1, 0, 3]
#eval [3, 4, 5] < [3, 5, 6]
