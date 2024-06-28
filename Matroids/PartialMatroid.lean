import Matroids.NearlySame

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

/--Adds an additional figure to the partial matroid and then eliminates any figure/option from the
remaining options that share all or all but one point with the figure that was just added -/
def augment (l : List Nat) (M : PartialMatroid) : PartialMatroid :=
  -- if !(l ∈ M.remainingOptions) then fail "can't add this" else
  { matroid := l :: M.matroid, remainingOptions := elimSmaller l (elimNearlySame l M.remainingOptions) }

-- old version with duplication
  -- { matroid := l :: M.matroid, remainingOptions := elimNearlySame l M.remainingOptions }
