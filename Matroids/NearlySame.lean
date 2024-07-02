
/-! # Code to ---

This file provides functions to identify within a list of list of natural numbers whether or not
there is a list of natural numbers with

## Main definitions

* `NearlySameAux`: checks if there is more than one different element between two lists.
* `NearlySame`: returns a boolean on whether or not there is more than one different element between
two lists
* `elimNearlySame`: Looks at a list of lists of natural numbers and see if there are any existing
lists in the list of lists that has at most one different element between them and eliminates items
from the list of lists that have a most one different element between it and the new list.
-/

/-- Check if two ordered lists of the same length differ by at most one entry-/
def NearlySameAux : List Nat → List Nat → (Bool × Bool × Bool)
  | [], [] => (true, false, false)
  | [], [_] => (true, false, true)
  | [], _ :: _ :: _ => (false, false, true)
  | [_], [] => (true, true, false)
  | _ :: _ :: _, [] => (false, true, false)
  | h1 :: t1, h2 :: t2 =>
    if h1 = h2 then
      NearlySameAux t1 t2
    else
      if h1 < h2 then
        let (b, leftFreePassUsed,  rightFreePassUsed) :=
          NearlySameAux t1 (h2::t2)
        if (leftFreePassUsed == true) then
          (false, true, rightFreePassUsed)
        else
          (b, true,  rightFreePassUsed)
      else -- h1 > h2
        -- use the right free pass
        let (b, leftFreePassUsed,  rightFreePassUsed) :=
          NearlySameAux (h1 :: t1) t2
        if (rightFreePassUsed == true) then
          (false, leftFreePassUsed, true)
        else
          (b, leftFreePassUsed,  true)


def NearlySame : List Nat → List Nat → Bool
  | l1, l2 =>
    let (a, _, _) := NearlySameAux l1 l2
    a

def elimNearlySame (l : List Nat) : List (List Nat) → List (List Nat)
  | [] => []
  | h1 :: t1 =>
    if (NearlySame l h1) then
      elimNearlySame l t1
    else
      h1 :: elimNearlySame l t1
