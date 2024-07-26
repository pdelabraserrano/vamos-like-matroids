import Mathlib.Data.List.Basic
import Mathlib.Data.List.Sort
import Mathlib.Data.Matrix.Notation

example : ∃ x y : ℤ, x ≥ y ∧ y ≥ x := by
  use 10
  use 10

example : ¬ ∀ x y : ℤ, x = y ∨ y = x := by
  push_neg
  use 10
  use 9
  constructor
  decide
  decide

example : ¬∀ x y : ℕ, y = x + 1 ∨ x = y + 1 := by
  push_neg
  use 3, 5
  constructor
  decide
  decide

example : ∀ x y : ℕ, True ∨ True := by
  intro _ _
  right
  decide

example : ∀ x y : ℕ, x - y ≥ 0 ∨ y - x ≥ 0 := by
  intro i j
  by_cases a : i ≥ j
  · left
    calc
      i - j ≥ i - i := by rel[a]
      _ = 0 := by norm_num
  · push_neg at a
    right
    calc
      j - i ≥ j - j := by rel[a]
      _ = 0 := by norm_num
