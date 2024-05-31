import Matroids.NearlySame
import Mathlib.Data.List.Basic

def combinations : Nat → Nat → List (List Nat)
  | _, 0 => [[]]
  | 0, _ + 1 => []
  | n + 1, k + 1 => (combinations n (k + 1)) ++ ((combinations n k).map (· ++ [n]))

#eval combinations 5 3
-- built from `combinations 4 3` and `combinations 4 2`

#eval combinations 4 3
-- [[0, 1, 2], [0, 1, 3], [0, 2, 3], [1, 2, 3]]

#eval combinations 4 2
-- [[0, 1], [0, 2], [1, 2], [0, 3], [1, 3], [2, 3]]
-- add 4 at the end of each one
-- [[0, 1, 4], [0, 2, 4], [1, 2, 4], [0, 3, 4], [1, 3, 4], [2, 3, 4]]

/-- Every list appearing in the list-of-lists `combinations n k` has length `k`. -/
theorem combinations_entries_lengths (n k : Nat) :
    (combinations n k).all (fun l ↦ l.length = k) := by
  match n, k with
  | _, 0 => simp [combinations]
  | 0, _ + 1 => simp [combinations]
  | n + 1, k + 1 =>
    simp [combinations]
    intro l hl
    obtain hl1 | hl2 := hl
    -- Prove by strong induction
    · have H := combinations_entries_lengths n (k + 1) -- inductive hypothesis
      simp at H
      -- exact H l hl1
      apply H
      apply hl1
    · obtain ⟨l2, hl2, hl3⟩ := hl2
      rw [← hl3]
      simp
      have H := combinations_entries_lengths n k -- inductive hypothesis
      simp at H
      apply H
      apply hl2


/-- Every entry in each of the lists in `combinations n k` is less than n. -/
theorem combinations_entries_bounds (n k : Nat) :
    (combinations n k).all (fun l ↦ l.all (fun i ↦ i < n)) := by
    match n, k with
    | _, 0 => simp [combinations]
    | 0, _ + 1 => simp [combinations]
    | n + 1, k + 1 =>
      simp [combinations]
      intro l ha x h4
      obtain h1 | h2 := ha
      have H := combinations_entries_bounds n (k + 1)
      sorry
      have H := combinations_entries_bounds n k
      sorry


-- Initial list of possible combinations
abbrev A := combinations 7 3
#eval A

-- First possibility (7 Triangles): [0, 1, 2], [0, 3, 4], [1, 3, 5], [2, 4, 5], [2, 3, 6], [1, 4, 6], [0, 5, 6]
abbrev B1 := elimNearlySame [0, 1, 2] A
#eval B1
abbrev C1 :=elimNearlySame [0, 3, 4] B1
#eval C1
abbrev D1 :=elimNearlySame [1, 3, 5] C1
#eval D1
abbrev E1 :=elimNearlySame [2, 4, 5] D1
#eval E1
abbrev F1 :=elimNearlySame [2, 3, 6] E1
#eval F1
abbrev G1 :=elimNearlySame [1, 4, 6] F1
#eval G1


-- Second possibility (5 Triangles): [0, 1, 2], [4, 5, 6], [0, 3, 4], [2, 3, 6], [1, 3, 5]
abbrev B2 := elimNearlySame [0, 1, 2] A
#eval B2
abbrev C2 :=elimNearlySame [4, 5, 6] B2
#eval C2
abbrev D2 :=elimNearlySame [0, 3, 4] C2
#eval D2
abbrev E2 :=elimNearlySame [2, 3, 6] D2
#eval E2

-- Third possibility (5 Triangles): [0, 1, 2], [4, 5, 6], [2, 3, 6], [1, 3, 5], [0, 3, 4]
abbrev B3 := elimNearlySame [0, 1, 2] A
#eval B3
abbrev C3 :=elimNearlySame [4, 5, 6] B3
#eval C3
abbrev D3 :=elimNearlySame [2, 3, 6] C3
#eval D3
abbrev E3 :=elimNearlySame [1, 3, 5] D3
#eval E3

-- Fourth possibility (7 Triangles): [0, 3, 4], [0, 1, 6], [1, 4, 5], [2, 4, 6], [0, 2, 5], [3, 5, 6], [1, 2, 3]
abbrev B4 := elimNearlySame [0, 3, 4] A
#eval B4
abbrev C4 :=elimNearlySame [0, 1, 6] B4
#eval C4
abbrev D4 :=elimNearlySame [1, 4, 5] C4
#eval D4
abbrev E4 :=elimNearlySame [2, 4, 6] D4
#eval E4
abbrev F4 :=elimNearlySame [0, 2, 5] E4
#eval F4
abbrev G4 :=elimNearlySame [3, 5, 6] F4
#eval G4
