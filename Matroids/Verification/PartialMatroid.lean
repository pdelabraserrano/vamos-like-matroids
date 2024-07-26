import Matroids.PartialMatroid
import Matroids.Verification.Basic
import Matroids.Verification.Miscellaneous

open PartialMatroid List

-- two ways of phrasing the same thing:
-- 1) Forall (fun a ↦ a < n) l
-- 2) ∀ a ∈ l, a < n

/-
P₀ is [0, 1]
P₁ is [2, 3]
P₂ is [4, 5]
P₃ is [6, 7]

vamosLike means:
out of the (i, j) possibilities with i < j, i.e.
01
02
03
12
13
23
it is true that Pᵢⱼ is in l, except for ij = 23

(the other (i, j) possibilities like
00
10
11
20
21
etc
are ruled out)
-/
lemma augment_normalized (l : List Nat) (A : PartialMatroid)
    (hA : List.NormalizedVamosLike A.matroid)
    (hL : ¬ l = ([4,5,6,7])) :
    List.NormalizedVamosLike (augment l A).matroid := by
  unfold NormalizedVamosLike
  intro P i j
  fin_cases i <;> fin_cases j
  · simp (config := {decide := true})
  · -- i = 0, j = 1
    unfold augment
    simp (config := {decide := true})
    have h := hA 0 1
    simp (config := {decide := true}) at h
    apply List.mem_mergeSort
    simp
    right
    apply h
  · -- i = 0, j = 2
    unfold augment
    simp (config := {decide := true})
    have h := hA 0 2
    simp (config := {decide := true}) at h
    apply List.mem_mergeSort
    simp
    right
    apply h
  · -- i = 0, j = 3
    unfold augment
    simp (config := {decide := true})
    have h := hA 0 3
    simp (config := {decide := true}) at h
    apply List.mem_mergeSort
    simp
    right
    apply h
  · simp (config := {decide := true})
  · simp (config := {decide := true})
  · -- i = 1, j = 2
    unfold augment
    simp (config := {decide := true})
    have h := hA 1 2
    simp (config := {decide := true}) at h
    apply List.mem_mergeSort
    simp
    right
    apply h
  · -- i = 1, j = 3
    unfold augment
    simp (config := {decide := true})
    have h := hA 1 3
    simp (config := {decide := true}) at h
    apply List.mem_mergeSort
    simp
    right
    apply h
  · simp (config := {decide := true})
  · simp (config := {decide := true})
  · simp (config := {decide := true})
  · -- i = 2, j = 3
    unfold augment
    simp (config := {decide := true})
    have h := hA 2 3
    simp (config := {decide := true}) at h
    apply List.not_mem_mergeSort
    simp
    push_neg
    constructor
    · push_neg at hL
      intro p
      rw[p] at hL
      contradiction
    · apply h
  · simp (config := {decide := true})
  · simp (config := {decide := true})
  · simp (config := {decide := true})
  · simp (config := {decide := true})

lemma augment_lawful (l : List Nat) (A : PartialMatroid)
    (hA : LawfulSparsePavingMatroid n r A.matroid)
    (l_mem_range : Forall (fun a ↦ a < n) l)
    (l_length_eq_rank : l.length = r)
    (l_sorted_of_mem : l.Sorted (· < ·))
    (l_not_nearlySame_as_matroid : A.matroid.Forall fun l₁ ↦ ¬ NearlySame l₁ l) :
    LawfulSparsePavingMatroid n r (augment l A).matroid where
  mem_range := by
    unfold augment
    simp
    apply List.forall_mergeSort
    simp
    constructor
    · apply l_mem_range
    · exact hA.mem_range
  length_eq_rank := by
    unfold augment
    simp
    apply List.forall_mergeSort
    simp
    constructor
    · apply l_length_eq_rank
    · exact hA.length_eq_rank
  sorted_of_mem := by
    unfold augment
    simp
    apply List.forall_mergeSort
    simp
    constructor
    · apply l_sorted_of_mem
    · exact hA.sorted_of_mem
  sorted := by
    unfold augment
    simp
    unfold sort
    sorry
  pairwise_not_nearlySame := by
    unfold augment
    simp
    unfold sort
    sorry



lemma elimNearlySame_notAdding (l : List Nat) (A : List (List Nat)) :
    ∀ k, k ∈ (elimNearlySame l A) → k ∈ A := by
  induction A with
  | nil => simp [elimNearlySame]
  | cons h1 t1 IH =>
    simp [elimNearlySame]
    split_ifs
    · intro t h
      apply IH at h
      right
      exact h
    · intro t h
      simp at h
      obtain th | hh := h
      left
      exact th
      apply IH at hh
      right
      exact hh



lemma elimGreater_notAdding (l : List Nat) (A : List (List Nat)) :
    ∀ k, k ∈ (elimGreater l A) → k ∈ A := by
  induction A with
  | nil => simp [elimGreater]
  | cons h1 t1 IH =>
    simp [elimGreater]
    intro k hk
    split_ifs at hk
    · apply IH at hk
      right
      apply hk
    · simp at hk
      obtain thk | hhk := hk
      left
      exact thk
      apply IH at hhk
      right
      exact hhk


lemma augment_notAdding (l : List Nat) (A : PartialMatroid) :
    ∀ k, k ∈ (augment l A).remainingOptions → k ∈ A.remainingOptions := by
  unfold augment
  simp
  intro k hk
  apply elimGreater_notAdding at hk
  apply elimNearlySame_notAdding
  exact hk


-- Need to figure out goal and potential hypothesis
lemma elimNearlySame_not_nearlySame (l : List Nat) (L : (List Nat)) :
   ∀ k, k ∈ (elimNearlySame l A) → k ∈ A  := by
  sorry


-- Need to figure out goal and potential hypothesis
lemma elimGreater_not_nearlySame (l : List Nat) (A : List (List Nat)) :
    ∀ k, k ∈ (elimGreater l A) → k ∈ A := by
    sorry


-- Homework
lemma augment_not_nearlySame (l : List Nat) (A : PartialMatroid)
    (hA : A.matroid.Forall (fun l₁ ↦ A.remainingOptions.Forall (fun l₂ ↦ ¬NearlySame l₁ l₂))):
    Forall (fun l₁ ↦ Forall (fun l₂ ↦ ¬NearlySame l₁ l₂) (augment l A).remainingOptions)
      (augment l A).matroid := by
  unfold augment
  simp
  apply List.forall_mergeSort
  push_neg at hA
  simp at hA
  rw [List.forall_iff_forall_mem]
  intro l₁ q
  sorry
