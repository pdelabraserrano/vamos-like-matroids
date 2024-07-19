import Matroids.AllPossibilities
import Matroids.Verification.Basic
import Matroids.Verification.PartialMatroid
import Matroids.Verification.Miscellaneous

open PartialMatroid List
set_option pp.unicode.fun true

/-! ## Prerequisites -/
-- to be contributed to the main library
-- probably an induction


lemma augmentations_lawful (A : PartialMatroid)
    (hM : LawfulSparsePavingMatroid n r A.matroid)
    (remainingOptions_mem_range : A.remainingOptions.Forall (List.Forall fun j ↦ j < n))
    (remainingOptions_length_eq_rank : A.remainingOptions.Forall (fun l ↦ l.length = r))
    (remainingOptions_sorted_of_mem : A.remainingOptions.Forall fun m ↦ m.Sorted (· < ·))
    (remainingOptions_not_nearlySame :
      A.matroid.Forall fun l₁ ↦ A.remainingOptions.Forall fun l₂ ↦ ¬ NearlySame l₁ l₂) :
    (augmentations A).Forall (fun M' ↦ LawfulSparsePavingMatroid n r M'.matroid) := by
  unfold augmentations
  rw [List.forall_map_iff]
  rw [List.forall_iff_forall_mem]
  intro l hl
  apply augment_lawful
  · apply hM
  · rw [List.forall_iff_forall_mem] at remainingOptions_mem_range
    apply remainingOptions_mem_range at hl
    apply hl
  · rw [List.forall_iff_forall_mem] at remainingOptions_length_eq_rank
    apply remainingOptions_length_eq_rank at hl
    apply hl
  · rw [List.forall_iff_forall_mem] at remainingOptions_sorted_of_mem
    apply remainingOptions_sorted_of_mem at hl
    apply hl
  · rw [List.forall_iff_forall_mem] at remainingOptions_not_nearlySame ⊢
    intro l₂ hl₂
    apply remainingOptions_not_nearlySame at hl₂
    rw [List.forall_iff_forall_mem] at hl₂
    apply hl₂ at hl
    apply hl


lemma augmentations_remainingOptions (A : PartialMatroid) :
    Forall (fun B ↦ ∀ l, l ∈ B.remainingOptions → l ∈ A.remainingOptions) (augmentations A) := by
  unfold augmentations
  rw [List.forall_iff_forall_mem]
  intro B hB
  simp at hB
  intro k hk
  obtain ⟨l, hhb⟩ := hB
  obtain ⟨_, hhhb⟩ := hhb
  apply augment_notAdding l
  rw [hhhb]
  exact hk


/-- For all partial matroids `A` for which no lists in `A.matroid` are `NearlySame` as any list in
`A.remainingOptions`, for any partial matroid `B`, which belongs to `augmentations A`, no
lists in `B.matroid` are `NearlySame` as any list in `B.remainingOptions` -/
lemma augmentations_not_nearlySame (A : PartialMatroid)
    (hA : A.matroid.Forall (fun l₁ ↦ A.remainingOptions.Forall (fun l₂ ↦ ¬NearlySame l₁ l₂))):
    (augmentations A).Forall (fun B ↦ B.matroid.Forall
      (fun l₁ ↦ B.remainingOptions.Forall (fun l₂ ↦ ¬NearlySame l₁ l₂)))  := by
  unfold augmentations
  rw [List.forall_iff_forall_mem]
  simp only [mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  intro l _
  apply augment_not_nearlySame (l := l) at hA
  apply hA


lemma augmentationsFinal_lawful (i : ℕ) (M : PartialMatroid)
    (hM : LawfulSparsePavingMatroid n r M.matroid)
    (remainingOptions_mem_range : M.remainingOptions.Forall (List.Forall fun j ↦ j < n))
    (remainingOptions_length_eq_rank : M.remainingOptions.Forall (fun l ↦ l.length = r))
    (remainingOptions_sorted_of_mem : M.remainingOptions.Forall fun m ↦ m.Sorted (· < ·))
    (remainingOptions_not_nearlySame :
      M.matroid.Forall fun l₁ ↦ M.remainingOptions.Forall fun l₂ ↦ ¬ NearlySame l₁ l₂) :
    (augmentationsFinal i M).Forall (fun M' ↦ LawfulSparsePavingMatroid n r M'.matroid) := by
  match i with
  | 0 => simp [hM]
  | k + 1 =>
    apply List.Forall.join
    rw [List.forall_map_iff]
    rw [List.forall_iff_forall_mem]
    -- let `B` be a matroid in the augmentations list of `A`
    intro B hB
    -- inductive hypothesis: use the same result for `k` in this `k + 1` step
    apply augmentationsFinal_lawful
    · -- proof that `B` is still a `LawfulSparsePavingMatroid`
      have hB₂ := augmentations_lawful M (n := n) (r := r)
      apply hB₂ at hM
      apply hM at remainingOptions_mem_range
      apply remainingOptions_mem_range at remainingOptions_length_eq_rank
      apply remainingOptions_length_eq_rank at remainingOptions_sorted_of_mem
      apply remainingOptions_sorted_of_mem at remainingOptions_not_nearlySame
      rw [List.forall_iff_forall_mem] at remainingOptions_not_nearlySame
      apply remainingOptions_not_nearlySame
      exact hB
    · -- proof that `remainingOptions` of `B` has less elements than `remainingOptions` of `A`
      have hAB := augmentations_remainingOptions M
      rw [List.forall_iff_forall_mem] at hAB
      apply hAB at hB
      rw [List.forall_iff_forall_mem] at remainingOptions_mem_range ⊢
      intro l hl
      apply remainingOptions_mem_range
      apply hB
      apply hl
    · -- proof that elements in `remainingOptions` of `B` have length `r`
      have hAB := augmentations_remainingOptions M
      rw [List.forall_iff_forall_mem] at hAB
      apply hAB at hB
      rw [List.forall_iff_forall_mem] at remainingOptions_length_eq_rank ⊢
      intro l hl
      apply remainingOptions_length_eq_rank
      apply hB
      apply hl
    · -- proof that elements in `remainingOptions` of `B` are sorted
      have hAB := augmentations_remainingOptions M
      rw [List.forall_iff_forall_mem] at hAB
      apply hAB at hB
      rw [List.forall_iff_forall_mem] at remainingOptions_sorted_of_mem ⊢
      intro l hl
      apply remainingOptions_sorted_of_mem
      apply hB
      apply hl
    · -- proof that two elements in `remainingOptions` of `B` are not `NearlySame`
      have hAB := augmentations_not_nearlySame M
      apply hAB at remainingOptions_not_nearlySame
      rw [List.forall_iff_forall_mem] at remainingOptions_not_nearlySame
      apply remainingOptions_not_nearlySame
      apply hB


lemma augmentations_normalized (A : PartialMatroid)
    (hAM : NormalizedVamosLike A.matroid)
    (hAR : ¬[4, 5, 6, 7] ∈ A.remainingOptions):
    (augmentations A).Forall (fun A' ↦ NormalizedVamosLike A'.matroid) := by
  unfold augmentations
  rw [List.forall_map_iff]
  rw [List.forall_iff_forall_mem]
  intro l hl
  sorry

-- Currently working on this, need to figure out how to phrase the goal
lemma augmentations_remainingOptions_normalized (A : PartialMatroid)
    (hAR : ¬[4, 5, 6, 7] ∈ A.remainingOptions):
    Forall (fun B ↦ ¬[4, 5, 6, 7] ∈ B.remainingOptions) (augmentations A) := by
  rw [List.forall_iff_forall_mem]
  intro B intro hB

  sorry

lemma augmentationsFinal_normalized (i : ℕ) (A : PartialMatroid)
    (hAM : NormalizedVamosLike A.matroid)
    (hAR : ¬[4, 5, 6, 7] ∈ A.remainingOptions):
    (augmentationsFinal i A).Forall (fun A' ↦ NormalizedVamosLike A'.matroid) := by
  match i with
  | 0 => simp [hAM]
  | j + 1 =>
    apply List.Forall.join
    rw [List.forall_map_iff]
    rw [List.forall_iff_forall_mem]
    -- let `B` be a matroid in the augmentations list of `A`
    intro B hB
    -- inductive hypothesis: use the same result for `k` in this `k + 1` step
    apply augmentationsFinal_normalized
    · -- proof that `B` is still a `LawfulSparsePavingMatroid`
      have hC := augmentations_normalized A
      apply hC at hAM
      apply hAM at hAR
      rw [List.forall_iff_forall_mem] at hAR
      apply hAR
      apply hB
    · -- proof that `[4, 5, 6, 7]` is not part of the remainingOptions of `B`
      have hC := augmentations_remainingOptions_normalized A
      rw [List.forall_iff_forall_mem] at hC
      apply hC at hAR
      sorry
