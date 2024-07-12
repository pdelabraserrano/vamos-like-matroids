import Matroids.AllPossibilities
import Matroids.Verification.Basic

open PartialMatroid List
set_option pp.unicode.fun true

/-! ## Prerequisites -/
-- to be contributed to the main library
-- probably an induction
lemma List.forall_append_iff {L1 L2 : List α} {P : α → Prop} :
     List.Forall P (L1 ++ L2) ↔ (List.Forall P L1) ∧ (List.Forall P L2) := by
  induction L1 with
  | nil =>
    simp
  | cons h t IH =>
    simp
    constructor
    · intro h1
      obtain ⟨th1, hh1⟩ := h1
      obtain ⟨IH1, _⟩ := IH
      apply IH1 at hh1
      obtain ⟨thh1, hhh1⟩ := hh1
      constructor
      · constructor
        · exact th1
        · exact thh1
      · exact hhh1
    · intro h1
      obtain ⟨th1, hh1⟩ := h1
      obtain ⟨_, IH2⟩ := IH
      obtain ⟨tth1, hth1⟩ := th1
      constructor
      · exact tth1
      · apply IH2
        constructor
        · exact hth1
        · exact hh1


lemma List.Forall.join {L : List (List α)} {P : α → Prop} (hl : L.Forall fun l ↦ l.Forall P) :
    L.join.Forall P := by
    unfold join
    match L with
    | []      => simp [join]
    | a :: as =>
      simp [join]
      have IH := List.Forall.join (L := as) (P := P)
      have h1 : Forall (fun l => Forall P l) as
      · simp at hl
        obtain ⟨th1, hh1⟩ := hl
        exact hh1
      apply IH at h1
      simp at hl
      obtain ⟨th1, hh1⟩ := hl
      rw [forall_append_iff]
      constructor
      · exact th1
      · exact h1



lemma augmentations_lawful (A : PartialMatroid)
    (hM : LawfulSparsePavingMatroid n r A.matroid)
    (remainingOptions_mem_range : A.remainingOptions.Forall (List.Forall fun j ↦ j < n))
    (remainingOptions_length_eq_rank : A.remainingOptions.Forall (fun l ↦ l.length = r))
    (remainingOptions_sorted_of_mem : A.remainingOptions.Forall fun m ↦ m.Sorted (· < ·))
    (remainingOptions_not_nearlySame :
      A.matroid.Forall fun l₁ ↦ A.remainingOptions.Forall fun l₂ ↦ ¬ NearlySame l₁ l₂) :
    (augmentations A).Forall (fun M' ↦ LawfulSparsePavingMatroid n r M'.matroid):=
  sorry

lemma augmentations_remainingOptions (A : PartialMatroid) :
    Forall (fun B ↦ ∀ l, l ∈ B.remainingOptions → l ∈ A.remainingOptions) (augmentations A) := by
  sorry

lemma augmentations_not_nearlySame (A : PartialMatroid)
    (hA : A.matroid.Forall (fun l₁ ↦ A.remainingOptions.Forall (fun l₂ ↦ ¬NearlySame l₁ l₂))):
    (augmentations A).Forall (fun B ↦ B.matroid.Forall
      (fun l₁ ↦ B.remainingOptions.Forall (fun l₂ ↦ ¬NearlySame l₁ l₂)))  := by
  sorry


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
