import Matroids.Verification.Basic
import Matroids.Relabelling



lemma mem_of_mem_pruning {lA : List (PartialMatroid)} {A : PartialMatroid}
    (hA : A ∈ pruning lA) :
    A ∈ lA := by
  induction lA with
  | nil =>
    rw[pruning] at hA
    apply hA
  | cons h t IH =>
    simp[pruning] at hA
    split_ifs at hA
    · simp
      apply IH at hA
      right
      apply hA
    · simp
      apply IH at hA
      right
      apply hA
    · simp
      simp at hA
      obtain hAA | hAAA := hA
      left
      apply hAA
      sorry

/-- If `A` is a list of `PartialMatroid`s, all of which are valid (n, r)-sparse paving matroids,
then when the `pruning` operation is performed, every `PartialMatroid` in the the resulting
list of partial matroids is still a valid (n, r)-sparse paving matroids. -/
lemma pruning_lawful (lA : List PartialMatroid)
    (hA : lA.Forall (fun M ↦ LawfulSparsePavingMatroid n r M.matroid)) :
    (pruning lA).Forall (fun M ↦ LawfulSparsePavingMatroid n r M.matroid) := by
  induction lA with
  | nil => simp
  | cons h t IH =>
    simp at hA
    obtain ⟨h_ok, t_ok⟩ := hA
    apply IH at t_ok
    simp [pruning]
    split_ifs
    · exact t_ok
    · exact t_ok
    · simp
      constructor
      · exact h_ok
      · exact t_ok


lemma pruning_normalized (A : List PartialMatroid)
    (hA : A.Forall (fun M ↦ List.NormalizedVamosLike M.matroid)) :
    (pruning A).Forall (fun M ↦ List.NormalizedVamosLike M.matroid) := by
  induction A with
  | nil => simp
  | cons h t IH =>
    simp at hA
    obtain ⟨h_ok, t_ok⟩ := hA
    apply IH at t_ok
    simp [pruning]
    split_ifs
    · exact t_ok
    · exact t_ok
    · simp
      constructor
      · exact h_ok
      · exact t_ok




/-- If `A` is a list of `PartialMatroid`s, then when the `pruning` operation is performed, every
`PartialMatroid` in `A` is isomorphic (up to permutation of 0, 1, 2, ... n - 1) to one of the
`PartialMatroid`s in the pruned list. -/
theorem permutationsComparison_mem_pruning_of_mem (A : List PartialMatroid) :
    A.Forall fun M ↦ ∃ M' ∈ pruning A, permutationsComparison n M.matroid M'.matroid := by
  induction A with
  | nil => simp[pruning]
  | cons h t IH =>
    rw [List.forall_iff_forall_mem]
    intro p hp
    rw [List.forall_iff_forall_mem] at IH
    simp at hp

    obtain hp1 | hp2 := hp
    · subst hp1
      unfold pruning
      clear IH
      simp
      split_ifs with h
      obtain ⟨ q, hq ⟩ := h
      obtain ⟨ a, ha ⟩ := hq
      unfold specialPermutationsComparison at ha
      use q
      constructor
      apply a
      unfold permutationsComparison

      sorry
      sorry
      sorry
    sorry



theorem foo_sameUpToRelabelling {A B : List (List Nat)} {g : Nat → Nat}
    {h : sameUpToRelabelling A B g} : A.length = B.length := by
  unfold sameUpToRelabelling at h
  simp at h
  -- unfold List.sort at h
  sorry

theorem length_eq_of_permutationsComparison {A B : List (List Nat)}
    {h : permutationsComparison 8 A B} : A.length = B.length := by
  unfold permutationsComparison at h
  rw [List.any_eq_true] at h
  obtain ⟨g, hg⟩ := h
  obtain ⟨_, h⟩ := hg
  apply foo_sameUpToRelabelling at h
  apply h

-- now?
theorem nonisomorphic_of_length {A B : List (List Nat)} (h : A.length ≠ B.length) :
    ¬ permutationsComparison 8 A B := by
  intro h₁
  apply h
  clear h
  apply length_eq_of_permutationsComparison
  apply h₁
