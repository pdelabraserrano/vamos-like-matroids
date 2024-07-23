import Matroids.Verification.AllPossibilities
import Matroids.Verification.Vamos
import Matroids.Verification.Buckets
import Matroids.Verification.Relabelling
import Matroids.MainComputation

/-! # Verifying that the main computation has the desired properties -/

/-! ## Main argument -/

lemma augmentedVamos_lawful (i : ℕ) :
    (augmentedVamos i).Forall fun L ↦ L.Forall fun M ↦ LawfulSparsePavingMatroid 8 4 M.matroid := by
  unfold augmentedVamos
  apply groupByBucket_lawful
  apply augmentationsFinal_lawful
  · apply vamos_lawful
  · apply vamos_remainingOptions_mem_range
  · apply vamos_remainingOptions_length_eq_rank
  · apply vamos_remainingOptions_sorted_of_mem
  · apply vamos_remainingOptions_not_nearlySame

--We know this is wrong. This is just a placeholder
lemma augmentedVamos_normalized (i : ℕ) :
    (augmentedVamos i).Forall fun L ↦ L.Forall fun M ↦ List.NormalizedVamosLike M.matroid := by
  unfold augmentedVamos
  apply groupByBucket_normalized
  apply augmentationsFinal_normalized
  · simp
    sorry
  · sorry






lemma prunedVamos_lawful (i : ℕ) :
    (prunedVamos i).Forall fun L ↦ L.Forall fun M ↦ LawfulSparsePavingMatroid 8 4 M.matroid := by
  rw [prunedVamos_def]
  rw [List.forall_map_iff]
  apply List.Forall.imp pruning_lawful
  apply augmentedVamos_lawful

lemma prunedVamos_normalized (i : ℕ) :
    (prunedVamos i).Forall fun L ↦ L.Forall fun M ↦ List.NormalizedVamosLike M.matroid := by
  rw [prunedVamos_def]
  rw [List.forall_map_iff]
  apply List.Forall.imp pruning_normalized
  apply augmentedVamos_normalized



lemma joinedPrunedVamos_lawful :
    joinedPrunedVamos.Forall fun M ↦ LawfulSparsePavingMatroid 8 4 M.matroid := by
  unfold joinedPrunedVamos
  apply List.Forall.join
  rw [List.forall_map_iff]
  rw [List.forall_iff_forall_mem]
  intro i _
  apply List.Forall.join
  apply prunedVamos_lawful

lemma joinedPrunedVamos_normalized :
    joinedPrunedVamos.Forall fun M ↦ List.NormalizedVamosLike M.matroid := by
  unfold joinedPrunedVamos
  apply List.Forall.join
  rw [List.forall_map_iff]
  rw [List.forall_iff_forall_mem]
  intro i _
  apply List.Forall.join
  apply prunedVamos_normalized

/-- The main computation produces only `List (List ℕ)` objects which are valid ("lawful") sparse
paving matroids.
Informally: Theorem 1 -/
lemma mainComputation_lawful : mainComputation.Forall (LawfulSparsePavingMatroid 8 4) := by
  unfold mainComputation
  rw [List.forall_map_iff]
  apply joinedPrunedVamos_lawful

/-- The main computation produces only `List (List ℕ)` objects which are "normalized Vámos-like".
Informally: Theorem 2 -/
lemma mainComputation_normalizedVamosLike: mainComputation.Forall List.NormalizedVamosLike := by
  unfold mainComputation
  rw [List.forall_map_iff]
  apply joinedPrunedVamos_normalized


/-- The list of `List (List ℕ)` objects provided by the main computation are mutually
non-isomorphic (up to permutation of 0, 1, 2, ... 7).
Informally: Theorem 3 -/
theorem nonisomorphic_mainComputation :
    mainComputation.Pairwise (fun l₁ l₂ ↦ ¬ permutationsComparison 8 l₁ l₂) :=
  sorry

/-- Any "normalized Vámos-like" `List (List ℕ)` object which is valid as an (8, 4) sparse paving
matroid is isomorphic to one of the objects on the list provided by the main computation.
Informally: Theorem 4 -/
theorem mainComputation_exhausts {l : List (List ℕ)} (hl₁ : LawfulSparsePavingMatroid 8 4 l)
    (hl₂ : l.NormalizedVamosLike) :
    ∃ l' ∈ mainComputation, permutationsComparison 8 l l' := by
  sorry
