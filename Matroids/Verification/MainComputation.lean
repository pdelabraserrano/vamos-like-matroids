import Matroids.Verification.AllPossibilities
import Matroids.Verification.Vamos
import Matroids.Verification.Buckets
import Matroids.Verification.Relabelling
import Matroids.MainComputation

/-! # Verifying that the main computation has the desired properties -/

/-- The main computation produces only `List (List ℕ)` objects which are valid ("lawful") sparse
paving matroids.
Informally: Theorem 1 -/
lemma mainComputation_lawful : mainComputation.Forall (LawfulSparsePavingMatroid 8 4) := by
  sorry

/-- The main computation produces only `List (List ℕ)` objects which are "normalized Vámos-like".
Informally: Theorem 2 -/
lemma mainComputation_normalizedVamosLike: mainComputation.Forall List.NormalizedVamosLike :=
  sorry

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
