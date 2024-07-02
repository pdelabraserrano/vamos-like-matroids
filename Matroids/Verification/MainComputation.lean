import Matroids.Verification.AllPossibilities
import Matroids.Verification.Vamos
import Matroids.Verification.Buckets
import Matroids.Verification.Relabelling
import Matroids.MainComputation

open PartialMatroid

/-! ## Main computation -/

/-- The main computation produces only `List (List ℕ)` objects which are valid ("lawful") sparse
paving matroids.
Informally: Theorem 1 -/
lemma mainComputation_lawful : mainComputation.Forall (LawfulSparsePavingMatroid 8 4) := by
  sorry

/-- The main computation produces only `List (List ℕ)` objects which are "normalized Vámos-like".
Informally: Theorem 2 -/
lemma mainComputation_normalizedVamosLike: mainComputation.Forall List.NormalizedVamosLike :=
  sorry

/-- The main computation, considered as a list of `Finset (Finset (Fin 8))` objects rather than a
list of `List (List ℕ)` objects. -/
def mainComputationFinset : List (Finset (Finset (Fin 8))) :=
  mainComputation.dependentMap (fun _ ↦ LawfulSparsePavingMatroid.nonbases) mainComputation_lawful

/-- The list of `Finset (Finset (Fin 8))` objects provided by the main computation are mutually
non-isomorphic (up to permutation of the underlying `Fin 8`).
Informally: Theorem 3 -/
theorem nonisomorphic_mainComputationFinset :
    mainComputationFinset.Pairwise (fun s t ↦ ¬ FinsetFinsetIsomorphic s t) :=
  sorry

/-- Any "normalized Vámos-like" `List (List ℕ)` object which is valid as an (8, 4) sparse paving
matroid is isomorphic to one of the objects on the list provided by the main computation.
Informally: Theorem 4 -/
theorem mainComputationFinset_exhausts {l : List (List ℕ)} (hl₁ : LawfulSparsePavingMatroid 8 4 l)
    (hl₂ : l.NormalizedVamosLike) :
    ∃ s ∈ mainComputationFinset, FinsetFinsetIsomorphic hl₁.nonbases s := by
  sorry
