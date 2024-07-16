import Matroids.NearlySame
import Mathlib.Data.Matrix.Notation

/-- A "valid" (n, r) sparse paving matroid; here `n` is the number of elements of the matroid and
`r` is its rank. -/
@[mk_iff]
structure LawfulSparsePavingMatroid (n r : ℕ) (l : List (List ℕ)) : Prop :=
  (mem_range : l.Forall (List.Forall fun i ↦ i < n))
  (length_eq_rank : l.Forall fun m ↦ m.length = r)
  (sorted_of_mem : l.Forall fun m ↦ m.Sorted (· < ·))
  (sorted : l.Sorted (· < ·))
  (pairwise_not_nearlySame : l.Pairwise (fun l₁ l₂ ↦ ¬ NearlySame l₁ l₂))

instance : DecidablePred (LawfulSparsePavingMatroid n r) :=
  fun l ↦ decidable_of_decidable_of_iff (lawfulSparsePavingMatroid_iff n r l).symm

/-- Property of a list of lists, that it contain `[0, 1, 2, 3]`, `[0, 1, 4, 5]`, `[0, 1, 6, 7]`,
`[2, 3, 4, 5]`, `[2, 3, 6, 7]`, and not contain `[4, 5, 6, 7]`. -/
def List.NormalizedVamosLike (l : List (List ℕ)) : Prop :=
  let P := ![[0, 1], [2, 3], [4, 5], [6, 7]]
  ∀ i j : Fin 4, i < j → (P i).append (P j) ∈ l ↔ (i, j) ≠ (2, 3)

instance : DecidablePred (List.NormalizedVamosLike) := by
  unfold List.NormalizedVamosLike
  infer_instance
