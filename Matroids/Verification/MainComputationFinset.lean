import Matroids.Verification.Miscellaneous
import Matroids.Verification.MainComputation

/-! # The main computation, considered as producing `Finset` objects

This file restates the desired properties of the main computation (originally stated in terms of
the `List` datatype) in the language of the `Finset` datatype.
-/

/-- A "valid" (n, r) sparse paving matroid; here `n` is the number of elements of the matroid and
`r` is its rank. -/
structure Finset.LawfulSparsePavingMatroid (n r : ℕ) (s : Finset (Finset (Fin n))) : Prop :=
  (card_eq_rank : ∀ m ∈ s, m.card = r)
  (pairwise_not_nearlySame : (s : Set (Finset (Fin n))).Pairwise (fun a b ↦ (a ∩ b).card + 2 ≤ r))

/-- Property of a finset of finsets, that it contain `{0, 1, 2, 3}`, `{0, 1, 4, 5}`, `{0, 1, 6, 7}`,
`{2, 3, 4, 5}`, `{2, 3, 6, 7}`, and not contain `{4, 5, 6, 7}`. -/
def Finset.NormalizedVamosLike (s : Finset (Finset (Fin 8))) : Prop :=
  let P := ![{0, 1}, {2, 3}, {4, 5}, {6, 7}]
  ∀ i j : Fin 4, i < j → (P i) ∪ (P j) ∈ s ↔ (i, j) ≠ (2, 3)

def FinsetFinsetIsomorphic (s : Finset (Finset α)) (t : Finset (Finset β)) : Prop :=
  ∃ e : α ≃ β, e.finsetCongr.finsetCongr s = t

def LawfulSparsePavingMatroid.nonbases {n r : ℕ} {l : List (List ℕ)}
    (hl : LawfulSparsePavingMatroid n r l) :
    Finset (Finset (Fin n)) :=
  let a : List (List (Fin n)) := l.dependentMap (List.dependentMap Fin.mk) hl.mem_range
  (a.map List.toFinset).toFinset

/-- The main computation, considered as a list of `Finset (Finset (Fin 8))` objects rather than a
list of `List (List ℕ)` objects. -/
def mainComputationFinset : List (Finset (Finset (Fin 8))) :=
  mainComputation.dependentMap (fun _ ↦ LawfulSparsePavingMatroid.nonbases) mainComputation_lawful

/-- The main computation produces only `Finset (Finset (Fin 8))` objects which are valid ("lawful")
sparse paving matroids. -/
lemma mainComputationFinset_lawful {s : Finset (Finset (Fin 8))} (hs : s ∈ mainComputationFinset) :
    s.LawfulSparsePavingMatroid 8 4 := by
  sorry

/-- The main computation produces only `Finset (Finset (Fin 8))` objects which are "normalized
Vámos-like". -/
lemma mainComputationFinset_normalizedVamosLike {s : Finset (Finset (Fin 8))}
    (hs : s ∈ mainComputationFinset) : s.NormalizedVamosLike :=
  sorry

/-- The list of `Finset (Finset (Fin 8))` objects provided by the main computation are mutually
non-isomorphic (up to permutation of the underlying `Fin 8`). -/
theorem nonisomorphic_mainComputationFinset :
    mainComputationFinset.Pairwise (fun s t ↦ ¬ FinsetFinsetIsomorphic s t) :=
  sorry

/-- Any "normalized Vámos-like" `Finset (Finset (Fin 8))` object which is valid as an (8, 4) sparse
paving matroid is isomorphic to one of the objects on the list provided by the main computation. -/
theorem mainComputationFinset_exhausts {s : Finset (Finset (Fin 8))}
    (hs₁ : s.LawfulSparsePavingMatroid 8 4) (hs₂ : s.NormalizedVamosLike) :
    ∃ t ∈ mainComputationFinset, FinsetFinsetIsomorphic s t := by
  sorry
