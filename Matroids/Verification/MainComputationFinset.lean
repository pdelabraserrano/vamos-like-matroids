import Matroids.Verification.Miscellaneous
import Matroids.Verification.MainComputation

def LawfulSparsePavingMatroid.nonbases {n r : ℕ} {l : List (List ℕ)}
    (hl : LawfulSparsePavingMatroid n r l) :
    Finset (Finset (Fin n)) :=
  let a : List (List (Fin n)) := l.dependentMap (List.dependentMap Fin.mk) hl.mem_range
  (a.map List.toFinset).toFinset

def FinsetFinsetIsomorphic (s : Finset (Finset α)) (t : Finset (Finset β)) : Prop :=
  ∃ e : α ≃ β, e.finsetCongr.finsetCongr s = t

/-- The main computation, considered as a list of `Finset (Finset (Fin 8))` objects rather than a
list of `List (List ℕ)` objects. -/
def mainComputationFinset : List (Finset (Finset (Fin 8))) :=
  mainComputation.dependentMap (fun _ ↦ LawfulSparsePavingMatroid.nonbases) mainComputation_lawful

/-- The list of `Finset (Finset (Fin 8))` objects provided by the main computation are mutually
non-isomorphic (up to permutation of the underlying `Fin 8`). -/
theorem nonisomorphic_mainComputationFinset :
    mainComputationFinset.Pairwise (fun s t ↦ ¬ FinsetFinsetIsomorphic s t) :=
  sorry

/-- Any "normalized Vámos-like" `List (List ℕ)` object which is valid as an (8, 4) sparse paving
matroid is isomorphic to one of the objects on the list provided by the main computation. -/
theorem mainComputationFinset_exhausts {l : List (List ℕ)} (hl₁ : LawfulSparsePavingMatroid 8 4 l)
    (hl₂ : l.NormalizedVamosLike) :
    ∃ s ∈ mainComputationFinset, FinsetFinsetIsomorphic hl₁.nonbases s := by
  sorry
