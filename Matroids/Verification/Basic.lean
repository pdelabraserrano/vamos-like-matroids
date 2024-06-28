import Matroids.Verification.Miscellaneous
import Matroids.Relabelling
import Matroids.AllPossibilities
import Mathlib.Data.Matrix.Notation

structure LawfulSparsePavingMatroid (n r : ℕ) (l : List (List ℕ)) : Prop :=
  (mem_range : l.Forall (List.Forall fun i ↦ i < n))
  (length_eq_rank : ∀ m ∈ l, m.length = r)
  (sorted_of_mem : ∀ m ∈ l, m.Sorted (· < ·))
  (sorted : l.Sorted (· < ·))
  (pairwise_not_nearlySame : l.Pairwise (fun l₁ l₂ ↦ ¬ NearlySame l₁ l₂))

def LawfulSparsePavingMatroid.nonbases {n r : ℕ} {l : List (List ℕ)}
    (hl : LawfulSparsePavingMatroid n r l) :
    Finset (Finset (Fin n)) :=
  let a : List (List (Fin n)) := l.dependentMap (List.dependentMap Fin.mk) hl.mem_range
  (a.map List.toFinset).toFinset

def FinsetFinsetIsomorphic (s : Finset (Finset α)) (t : Finset (Finset β)) : Prop :=
  ∃ e : α ≃ β, e.finsetCongr.finsetCongr s = t

def List.NormalizedVamosLike (l : List (List ℕ)) : Prop :=
  let P := ![[0, 1], [2, 3], [4, 5], [6, 7]]
  ∀ i j : Fin 4, i < j → (P i).append (P j) ∈ l ↔ (i, j) ≠ (2, 3)

/-! ## Main computation -/

def mainComputationAux : List (List (List ℕ)) :=
  -- take the augmentations by `i` quadrangles of the Vamos sparse paving matroid, and group
  --("bucket") by basic numeric statistics
  let Vamos (i : ℕ) : List (List PartialMatroid) :=
    PartialMatroid.groupByBucket (PartialMatroid.augmentationsFinal i PartialMatroid.Vamos)
  -- eliminate duplicates within each bucket
  let prunedVamos (i : ℕ) : List (List PartialMatroid) := (Vamos i).map pruning
  -- concatenate buckets and then concatenate over all `i`
  let joinedPrunedVamos : List PartialMatroid :=
    ((List.range 9).map fun i ↦ (prunedVamos i).join).join
  -- forget the information about what more could be augmented to each and just present the
  -- quadrangle information
  joinedPrunedVamos.map PartialMatroid.matroid

irreducible_def mainComputation : List (List (List ℕ)) := mainComputationAux

/-- The main computation produces only `List (List ℕ)` objects which are valid ("lawful") sparse
paving matroids. -/
lemma mainComputation_lawful: mainComputation.Forall (LawfulSparsePavingMatroid 8 4) :=
  sorry

/-- The main computation produces only `List (List ℕ)` objects which are "normalized Vámos-like". -/
lemma mainComputation_normalizedVamosLike: mainComputation.Forall List.NormalizedVamosLike :=
  sorry

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
