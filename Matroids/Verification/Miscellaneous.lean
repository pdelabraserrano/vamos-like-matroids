import Mathlib.Data.List.Basic

variable {α β : Type*}

/-- Map a partially-defined (i.e. dependent) function `f` over a list, if the dependency is
satisfied for every element of the list. -/
def List.dependentMap {P : α → Prop} (f : ∀ a, P a → β) : ∀ (l : List α), l.Forall P → List β
  | [], _ => []
  | h :: t, hl =>
    let hl' : _ ∧ _ := (List.forall_cons _ _ _).1 hl
    f h hl'.1 :: dependentMap f t hl'.2
