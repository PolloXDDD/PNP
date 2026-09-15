import PNP.Elimination

/-! Support bookkeeping for a complete elimination schedule. -/
namespace PNP

def remainingScope : List Nat → List Nat → List Nat
  | [], s => s
  | i :: is, s => remainingScope is (eraseVar i s)

@[simp] theorem mem_remainingScope (is s : List Nat) (j : Nat) :
    j ∈ remainingScope is s ↔ j ∈ s ∧ j ∉ is := by
  induction is generalizing s with
  | nil => simp [remainingScope]
  | cons i is ih =>
    simp [remainingScope, ih, and_assoc, and_left_comm, and_comm]

theorem remainingScope_empty {is s : List Nat}
    (h : ∀ j, j ∈ s → j ∈ is) : remainingScope is s = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro j hj
  obtain ⟨hs, hi⟩ := (mem_remainingScope is s j).mp hj
  exact hi (h j hs)

@[simp] theorem remainingScope_self (s : List Nat) : remainingScope s s = [] :=
  remainingScope_empty (fun _ h => h)

theorem supported_eliminate {s : List Nat} {f : Factor} (is : List Nat)
    (h : Supported s f) : Supported (remainingScope is s) (eliminate is f) := by
  induction is generalizing s f with
  | nil => exact h
  | cons i is ih => exact ih (supported_project i h)

theorem eliminate_constant_of_covers {s : List Nat} {f : Factor}
    (is : List Nat) (h : Supported s f) (hc : ∀ j, j ∈ s → j ∈ is)
    (a b : Assignment) : eliminate is f a = eliminate is f b := by
  have hs := supported_eliminate is h
  rw [remainingScope_empty hc] at hs
  exact supported_nil_constant hs a b

theorem elimination_decision_iff {s : List Nat} {f : Factor}
    (is : List Nat) (h : Supported s f) (hc : ∀ j, j ∈ s → j ∈ is)
    (a : Assignment) : eliminate is f a = true ↔ Satisfiable f := by
  have hs := supported_eliminate is h
  rw [remainingScope_empty hc] at hs
  rw [← eliminate_satisfiable_iff is f]
  exact (supported_nil_sat_iff hs a).symm

end PNP
