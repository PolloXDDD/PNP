import PNP.Witness

/-!
# Repeated elimination and reverse reconstruction

The elimination order is arbitrary, including repetitions and irrelevant
variables. All soundness and completeness results hold independently of a
width heuristic. Evaluation may have exponential cost.
-/
namespace PNP

def eliminate : List Nat → Factor → Factor
  | [], f => f
  | i :: is, f => eliminate is (project i f)

@[simp] theorem eliminate_nil (f : Factor) : eliminate [] f = f := rfl

@[simp] theorem eliminate_cons (i : Nat) (is : List Nat) (f : Factor) :
    eliminate (i :: is) f = eliminate is (project i f) := rfl

theorem eliminate_append (is js : List Nat) (f : Factor) :
    eliminate (is ++ js) f = eliminate js (eliminate is f) := by
  induction is generalizing f with
  | nil => rfl
  | cons i is ih => exact ih (project i f)

theorem eliminate_satisfiable_iff (is : List Nat) (f : Factor) :
    Satisfiable (eliminate is f) ↔ Satisfiable f := by
  induction is generalizing f with
  | nil => rfl
  | cons i is ih =>
    rw [eliminate_cons, ih, project_satisfiable_iff]

theorem eliminate_unsatisfiable_iff (is : List Nat) (f : Factor) :
    Unsatisfiable (eliminate is f) ↔ Unsatisfiable f := by
  simp [unsatisfiable_iff_not_satisfiable, eliminate_satisfiable_iff]

theorem eliminate_of_witness (is : List Nat) (f : Factor) (a : Assignment)
    (h : f a = true) : eliminate is f a = true := by
  induction is generalizing f with
  | nil => exact h
  | cons i is ih => exact ih (project i f) (project_of_witness i f a h)

def reconstruct : List Nat → Factor → Assignment → Assignment
  | [], _, a => a
  | i :: is, f, a => recover i f (reconstruct is (project i f) a)

@[simp] theorem reconstruct_nil (f : Factor) (a : Assignment) :
    reconstruct [] f a = a := rfl

@[simp] theorem reconstruct_cons (i : Nat) (is : List Nat)
    (f : Factor) (a : Assignment) :
    reconstruct (i :: is) f a = recover i f (reconstruct is (project i f) a) := rfl

theorem reconstruct_sound (is : List Nat) (f : Factor) (a : Assignment)
    (h : eliminate is f a = true) : f (reconstruct is f a) = true := by
  induction is generalizing f with
  | nil => exact h
  | cons i is ih =>
    exact recover_sound i f _ (ih (project i f) h)

theorem reconstruct_other (is : List Nat) (f : Factor) (a : Assignment)
    (j : Nat) (h : j ∉ is) : reconstruct is f a j = a j := by
  induction is generalizing f with
  | nil => rfl
  | cons i is ih =>
    have hji : j ≠ i := by intro he; subst j; exact h (by simp)
    have hj : j ∉ is := by intro hj; exact h (by simp [hj])
    rw [reconstruct_cons, recover_other i j f _ hji, ih (project i f) hj]

theorem reconstruct_agrees_outside (is : List Nat) (f : Factor)
    (a : Assignment) (s : List Nat) (h : ∀ j, j ∈ s → j ∉ is) :
    AgreeOn s (reconstruct is f a) a := by
  intro j hj
  exact reconstruct_other is f a j (h j hj)

end PNP
