import PNP.Factor

/-!
# Exact existential quantification

A projected factor is the disjunction of its two Boolean cofactors. The
quantifier ranges over one bit, and consequently introduces no real arithmetic,
approximation, relaxation, or unbounded oracle.
-/
namespace PNP

def project (i : Nat) (f : Factor) : Factor :=
  fun a => f (set a i false) || f (set a i true)

@[simp] theorem project_true_iff (i : Nat) (f : Factor) (a : Assignment) :
    project i f a = true ↔ ∃ b : Bool, f (set a i b) = true := by
  simp [project, bool_cases_exists]

theorem project_of_witness (i : Nat) (f : Factor) (a : Assignment)
    (h : f a = true) : project i f a = true := by
  apply (project_true_iff i f a).mpr
  exact ⟨a i, by simpa using h⟩

theorem project_satisfiable_iff (i : Nat) (f : Factor) :
    Satisfiable (project i f) ↔ Satisfiable f := by
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨b, hb⟩ := (project_true_iff i f a).mp ha
    exact ⟨set a i b, hb⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, project_of_witness i f a ha⟩

theorem project_unsatisfiable_iff (i : Nat) (f : Factor) :
    Unsatisfiable (project i f) ↔ Unsatisfiable f := by
  simp [unsatisfiable_iff_not_satisfiable, project_satisfiable_iff]

@[simp] theorem project_set (i : Nat) (f : Factor) (a : Assignment) (b : Bool) :
    project i f (set a i b) = project i f a := by
  simp [project]

@[simp] theorem project_idempotent (i : Nat) (f : Factor) :
    project i (project i f) = project i f := by
  funext a
  simp [project]

@[simp] theorem project_truth (i : Nat) : project i truth = truth := by
  funext a; simp [project, truth]

@[simp] theorem project_falsity (i : Nat) : project i falsity = falsity := by
  funext a; simp [project, falsity]

theorem project_commute (i j : Nat) (f : Factor) :
    project i (project j f) = project j (project i f) := by
  by_cases h : i = j
  · subst j; rfl
  · funext a
    simp only [project]
    rw [set_commute a i j false false h,
      set_commute a i j false true h,
      set_commute a i j true false h,
      set_commute a i j true true h]
    cases f (set (set a j false) i false) <;>
      cases f (set (set a j true) i false) <;>
      cases f (set (set a j false) i true) <;>
      cases f (set (set a j true) i true) <;> rfl

end PNP
