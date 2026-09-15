import PNP.EliminationScope

/-!
# Factors carrying checked scope invariants

Every factor carries a proof that the advertised variables determine its value.
A scope may conservatively contain unused variables. This permits mechanical
union and projection without assuming an optimal support computation.
-/
namespace PNP

structure ScopedFactor where
  scope : List Nat
  eval : Factor
  locality : Supported scope eval

def evalFactors (fs : List ScopedFactor) : Factor := combine (fs.map ScopedFactor.eval)

def unionScope (fs : List ScopedFactor) : List Nat := fs.flatMap ScopedFactor.scope

@[simp] theorem evalFactors_nil (a : Assignment) : evalFactors [] a = true := rfl

@[simp] theorem evalFactors_cons (f : ScopedFactor) (fs : List ScopedFactor)
    (a : Assignment) : evalFactors (f :: fs) a = (f.eval a && evalFactors fs a) := rfl

theorem evalFactors_true_iff (fs : List ScopedFactor) (a : Assignment) :
    evalFactors fs a = true ↔ ∀ f, f ∈ fs → f.eval a = true := by
  simp [evalFactors, combine_true_iff]

@[simp] theorem mem_unionScope (fs : List ScopedFactor) (j : Nat) :
    j ∈ unionScope fs ↔ ∃ f, f ∈ fs ∧ j ∈ f.scope := by
  simp [unionScope]

theorem supported_evalFactors (fs : List ScopedFactor) :
    Supported (unionScope fs) (evalFactors fs) := by
  intro a b hab
  apply eq_of_true_iff
  rw [evalFactors_true_iff, evalFactors_true_iff]
  have he : ∀ f, f ∈ fs → f.eval a = f.eval b := by
    intro f hf
    apply f.locality a b
    intro j hj
    exact hab j ((mem_unionScope fs j).mpr ⟨f, hf, hj⟩)
  constructor
  · intro ha f hf; rw [← he f hf]; exact ha f hf
  · intro hb f hf; rw [he f hf]; exact hb f hf

def mergedFactor (fs : List ScopedFactor) : ScopedFactor :=
  ⟨unionScope fs, evalFactors fs, supported_evalFactors fs⟩

def projectedFactor (i : Nat) (f : ScopedFactor) : ScopedFactor :=
  ⟨eraseVar i f.scope, project i f.eval, supported_project i f.locality⟩

@[simp] theorem projectedFactor_eval (i : Nat) (f : ScopedFactor) :
    (projectedFactor i f).eval = project i f.eval := rfl

@[simp] theorem projectedFactor_scope (i : Nat) (f : ScopedFactor) :
    (projectedFactor i f).scope = eraseVar i f.scope := rfl

@[simp] theorem projectedFactor_absent (i : Nat) (f : ScopedFactor) :
    i ∉ (projectedFactor i f).scope := by simp

theorem evalFactors_append (fs gs : List ScopedFactor) :
    evalFactors (fs ++ gs) = conjunction (evalFactors fs) (evalFactors gs) := by
  simp [evalFactors, List.map_append, combine_append]

theorem evalFactors_permutation {fs gs : List ScopedFactor} (h : fs.Perm gs) :
    evalFactors fs = evalFactors gs := by
  apply combine_permutation
  exact h.map ScopedFactor.eval

end PNP
