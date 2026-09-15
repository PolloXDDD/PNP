import PNP.Assignment
import PNP.Boolean

/-!
# Boolean factors and conjunction

All statements concern exact Boolean evaluation.  Satisfiability is reflected
through equality to `true`, making the semantic layer compatible with finite
truth tables.
-/
namespace PNP

abbrev Factor := Assignment → Bool

def Satisfiable (f : Factor) : Prop := ∃ a, f a = true

def Unsatisfiable (f : Factor) : Prop := ∀ a, f a = false

def truth : Factor := fun _ => true

def falsity : Factor := fun _ => false

def conjunction (f g : Factor) : Factor := fun a => f a && g a

def combine : List Factor → Factor
  | [] => truth
  | f :: fs => conjunction f (combine fs)

@[simp] theorem conjunction_true_iff (f g : Factor) (a : Assignment) :
    conjunction f g a = true ↔ f a = true ∧ g a = true := by
  simp [conjunction]

@[simp] theorem combine_nil (a : Assignment) : combine [] a = true := rfl

@[simp] theorem combine_cons (f : Factor) (fs : List Factor) (a : Assignment) :
    combine (f :: fs) a = (f a && combine fs a) := rfl

theorem combine_true_iff (fs : List Factor) (a : Assignment) :
    combine fs a = true ↔ ∀ f, f ∈ fs → f a = true := by
  induction fs with
  | nil => simp [combine, truth]
  | cons f fs ih => simp [combine, conjunction, ih]

theorem combine_append (fs gs : List Factor) :
    combine (fs ++ gs) = conjunction (combine fs) (combine gs) := by
  funext a
  apply eq_of_true_iff
  simp [combine_true_iff, List.mem_append, or_imp, forall_and,
    conjunction_true_iff]

theorem combine_permutation {fs gs : List Factor} (h : fs.Perm gs) :
    combine fs = combine gs := by
  funext a
  apply eq_of_true_iff
  simp only [combine_true_iff]
  constructor
  · intro hf f hg; exact hf f ((h.mem_iff).mpr hg)
  · intro hg f hf; exact hg f ((h.mem_iff).mp hf)

theorem unsatisfiable_iff_not_satisfiable (f : Factor) :
    Unsatisfiable f ↔ ¬ Satisfiable f := by
  constructor
  · intro h ⟨a, ha⟩
    rw [h a] at ha
    contradiction
  · intro h a
    cases hf : f a
    · rfl
    · exact False.elim (h ⟨a, hf⟩)

theorem truth_satisfiable : Satisfiable truth := ⟨fun _ => false, rfl⟩

theorem falsity_unsatisfiable : Unsatisfiable falsity := by intro a; rfl

end PNP

