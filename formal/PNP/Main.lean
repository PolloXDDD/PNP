import Std

/-!
# Exact Boolean existential elimination

This is the initial semantic kernel.  It proves the exactness of eliminating one
Boolean variable.  It does not assert a polynomial bound on factor table size.
-/
namespace PNP

abbrev Assignment := Nat → Bool
abbrev Factor := Assignment → Bool

def set (a : Assignment) (i : Nat) (b : Bool) : Assignment :=
  fun j => if j = i then b else a j

def project (i : Nat) (f : Factor) : Factor :=
  fun a => f (set a i false) || f (set a i true)

def Satisfiable (f : Factor) : Prop := ∃ a, f a = true

theorem project_true_iff (i : Nat) (f : Factor) (a : Assignment) :
    project i f a = true ↔ ∃ b : Bool, f (set a i b) = true := by
  cases h0 : f (set a i false) <;> cases h1 : f (set a i true) <;>
    simp [project, h0, h1]

end PNP
