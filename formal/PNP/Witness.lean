import PNP.Support

/-!
# Constructive witness recovery

The stored choice is false whenever the false cofactor succeeds, otherwise true.
Its correctness requires a successful projected factor. An unsuccessful
projection never licenses a satisfying-assignment claim.
-/
namespace PNP

def chooseBit (i : Nat) (f : Factor) (a : Assignment) : Bool :=
  if f (set a i false) then false else true

def recover (i : Nat) (f : Factor) (a : Assignment) : Assignment :=
  set a i (chooseBit i f a)

theorem chooseBit_sound (i : Nat) (f : Factor) (a : Assignment)
    (h : project i f a = true) : f (set a i (chooseBit i f a)) = true := by
  cases h0 : f (set a i false)
  · have h1 : f (set a i true) = true := by simpa [project, h0] using h
    simpa [chooseBit, h0] using h1
  · simpa [chooseBit, h0] using h0

theorem recover_sound (i : Nat) (f : Factor) (a : Assignment)
    (h : project i f a = true) : f (recover i f a) = true :=
  chooseBit_sound i f a h

@[simp] theorem recover_other (i j : Nat) (f : Factor) (a : Assignment)
    (h : j ≠ i) : recover i f a j = a j := by simp [recover, h]

@[simp] theorem recover_at (i : Nat) (f : Factor) (a : Assignment) :
    recover i f a i = chooseBit i f a := by simp [recover]

theorem recover_preserves_projection (i : Nat) (f : Factor) (a : Assignment) :
    project i f (recover i f a) = project i f a := by simp [recover]

theorem chooseBit_prefers_false (i : Nat) (f : Factor) (a : Assignment)
    (h : f (set a i false) = true) : chooseBit i f a = false := by
  simp [chooseBit, h]

theorem chooseBit_uses_true (i : Nat) (f : Factor) (a : Assignment)
    (h : f (set a i false) = false) : chooseBit i f a = true := by
  simp [chooseBit, h]

theorem recover_agreeOn_absent (i : Nat) (f : Factor) (a : Assignment)
    (s : List Nat) (h : i ∉ s) : AgreeOn s (recover i f a) a := by
  exact agreeOn_set_absent a i (chooseBit i f a) h

end PNP
