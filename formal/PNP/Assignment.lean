import Std

/-!
# Assignments and single-coordinate updates

Variables are natural numbers.  A total assignment makes all operations total,
including projections of variables absent from a formula.
-/
namespace PNP

abbrev Assignment := Nat → Bool

def set (a : Assignment) (i : Nat) (b : Bool) : Assignment :=
  fun j => if j = i then b else a j

@[simp] theorem set_same (a : Assignment) (i : Nat) (b : Bool) :
    set a i b i = b := by simp [set]

@[simp] theorem set_other (a : Assignment) (i j : Nat) (b : Bool) (h : j ≠ i) :
    set a i b j = a j := by simp [set, h]

@[simp] theorem set_current (a : Assignment) (i : Nat) : set a i (a i) = a := by
  funext j
  by_cases h : j = i
  · subst j; simp
  · simp [set, h]

@[simp] theorem set_overwrite (a : Assignment) (i : Nat) (b c : Bool) :
    set (set a i b) i c = set a i c := by
  funext j
  by_cases h : j = i <;> simp [set, h]

theorem set_commute (a : Assignment) (i j : Nat) (b c : Bool) (h : i ≠ j) :
    set (set a i b) j c = set (set a j c) i b := by
  funext k
  by_cases hi : k = i
  · subst k; simp [set, h]
  · by_cases hj : k = j
    · subst k; simp [set, hi]
    · simp [set, hi, hj]

def AgreeOn (s : List Nat) (a b : Assignment) : Prop :=
  ∀ i, i ∈ s → a i = b i

theorem agreeOn_refl (s : List Nat) (a : Assignment) : AgreeOn s a a := by
  intro i hi; rfl

theorem agreeOn_symm {s : List Nat} {a b : Assignment} (h : AgreeOn s a b) :
    AgreeOn s b a := by intro i hi; exact (h i hi).symm

theorem agreeOn_trans {s : List Nat} {a b c : Assignment}
    (hab : AgreeOn s a b) (hbc : AgreeOn s b c) : AgreeOn s a c := by
  intro i hi; exact (hab i hi).trans (hbc i hi)

theorem agreeOn_mono {s t : List Nat} {a b : Assignment}
    (hst : ∀ i, i ∈ s → i ∈ t) (h : AgreeOn t a b) : AgreeOn s a b := by
  intro i hi; exact h i (hst i hi)

theorem agreeOn_append {s t : List Nat} {a b : Assignment} :
    AgreeOn (s ++ t) a b ↔ AgreeOn s a b ∧ AgreeOn t a b := by
  simp [AgreeOn, List.mem_append, or_imp, forall_and]

theorem agreeOn_set_absent {s : List Nat} (a : Assignment) (i : Nat) (b : Bool)
    (hi : i ∉ s) : AgreeOn s (set a i b) a := by
  intro j hj
  apply set_other
  intro hji
  subst j
  exact hi hj

end PNP
