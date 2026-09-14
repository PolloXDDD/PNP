import Std

/-! Elementary Boolean reflection lemmas used by the executable semantics. -/
namespace PNP

@[simp] theorem and_true_iff (p q : Bool) :
    (p && q) = true ↔ p = true ∧ q = true := by
  cases p <;> cases q <;> decide

@[simp] theorem or_true_iff (p q : Bool) :
    (p || q) = true ↔ p = true ∨ q = true := by
  cases p <;> cases q <;> decide

theorem eq_of_true_iff (p q : Bool) (h : p = true ↔ q = true) : p = q := by
  cases p <;> cases q <;> simp_all

theorem bool_cases_exists (p : Bool → Prop) :
    (∃ b, p b) ↔ p false ∨ p true := by
  constructor
  · rintro ⟨b, hb⟩
    cases b
    · exact Or.inl hb
    · exact Or.inr hb
  · intro h
    cases h with
    | inl hf => exact ⟨false, hf⟩
    | inr ht => exact ⟨true, ht⟩

end PNP
