import PNP.Projection

/-!
# Finite support and locality

A support is an explicit list of variable identifiers. Lists may contain
repetitions: none of the semantic theorems assume a hidden uniqueness invariant.
-/
namespace PNP

def Supported (s : List Nat) (f : Factor) : Prop :=
  ∀ a b, AgreeOn s a b → f a = f b

theorem supported_mono {s t : List Nat} {f : Factor}
    (h : Supported s f) (hst : ∀ i, i ∈ s → i ∈ t) : Supported t f := by
  intro a b hab
  exact h a b (agreeOn_mono hst hab)

theorem supported_truth (s : List Nat) : Supported s truth := by
  intro a b h; rfl

theorem supported_falsity (s : List Nat) : Supported s falsity := by
  intro a b h; rfl

theorem supported_conjunction {s t : List Nat} {f g : Factor}
    (hf : Supported s f) (hg : Supported t g) :
    Supported (s ++ t) (conjunction f g) := by
  intro a b hab
  obtain ⟨hs, ht⟩ := agreeOn_append.mp hab
  simp [conjunction, hf a b hs, hg a b ht]

def eraseVar (i : Nat) (s : List Nat) : List Nat := s.filter (fun j => j != i)

@[simp] theorem mem_eraseVar (i j : Nat) (s : List Nat) :
    j ∈ eraseVar i s ↔ j ∈ s ∧ j ≠ i := by
  simp [eraseVar]

@[simp] theorem not_mem_eraseVar (i : Nat) (s : List Nat) :
    i ∉ eraseVar i s := by simp

theorem agreeOn_set_pair {s : List Nat} {a b : Assignment} (i : Nat) (v : Bool)
    (h : AgreeOn (eraseVar i s) a b) : AgreeOn s (set a i v) (set b i v) := by
  intro j hj
  by_cases he : j = i
  · subst j; simp
  · simp only [set_other _ _ _ _ he]
    exact h j ((mem_eraseVar i j s).mpr ⟨hj, he⟩)

theorem supported_project {s : List Nat} {f : Factor} (i : Nat)
    (h : Supported s f) : Supported (eraseVar i s) (project i f) := by
  intro a b hab
  have hf := h (set a i false) (set b i false) (agreeOn_set_pair i false hab)
  have ht := h (set a i true) (set b i true) (agreeOn_set_pair i true hab)
  simp [project, hf, ht]

theorem supported_set_absent {s : List Nat} {f : Factor}
    (h : Supported s f) (i : Nat) (hi : i ∉ s) (a : Assignment) (b : Bool) :
    f (set a i b) = f a := by
  exact h _ _ (agreeOn_set_absent a i b hi)

theorem project_absent {s : List Nat} {f : Factor}
    (h : Supported s f) (i : Nat) (hi : i ∉ s) : project i f = f := by
  funext a
  simp [project, supported_set_absent h i hi]

theorem supported_nil_constant {f : Factor} (h : Supported [] f)
    (a b : Assignment) : f a = f b := by
  apply h a b
  intro i hi
  simp at hi

theorem supported_nil_sat_iff {f : Factor} (h : Supported [] f) (a : Assignment) :
    Satisfiable f ↔ f a = true := by
  constructor
  · rintro ⟨b, hb⟩
    rw [← supported_nil_constant h b a]
    exact hb
  · exact fun ha => ⟨a, ha⟩

end PNP
