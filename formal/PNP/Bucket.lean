import PNP.ScopedFactor

/-!
# Local bucket elimination

Only factors whose declared scope contains the chosen variable enter its bucket.
The remaining factors are invariant under updates to that variable. This is the
precise algebraic justification for projecting the bucket instead of the entire
conjunction. Scope sizes are not assumed to remain small.
-/
namespace PNP

def inBucket (i : Nat) (fs : List ScopedFactor) : List ScopedFactor :=
  fs.filter (fun f => decide (i ∈ f.scope))

def outsideBucket (i : Nat) (fs : List ScopedFactor) : List ScopedFactor :=
  fs.filter (fun f => decide (i ∉ f.scope))

@[simp] theorem mem_inBucket (i : Nat) (fs : List ScopedFactor) (f : ScopedFactor) :
    f ∈ inBucket i fs ↔ f ∈ fs ∧ i ∈ f.scope := by simp [inBucket]

@[simp] theorem mem_outsideBucket (i : Nat) (fs : List ScopedFactor) (f : ScopedFactor) :
    f ∈ outsideBucket i fs ↔ f ∈ fs ∧ i ∉ f.scope := by simp [outsideBucket]

theorem bucket_partition (i : Nat) (fs : List ScopedFactor) :
    evalFactors fs = conjunction (evalFactors (inBucket i fs))
      (evalFactors (outsideBucket i fs)) := by
  funext a
  apply eq_of_true_iff
  rw [conjunction_true_iff]
  simp only [evalFactors_true_iff]
  constructor
  · intro hf
    exact ⟨fun f h => hf f ((mem_inBucket i fs f).mp h).1,
      fun f h => hf f ((mem_outsideBucket i fs f).mp h).1⟩
  · rintro ⟨hb, ho⟩ f hf
    by_cases hi : i ∈ f.scope
    · exact hb f ((mem_inBucket i fs f).mpr ⟨hf, hi⟩)
    · exact ho f ((mem_outsideBucket i fs f).mpr ⟨hf, hi⟩)

theorem outside_bucket_absent (i : Nat) (fs : List ScopedFactor) :
    i ∉ unionScope (outsideBucket i fs) := by
  intro h
  obtain ⟨f, hf, hi⟩ := (mem_unionScope _ i).mp h
  exact ((mem_outsideBucket i fs f).mp hf).2 hi

theorem outside_bucket_invariant (i : Nat) (fs : List ScopedFactor)
    (a : Assignment) (b : Bool) :
    evalFactors (outsideBucket i fs) (set a i b) =
      evalFactors (outsideBucket i fs) a := by
  exact supported_set_absent (supported_evalFactors _) i (outside_bucket_absent i fs) a b

theorem project_conjunction_invariant (i : Nat) (f g : Factor)
    (h : ∀ a b, g (set a i b) = g a) :
    project i (conjunction f g) = conjunction (project i f) g := by
  funext a
  simp only [project, conjunction, h]
  cases f (set a i false) <;> cases f (set a i true) <;> cases g a <;> rfl

def bucketStep (i : Nat) (fs : List ScopedFactor) : List ScopedFactor :=
  projectedFactor i (mergedFactor (inBucket i fs)) :: outsideBucket i fs

theorem bucketStep_exact (i : Nat) (fs : List ScopedFactor) :
    evalFactors (bucketStep i fs) = project i (evalFactors fs) := by
  rw [bucket_partition i fs]
  rw [project_conjunction_invariant i _ _ (outside_bucket_invariant i fs)]
  rfl

theorem bucketStep_satisfiable_iff (i : Nat) (fs : List ScopedFactor) :
    Satisfiable (evalFactors (bucketStep i fs)) ↔ Satisfiable (evalFactors fs) := by
  rw [bucketStep_exact, project_satisfiable_iff]

theorem bucketStep_unsatisfiable_iff (i : Nat) (fs : List ScopedFactor) :
    Unsatisfiable (evalFactors (bucketStep i fs)) ↔ Unsatisfiable (evalFactors fs) := by
  rw [bucketStep_exact, project_unsatisfiable_iff]

theorem bucketStep_absent (i : Nat) (fs : List ScopedFactor) :
    i ∉ unionScope (bucketStep i fs) := by
  intro h
  obtain ⟨f, hf, hi⟩ := (mem_unionScope _ i).mp h
  simp only [bucketStep, List.mem_cons] at hf
  cases hf with
  | inl he => subst f; exact projectedFactor_absent i _ hi
  | inr ho => exact ((mem_outsideBucket i fs f).mp ho).2 hi

theorem bucketStep_no_new_variables (i j : Nat) (fs : List ScopedFactor)
    (h : j ∈ unionScope (bucketStep i fs)) : j ∈ unionScope fs := by
  obtain ⟨f, hf, hj⟩ := (mem_unionScope _ j).mp h
  simp only [bucketStep, List.mem_cons] at hf
  cases hf with
  | inl he =>
    subst f
    obtain ⟨hb, _⟩ := (mem_eraseVar i j _).mp hj
    obtain ⟨g, hg, hjg⟩ := (mem_unionScope _ j).mp hb
    exact (mem_unionScope fs j).mpr ⟨g, ((mem_inBucket i fs g).mp hg).1, hjg⟩
  | inr ho =>
    exact (mem_unionScope fs j).mpr ⟨f, ((mem_outsideBucket i fs f).mp ho).1, hj⟩

end PNP
