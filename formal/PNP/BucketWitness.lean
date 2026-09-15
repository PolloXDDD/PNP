import PNP.Bucket

/-!
# Reconstructing from stored bucket choices

A bucket's local witness restores the eliminated variable. Every factor outside
the bucket keeps its previous value, so the recovered bit satisfies the entire
preceding factor collection. This validates the reverse direction of the
implementation's witness trace.
-/
namespace PNP

def recoverBucket (i : Nat) (fs : List ScopedFactor) (a : Assignment) : Assignment :=
  recover i (evalFactors (inBucket i fs)) a

theorem recoverBucket_sound (i : Nat) (fs : List ScopedFactor) (a : Assignment)
    (h : evalFactors (bucketStep i fs) a = true) :
    evalFactors fs (recoverBucket i fs a) = true := by
  have hs : project i (evalFactors (inBucket i fs)) a = true ∧
      evalFactors (outsideBucket i fs) a = true := by
    exact (and_true_iff _ _).mp h
  rw [bucket_partition i fs, conjunction_true_iff]
  constructor
  · exact recover_sound i _ a hs.1
  · simpa [recoverBucket, recover, outside_bucket_invariant] using hs.2

theorem recoverBucket_other (i j : Nat) (fs : List ScopedFactor) (a : Assignment)
    (h : j ≠ i) : recoverBucket i fs a j = a j := by
  exact recover_other i j _ a h

def runBuckets : List Nat → List ScopedFactor → List ScopedFactor
  | [], fs => fs
  | i :: is, fs => runBuckets is (bucketStep i fs)

def reconstructBuckets : List Nat → List ScopedFactor → Assignment → Assignment
  | [], _, a => a
  | i :: is, fs, a => recoverBucket i fs (reconstructBuckets is (bucketStep i fs) a)

theorem runBuckets_exact (is : List Nat) (fs : List ScopedFactor) :
    evalFactors (runBuckets is fs) = eliminate is (evalFactors fs) := by
  induction is generalizing fs with
  | nil => rfl
  | cons i is ih =>
    simp only [runBuckets, eliminate_cons, ih, bucketStep_exact]

theorem runBuckets_satisfiable_iff (is : List Nat) (fs : List ScopedFactor) :
    Satisfiable (evalFactors (runBuckets is fs)) ↔ Satisfiable (evalFactors fs) := by
  rw [runBuckets_exact, eliminate_satisfiable_iff]

theorem runBuckets_unsatisfiable_iff (is : List Nat) (fs : List ScopedFactor) :
    Unsatisfiable (evalFactors (runBuckets is fs)) ↔ Unsatisfiable (evalFactors fs) := by
  rw [runBuckets_exact, eliminate_unsatisfiable_iff]

theorem reconstructBuckets_sound (is : List Nat) (fs : List ScopedFactor)
    (a : Assignment) (h : evalFactors (runBuckets is fs) a = true) :
    evalFactors fs (reconstructBuckets is fs a) = true := by
  induction is generalizing fs with
  | nil => exact h
  | cons i is ih =>
    exact recoverBucket_sound i fs _ (ih (bucketStep i fs) h)

theorem reconstructBuckets_other (is : List Nat) (fs : List ScopedFactor)
    (a : Assignment) (j : Nat) (h : j ∉ is) :
    reconstructBuckets is fs a j = a j := by
  induction is generalizing fs with
  | nil => rfl
  | cons i is ih =>
    have hji : j ≠ i := by intro he; subst j; exact h (by simp)
    have hj : j ∉ is := by intro hj; exact h (by simp [hj])
    change recoverBucket i fs (reconstructBuckets is (bucketStep i fs) a) j = a j
    rw [recoverBucket_other i j fs _ hji, ih (bucketStep i fs) hj]

theorem bucket_decision_iff (is : List Nat) (fs : List ScopedFactor)
    (hc : ∀ j, j ∈ unionScope fs → j ∈ is) (a : Assignment) :
    evalFactors (runBuckets is fs) a = true ↔ Satisfiable (evalFactors fs) := by
  rw [runBuckets_exact]
  exact elimination_decision_iff is (supported_evalFactors fs) hc a

end PNP
