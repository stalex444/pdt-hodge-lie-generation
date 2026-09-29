module
public import GravityScreening.Basic

@[expose] public section

/-!
# Subnormalized horizon branches

The scalar defect channel does not change a normalized conditional state, but
it does change the unconditioned weight of that state in a horizon instrument.
This file checks the resulting entropy-first-law scaling in a finite diagonal
model.  Identifying the retained branch with physical horizon cells remains a
physical premise.
-/

namespace GravityScreening

/-- A branch of amplitude `d` sends a diagonal state perturbation to one with
Born weight `d^2`.  The result is deliberately left subnormalized. -/
def scalarBranchPerturbation {n : ℕ} (d : ℝ) (delta : Fin n → ℝ) :
    Fin n → ℝ :=
  fun i => d ^ 2 * delta i

/-- The entropy first-law pairing on a subnormalized scalar branch is its Born
weight times the input pairing. -/
theorem scalarBranch_firstLaw {n : ℕ} (k delta : Fin n → ℝ) (d : ℝ) :
    firstLawVariation k (scalarBranchPerturbation d delta) =
      d ^ 2 * firstLawVariation k delta := by
  unfold firstLawVariation scalarBranchPerturbation
  simp_rw [show ∀ i, d ^ 2 * delta i * k i = d ^ 2 * (delta i * k i) by
    intro i
    ring]
  exact (Finset.mul_sum Finset.univ (fun i => delta i * k i) (d ^ 2)).symm

/-- If `d` is the complementary amplitude to `l`, the visible branch scales
every first-law variation by `1-l^2`. -/
theorem defectBranch_firstLaw {n : ℕ} (k delta : Fin n → ℝ) (l d : ℝ)
    (hdefect : d ^ 2 = screening l) :
    firstLawVariation k (scalarBranchPerturbation d delta) =
      screening l * firstLawVariation k delta := by
  rw [scalarBranch_firstLaw, hdefect]

/-- At the quartic root, the subnormalized complementary branch carries the
exact factor `(2q-1)/q^2` occurring in the PDT entropy-area density. -/
theorem quarticDefectBranch_firstLaw {n : ℕ} (k delta : Fin n → ℝ)
    (q d : ℝ) (hq0 : q ≠ 0)
    (hdefect : d ^ 2 = screening (lambda4 q)) :
    firstLawVariation k (scalarBranchPerturbation d delta) =
      ((2 * q - 1) / q ^ 2) * firstLawVariation k delta := by
  rw [defectBranch_firstLaw k delta (lambda4 q) d hdefect]
  rw [quartic_screening_identity q hq0]

/-- Renormalizing a nonzero scalar branch removes its common Born weight.
This is the algebraic boundary between conditional state information and an
unconditioned horizon-cell density. -/
theorem scalarBranch_renormalizes {n : ℕ} (delta : Fin n → ℝ) (d : ℝ)
    (hd : d ≠ 0) :
    (fun i => scalarBranchPerturbation d delta i / d ^ 2) = delta := by
  funext i
  simp [scalarBranchPerturbation, hd]

/-! ## Normalized erasure completion

The retained block may be completed by a state-independent erasure flag.  The
total output is normalized, and the fixed binary contribution cancels from
entropy differences.  We prove the diagonal finite-state identity directly.
-/

/-- Shannon entropy of a finite positive diagonal density. -/
noncomputable def diagonalEntropy {n : ℕ} (p : Fin n → ℝ) : ℝ :=
  ∑ i, entropyContribution 1 (p i)

/-- Entropy of the block-diagonal erasure output: a retained block of total
weight `s` and an erasure flag of weight `1-s`. -/
noncomputable def erasureEntropy {n : ℕ} (s : ℝ) (p : Fin n → ℝ) : ℝ :=
  entropyContribution 1 (1 - s) +
    ∑ i, entropyContribution 1 (s * p i)

/-- Scaling one positive diagonal weight separates into its internal entropy
and the state-independent branch contribution. -/
theorem entropyContribution_scale (s x : ℝ) (hs : s ≠ 0) (hx : x ≠ 0) :
    entropyContribution 1 (s * x) =
      s * entropyContribution 1 x - s * x * Real.log s := by
  unfold entropyContribution
  rw [Real.log_mul hs hx]
  ring

/-- Two equally normalized inputs have erasure-output entropy difference
exactly `s` times their input entropy difference.  The erasure flag and binary
mixing entropy cancel because the channel weight is fixed. -/
theorem erasureEntropy_difference {n : ℕ} (s : ℝ) (p r : Fin n → ℝ)
    (hs : s ≠ 0) (hp : ∀ i, p i ≠ 0) (hr : ∀ i, r i ≠ 0)
    (hnorm : ∑ i, p i = ∑ i, r i) :
    erasureEntropy s p - erasureEntropy s r =
      s * (diagonalEntropy p - diagonalEntropy r) := by
  unfold erasureEntropy diagonalEntropy
  have hp_sum :
      (∑ i, entropyContribution 1 (s * p i)) =
        ∑ i, (s * entropyContribution 1 (p i) - s * p i * Real.log s) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact entropyContribution_scale s (p i) hs (hp i)
  have hr_sum :
      (∑ i, entropyContribution 1 (s * r i)) =
        ∑ i, (s * entropyContribution 1 (r i) - s * r i * Real.log s) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact entropyContribution_scale s (r i) hs (hr i)
  rw [hp_sum, hr_sum]
  simp_rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hbranch :
      (∑ i, s * p i * Real.log s) = ∑ i, s * r i * Real.log s := by
    calc
      (∑ i, s * p i * Real.log s) =
          (s * Real.log s) * ∑ i, p i := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = (s * Real.log s) * ∑ i, r i := by rw [hnorm]
      _ = ∑ i, s * r i * Real.log s := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            ring
  rw [hbranch]
  ring

/-- A retained block of weight `s` plus an erasure flag of weight `1-s` has
unit total mass whenever the input does. -/
theorem erasure_mass_normalized {n : ℕ} (s : ℝ) (p : Fin n → ℝ)
    (hnorm : ∑ i, p i = 1) :
    (1 - s) + ∑ i, s * p i = 1 := by
  rw [← Finset.mul_sum, hnorm]
  ring

#print axioms GravityScreening.scalarBranch_firstLaw
#print axioms GravityScreening.defectBranch_firstLaw
#print axioms GravityScreening.quarticDefectBranch_firstLaw
#print axioms GravityScreening.scalarBranch_renormalizes
#print axioms GravityScreening.entropyContribution_scale
#print axioms GravityScreening.erasureEntropy_difference
#print axioms GravityScreening.erasure_mass_normalized

end GravityScreening
