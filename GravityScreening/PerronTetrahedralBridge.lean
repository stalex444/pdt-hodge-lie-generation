module
public import GravityScreening.TetrahedralInformationFrame

@[expose] public section

/-!
# Quartic Perron mass versus the normalized tetrahedral record

The quartic Perron vector supplies a structurally fixed four-outcome weight.
The inverse-step residual acts on its eigenline by the exact scalar `lambda4`.
This file proves that normalizing the four weights removes that scalar and
leaves the associated three-coordinate tetrahedral record unchanged.

Consequently `lambda4` is an unnormalized mass/amplitude coefficient in this
model, not a displacement or Fisher-score correlation of the normalized
record.
-/

namespace GravityScreening

/-- The quartic invariant letter-frequency vector. -/
noncomputable def normalizedQuarticPerron (q : ℝ) : Fin 4 → ℝ :=
  fun i => quarticPerronVector q i / quarticPerronMass q

/-- Its entries have total mass one whenever the Perron mass is nonzero. -/
theorem normalizedQuarticPerron_sum
    (q : ℝ) (hmass : quarticPerronMass q ≠ 0) :
    ∑ i, normalizedQuarticPerron q i = 1 := by
  unfold quarticPerronMass at hmass
  simp [normalizedQuarticPerron, quarticPerronVector, quarticPerronMass,
    Fin.sum_univ_four]
  field_simp [hmass]
  ring_nf

/-- The distinguished renewal outcome of the normalized Perron distribution
has weight exactly `lambda4`. -/
theorem normalizedQuarticPerron_renewal_eq_lambda4
    (q : ℝ) (hq : q ^ 4 = q + 1) (hq1 : 1 < q) :
    normalizedQuarticPerron q 0 = lambda4 q := by
  simp [normalizedQuarticPerron, quarticPerronVector]
  simpa [one_div] using quarticRenewalFrequency q hq hq1

/-- The residual acts on the normalized four-weight vector by the same scalar
`lambda4`; normalization does not change the eigenvalue equation. -/
theorem quarticResidual_normalizedPerron
    (q : ℝ) (hq : q ^ 4 = q + 1) (hq1 : 1 < q) :
    quarticResidual.mulVec (normalizedQuarticPerron q) =
      fun i => lambda4 q * normalizedQuarticPerron q i := by
  have hq0 : q ≠ 0 := by linarith
  have hmass : quarticPerronMass q ≠ 0 := by
    unfold quarticPerronMass
    positivity
  funext i
  fin_cases i <;>
    simp [normalizedQuarticPerron, quarticResidual, quarticPerronVector,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
    unfold lambda4 <;>
    field_simp [hq0, hmass] <;>
    nlinarith [hq]

/-- The total residual mass is `lambda4`. -/
theorem quarticResidual_normalizedPerron_sum
    (q : ℝ) (hq : q ^ 4 = q + 1) (hq1 : 1 < q) :
    ∑ i, (quarticResidual.mulVec (normalizedQuarticPerron q)) i = lambda4 q := by
  have hmass : quarticPerronMass q ≠ 0 := by
    unfold quarticPerronMass
    positivity
  rw [quarticResidual_normalizedPerron q hq hq1]
  rw [← Finset.mul_sum]
  rw [normalizedQuarticPerron_sum q hmass]
  ring

/-- If the Perron residual is read as a classical thinning of probability
mass, its complementary mass is `1 / q`, rather than the gravity factor. -/
theorem quarticResidual_classical_complement
    (q : ℝ) (hq : q ^ 4 = q + 1) (hq1 : 1 < q) :
    1 - (∑ i, (quarticResidual.mulVec
      (normalizedQuarticPerron q)) i) = 1 / q := by
  rw [quarticResidual_normalizedPerron_sum q hq hq1]
  unfold lambda4
  ring

/-- For `q > 1`, the classical complement and the Hilbert/Born complement
are genuinely different.  The latter is the screening factor. -/
theorem classicalComplement_ne_BornComplement
    (q : ℝ) (hq1 : 1 < q) :
    1 - lambda4 q ≠ screening (lambda4 q) := by
  have hq0 : q ≠ 0 := by linarith
  intro h
  unfold lambda4 screening at h
  field_simp [hq0] at h
  nlinarith

/-- Renormalizing the residual branch returns exactly the original four
probabilities. -/
theorem quarticResidual_renormalized_eq
    (q : ℝ) (hq : q ^ 4 = q + 1) (hq1 : 1 < q) :
    (fun i =>
      (quarticResidual.mulVec (normalizedQuarticPerron q)) i / lambda4 q) =
        normalizedQuarticPerron q := by
  have hlambda : lambda4 q ≠ 0 := by
    have hq0 : q ≠ 0 := by linarith
    rw [lambda4_eq_relative_increment q hq0]
    exact div_ne_zero (by linarith) hq0
  rw [quarticResidual_normalizedPerron q hq hq1]
  funext i
  field_simp [hlambda]

/-- Therefore the three-coordinate tetrahedral record is invariant after
conditioning on the residual branch. -/
theorem quarticResidual_tetraRecord_invariant
    (q : ℝ) (hq : q ^ 4 = q + 1) (hq1 : 1 < q) :
    tetraRecord
        (fun i =>
          (quarticResidual.mulVec (normalizedQuarticPerron q)) i / lambda4 q) =
      tetraRecord (normalizedQuarticPerron q) := by
  rw [quarticResidual_renormalized_eq q hq hq1]

/-! ## Scalar Hilbert branch followed by tetrahedral readout -/

/-- Unconditioned outcome weights after a scalar Hilbert-space branch of
amplitude `a`.  Born weights acquire the square `a^2`. -/
def scalarOutcomeBranch
    (a : ℝ) (weight : Fin 4 → ℝ) (i : Fin 4) : ℝ :=
  a ^ 2 * weight i

/-- A normalized four-outcome distribution has total branch weight `a^2`. -/
theorem scalarOutcomeBranch_sum
    (a : ℝ) (weight : Fin 4 → ℝ) (hsum : ∑ i, weight i = 1) :
    ∑ i, scalarOutcomeBranch a weight i = a ^ 2 := by
  simp only [scalarOutcomeBranch, ← Finset.mul_sum, hsum, mul_one]

/-- Conditioning on any nonzero scalar branch restores every outcome
probability.  Hence a normalized Fisher metric cannot detect the scalar. -/
theorem scalarOutcomeBranch_renormalizes
    (a : ℝ) (weight : Fin 4 → ℝ) (ha : a ≠ 0) :
    (fun i => scalarOutcomeBranch a weight i / a ^ 2) = weight := by
  funext i
  unfold scalarOutcomeBranch
  field_simp [ha]

/-- On the quartic Perron state, the residual amplitude gives total Born
weight `lambda4^2`; its complementary unconditioned weight is exactly `S_Q`. -/
theorem quarticPerron_BornBranch_split
    (q : ℝ) (_hq : q ^ 4 = q + 1) (hq1 : 1 < q) :
    (∑ i, scalarOutcomeBranch (lambda4 q)
        (normalizedQuarticPerron q) i = lambda4 q ^ 2) ∧
      1 - (∑ i, scalarOutcomeBranch (lambda4 q)
        (normalizedQuarticPerron q) i) = screening (lambda4 q) := by
  have hmass : quarticPerronMass q ≠ 0 := by
    unfold quarticPerronMass
    positivity
  have hsum := normalizedQuarticPerron_sum q hmass
  rw [scalarOutcomeBranch_sum (lambda4 q)
    (normalizedQuarticPerron q) hsum]
  exact ⟨rfl, rfl⟩

/-- Conditional tetrahedral readout is unchanged by the nonzero quartic
scalar branch. -/
theorem quarticPerron_BornBranch_tetraRecord_invariant
    (q : ℝ) (hq1 : 1 < q) :
    tetraRecord
        (fun i => scalarOutcomeBranch (lambda4 q)
          (normalizedQuarticPerron q) i / lambda4 q ^ 2) =
      tetraRecord (normalizedQuarticPerron q) := by
  have hq0 : q ≠ 0 := by linarith
  have hlambda : lambda4 q ≠ 0 := by
    rw [lambda4_eq_relative_increment q hq0]
    exact div_ne_zero (by linarith) hq0
  rw [scalarOutcomeBranch_renormalizes
    (lambda4 q) (normalizedQuarticPerron q) hlambda]

#print axioms GravityScreening.normalizedQuarticPerron_sum
#print axioms GravityScreening.normalizedQuarticPerron_renewal_eq_lambda4
#print axioms GravityScreening.quarticResidual_normalizedPerron
#print axioms GravityScreening.quarticResidual_normalizedPerron_sum
#print axioms GravityScreening.quarticResidual_classical_complement
#print axioms GravityScreening.classicalComplement_ne_BornComplement
#print axioms GravityScreening.quarticResidual_renormalized_eq
#print axioms GravityScreening.quarticResidual_tetraRecord_invariant
#print axioms GravityScreening.scalarOutcomeBranch_sum
#print axioms GravityScreening.scalarOutcomeBranch_renormalizes
#print axioms GravityScreening.quarticPerron_BornBranch_split
#print axioms GravityScreening.quarticPerron_BornBranch_tetraRecord_invariant

end GravityScreening
