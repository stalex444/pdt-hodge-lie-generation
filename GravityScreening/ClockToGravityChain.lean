module
public import GravityScreening.ClockHodgeBridge
public import GravityScreening.ClockForcesConstitutive
public import GravityScreening.DoubledSpinTwoOperator

@[expose] public section

/-!
# From the quartic clock action to the screened spin-two equation

This file isolates the remaining physical placement premise.  The premise
does not assume a matrix coefficient: it says that the orientation-even
gravitational channel carries the same action on the exponential area weight
as one quartic clock translation.  The clock theorem then supplies `1/q`,
exchange symmetry and unit mean normalization force the entire constitutive
block, and elimination of the canonical partner gives the screened sourced
operator equation.

The identification of this even channel with the physical gravitational
prepotential pair is not a mathematical consequence of the quartic
polynomial.  Everything following that explicitly named premise is.
-/

namespace GravityScreening

/-- The gravitational even channel realizes the pullback of one clock
translation on the exponential area weight.  This is the single physical
placement premise used below. -/
def ClockActsOnEvenChannel
    (M : Matrix (Fin 2) (Fin 2) ℝ) (q : ℝ) : Prop :=
  ∀ x,
    M.mulVec ![areaBoltzmannWeight x, areaBoltzmannWeight x] =
      ![dualTranslationPullback (Real.log q) areaBoltzmannWeight x,
        dualTranslationPullback (Real.log q) areaBoltzmannWeight x]

/-- The clock-placement premise implies the retained even-channel weight
`1/q`; it need not be assumed separately. -/
theorem clockAction_implies_evenCoreWeight
    (M : Matrix (Fin 2) (Fin 2) ℝ) (q : ℝ) (hq : 0 < q)
    (hclock : ClockActsOnEvenChannel M q) :
    HasEvenCoreWeight M q := by
  unfold HasEvenCoreWeight
  have hzero := hclock 0
  rw [areaBoltzmannWeight_dualTranslation_log q 0 hq] at hzero
  simpa [areaBoltzmannWeight] using hzero

/-- Calibration theorem: because the exponential weight never vanishes and
the matrix action is linear, realizing the clock translation on every equal
input is exactly equivalent to assigning the even channel the weight `1/q`.
The clock-action language therefore exposes the physical premise dynamically;
it does not weaken that premise mathematically. -/
theorem clockAction_iff_evenCoreWeight
    (M : Matrix (Fin 2) (Fin 2) ℝ) (q : ℝ) (hq : 0 < q) :
    ClockActsOnEvenChannel M q ↔ HasEvenCoreWeight M q := by
  constructor
  · exact clockAction_implies_evenCoreWeight M q hq
  · intro hcore x
    unfold HasEvenCoreWeight at hcore
    have hcore0 := congrFun hcore (0 : Fin 2)
    have hcore1 := congrFun hcore (1 : Fin 2)
    rw [areaBoltzmannWeight_dualTranslation_log q x hq]
    ext i
    fin_cases i
    · simp [one_div, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
        at hcore0 ⊢
      calc
        M 0 0 * areaBoltzmannWeight x +
            M 0 1 * areaBoltzmannWeight x =
          (M 0 0 + M 0 1) * areaBoltzmannWeight x := by ring
        _ = q⁻¹ * areaBoltzmannWeight x := by rw [hcore0]
    · simp [one_div, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
        at hcore1 ⊢
      calc
        M 1 0 * areaBoltzmannWeight x +
            M 1 1 * areaBoltzmannWeight x =
          (M 1 0 + M 1 1) * areaBoltzmannWeight x := by ring
        _ = q⁻¹ * areaBoltzmannWeight x := by rw [hcore1]

/-- For a positive quartic root, the clock action, channel exchange symmetry,
and unit mean normalization force the complete constitutive block.  The same
coefficient is independently the renewal frequency and the normalized
left/right Perron residual. -/
theorem quarticClock_forces_constitutive_chain
    (M : Matrix (Fin 2) (Fin 2) ℝ) (q : ℝ)
    (hq4 : q ^ 4 = q + 1) (hq1 : 1 < q)
    (hexchange : IsChannelExchangeSymmetric M)
    (hmean : HasUnitDiagonalMean M)
    (hclock : ClockActsOnEvenChannel M q) :
    M = constitutiveBlock (lambda4 q) ∧
      Matrix.det M = (2 * q - 1) / q ^ 2 ∧
      lambda4 q = 1 / quarticPerronMass q ∧
      lambda4 q = quarticBiResidualCoefficient q ∧
      0 < Matrix.det M := by
  have hqpos : 0 < q := by linarith
  have hq0 : q ≠ 0 := ne_of_gt hqpos
  have hcore : HasEvenCoreWeight M q :=
    clockAction_implies_evenCoreWeight M q hqpos hclock
  have hmatrix : M = constitutiveBlock (lambda4 q) :=
    clockWeight_forces_constitutiveBlock M q hexchange hmean hcore
  have hdet : Matrix.det M = (2 * q - 1) / q ^ 2 :=
    clockWeight_forced_quartic_det M q hq0 hexchange hmean hcore
  refine ⟨hmatrix, hdet, ?_, ?_, ?_⟩
  · exact (quarticRenewalFrequency q hq4 hq1).symm
  · exact (quarticBiResidualCoefficient_eq_lambda4 q hq4 hq1).symm
  · rw [hdet]
    have hnum : 0 < 2 * q - 1 := by linarith
    have hden : 0 < q ^ 2 := by positivity
    exact div_pos hnum hden

section SourcedOperator

variable {V W : Type*}
variable [AddCommGroup V] [Module ℝ V]
variable [AddCommGroup W] [Module ℝ W]

/-- Capstone source equation.  Once the clock is placed on the even
gravitational channel, no additional mixing coefficient occurs: the forced
quartic block reduces the complete sourced linear operator by the exact
factor `(2*q-1)/q^2`. -/
theorem quarticClock_forces_screened_sourceEquation
    (M : Matrix (Fin 2) (Fin 2) ℝ) (q : ℝ)
    (hq4 : q ^ 4 = q + 1) (hq1 : 1 < q)
    (hexchange : IsChannelExchangeSymmetric M)
    (hmean : HasUnitDiagonalMean M)
    (hclock : ClockActsOnEvenChannel M q)
    (E : V →ₗ[ℝ] W) (field partner : V) (source : W)
    (hequations :
      doubledOperatorElectric (lambda4 q) E field partner = source ∧
        doubledOperatorMagnetic (lambda4 q) E field partner = 0) :
    M = constitutiveBlock (lambda4 q) ∧
      Matrix.det M = (2 * q - 1) / q ^ 2 ∧
      ((2 * q - 1) / q ^ 2) • E field = source ∧
      E partner = lambda4 q • E field := by
  have hchain := quarticClock_forces_constitutive_chain
    M q hq4 hq1 hexchange hmean hclock
  have hq0 : q ≠ 0 := by linarith
  have hreduce :=
    (quartic_doubledLinearOperator_sourceReduction
      q E field partner source hq0).mp hequations
  exact ⟨hchain.1, hchain.2.1, hreduce.1, hreduce.2⟩

end SourcedOperator

#print axioms GravityScreening.clockAction_implies_evenCoreWeight
#print axioms GravityScreening.clockAction_iff_evenCoreWeight
#print axioms GravityScreening.quarticClock_forces_constitutive_chain
#print axioms GravityScreening.quarticClock_forces_screened_sourceEquation

end GravityScreening
