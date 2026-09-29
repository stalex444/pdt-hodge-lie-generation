module
public import GravityScreening.CubicGraphKMSData
public import GravityScreening.RhoQModularIndependence
public import GravityScreening.UnifiedCouplingGrammar

@[expose] public section

/-!
# The joint cubic--quartic modular flow

The cubic and quartic graph clocks combine by tensor-product multiplication.
The synchronized one-step ratio is `1/(rho*q)` and the real-time frequency is
`log (rho*q)`.  Their separate logarithmic frequencies remain incommensurate.
-/

namespace GravityScreening

/-- Product of the cubic and quartic analytic modular multipliers. -/
noncomputable def rhoQJointModularAnalyticFlow
    (rho q : ℝ) (z : ℂ) : ℂ :=
  quarticModularAnalyticFlow rho z * quarticModularAnalyticFlow q z

/-- The product flow is exactly the analytic flow at the joint `rho*q` scale. -/
theorem rhoQJointModularAnalyticFlow_eq_productScale
    (rho q : ℝ) (hrho : 0 < rho) (hq : 0 < q) (z : ℂ) :
    rhoQJointModularAnalyticFlow rho q z =
      quarticModularAnalyticFlow (rho * q) z := by
  unfold rhoQJointModularAnalyticFlow quarticModularAnalyticFlow
  rw [← Complex.exp_add, Real.log_mul hrho.ne' hq.ne']
  congr 1
  push_cast
  ring

/-- The joint flow remains unitary on the real modular-time axis. -/
theorem rhoQJointModularAnalyticFlow_real_norm
    (rho q t : ℝ) :
    ‖rhoQJointModularAnalyticFlow rho q (t : ℂ)‖ = 1 := by
  rw [rhoQJointModularAnalyticFlow, norm_mul,
    quarticModularAnalyticFlow_real_norm,
    quarticModularAnalyticFlow_real_norm, one_mul]

/-- A synchronized negative-imaginary step has the joint inverse ratio
`1/(rho*q)`. -/
theorem rhoQJointModularAnalyticFlow_imaginaryStep
    (rho q : ℝ) (hrho : 0 < rho) (hq : 0 < q) :
    rhoQJointModularAnalyticFlow rho q (-Complex.I) =
      ((1 / (rho * q) : ℝ) : ℂ) := by
  rw [rhoQJointModularAnalyticFlow,
    quarticModularAnalyticFlow_imaginaryStep rho hrho,
    quarticModularAnalyticFlow_imaginaryStep q hq]
  norm_cast
  field_simp

/-- The synchronized real-time frequency is the logarithm of the PDT joint
ruler. -/
theorem rhoQJointModularAnalyticFlow_real_tick
    (rho q : ℝ) (hrho : 0 < rho) (hq : 0 < q) :
    rhoQJointModularAnalyticFlow rho q 1 =
      Complex.exp (((-Real.log (rho * q) : ℝ) : ℂ) * Complex.I) := by
  rw [rhoQJointModularAnalyticFlow_eq_productScale rho q hrho hq]
  exact quarticModularAnalyticFlow_real_tick (rho * q)

/-- One joint inverse modular ratio is the inverse of the common `rho*q`
scale. -/
theorem cubicQuarticConnesParameters_mul
    (rho q : ℝ) (hrho : 0 < rho) (hq : 0 < q) :
    cubicConnesParameter rho * quarticConnesParameter q =
      1 / (rho * q) := by
  rw [cubicConnesParameter_eq_inv rho hrho,
    quarticConnesParameter_eq_inv q hq]
  field_simp

/-- Combined arithmetic/modular capstone: the two graph clocks are
incommensurate, their joint real-time flow is unitary, and their synchronized
imaginary step is the inverse `rho*q` ruler. -/
theorem rhoQ_modularCompletion_capstone
    (rho q t : ℝ)
    (hrho3 : rho ^ 3 = rho + 1) (hrho1 : 1 < rho)
    (hq4 : q ^ 4 = q + 1) (hq1 : 1 < q) :
    Irrational (Real.log rho / Real.log q) ∧
      ‖rhoQJointModularAnalyticFlow rho q (t : ℂ)‖ = 1 ∧
      rhoQJointModularAnalyticFlow rho q (-Complex.I) =
        ((1 / (rho * q) : ℝ) : ℂ) := by
  have hrho : 0 < rho := lt_trans zero_lt_one hrho1
  have hq : 0 < q := lt_trans zero_lt_one hq1
  exact ⟨rhoQ_log_ratio_irrational hrho3 hrho1 hq4 hq1,
    rhoQJointModularAnalyticFlow_real_norm rho q t,
    rhoQJointModularAnalyticFlow_imaginaryStep rho q hrho hq⟩

/-- The joint modular step, the `rho*q` exponent block, and the separate
quartic screening block coexist in one exact statement.  The displayed
gravitational interpretation of the determinant remains the proposal recorded
by `UnifiedCouplingGrammar`. -/
theorem rhoQ_modularGravityDenominator_capstone
    (rho q : ℝ) (hrho : 0 < rho) (hq : 0 < q) :
    rhoQJointModularAnalyticFlow rho q (-Complex.I) =
        ((1 / (rho * q) : ℝ) : ℂ) ∧
      Matrix.det
          (scalarResponseMatrix gravitationalExponent (rho * q)) *
        Matrix.det (constitutiveBlock (lambda4 q)) =
          (rho * q) ^ gravitationalExponent *
            screening (lambda4 q) := by
  exact ⟨rhoQJointModularAnalyticFlow_imaginaryStep rho q hrho hq,
    quarticCombinedResponse_det rho q⟩

#print axioms GravityScreening.rhoQJointModularAnalyticFlow_eq_productScale
#print axioms GravityScreening.rhoQJointModularAnalyticFlow_imaginaryStep
#print axioms GravityScreening.cubicQuarticConnesParameters_mul
#print axioms GravityScreening.rhoQ_modularCompletion_capstone
#print axioms GravityScreening.rhoQ_modularGravityDenominator_capstone

end GravityScreening
