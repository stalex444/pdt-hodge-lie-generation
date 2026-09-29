module
public import GravityScreening.RhoQModularCompletion

@[expose] public section

/-!
# Fixed two-pi normalization of the joint modular clock

For a wedge algebra satisfying the Bisognano--Wichmann convention,
modular time `t` is geometric boost rapidity `-2*pi*t`.  This file proves
that the joint `rho*Q` modular phase therefore has the unique boost weight
`log (rho*Q)/(2*pi)`.

The theorem is an exact normalization identity.  It does not assert that the
graph product representation is a physical wedge algebra; that is the
remaining spacetime correspondence.
-/

namespace GravityScreening

/-- Geometric boost rapidity in the Bisognano--Wichmann sign convention
`Delta^(i t) = U(Lambda(-2*pi*t))`. -/
noncomputable def wedgeBoostRapidity (t : ℝ) : ℝ :=
  -2 * Real.pi * t

/-- Boost spectral weight forced by the joint modular eigenvalue. -/
noncomputable def rhoQBoostWeight (rho q : ℝ) : ℝ :=
  Real.log (rho * q) / (2 * Real.pi)

/-- Scalar phase of a boost eigenmode with weight `omega` and rapidity
`eta`. -/
noncomputable def boostEigenphase (omega eta : ℝ) : ℂ :=
  Complex.exp (((omega * eta : ℝ) : ℂ) * Complex.I)

/-- The fixed boost weight times the fixed rapidity is exactly the modular
phase angle.  No adjustable normalization remains. -/
theorem rhoQBoostWeight_mul_rapidity
    (rho q t : ℝ) :
    rhoQBoostWeight rho q * wedgeBoostRapidity t =
      -Real.log (rho * q) * t := by
  unfold rhoQBoostWeight wedgeBoostRapidity
  field_simp [Real.pi_ne_zero]

/-- For positive roots, the joint modular flow is exactly the boost
eigenphase at the Bisognano--Wichmann rapidity. -/
theorem rhoQJointModularAnalyticFlow_eq_boostEigenphase
    (rho q t : ℝ) (hrho : 0 < rho) (hq : 0 < q) :
    rhoQJointModularAnalyticFlow rho q (t : ℂ) =
      boostEigenphase (rhoQBoostWeight rho q) (wedgeBoostRapidity t) := by
  rw [rhoQJointModularAnalyticFlow_eq_productScale rho q hrho hq]
  unfold quarticModularAnalyticFlow boostEigenphase
  rw [rhoQBoostWeight_mul_rapidity]
  congr 1
  push_cast
  ring

/-- The joint boost weight is positive in the positive-root regime. -/
theorem rhoQBoostWeight_pos
    (rho q : ℝ) (hrho : 1 < rho) (hq : 1 < q) :
    0 < rhoQBoostWeight rho q := by
  have hcross : 0 < (rho - 1) * (q - 1) :=
    mul_pos (sub_pos.mpr hrho) (sub_pos.mpr hq)
  have hprod : 1 < rho * q := by nlinarith
  exact div_pos (Real.log_pos hprod) (by positivity)

/-- Fixed-normalization capstone: the same joint flow is a real boost phase,
has inverse `rho*Q` imaginary step, and coexists with the separate quartic
screening determinant.  Only the first equality uses the displayed
Bisognano--Wichmann parameter convention; physical wedge realization remains
an explicit premise outside this theorem. -/
theorem rhoQ_twoPiBoost_gravity_capstone
    (rho q t : ℝ) (hrho : 0 < rho) (hq : 0 < q) :
    rhoQJointModularAnalyticFlow rho q (t : ℂ) =
        boostEigenphase (rhoQBoostWeight rho q) (wedgeBoostRapidity t) ∧
      rhoQJointModularAnalyticFlow rho q (-Complex.I) =
        ((1 / (rho * q) : ℝ) : ℂ) ∧
      Matrix.det
          (scalarResponseMatrix gravitationalExponent (rho * q)) *
        Matrix.det (constitutiveBlock (lambda4 q)) =
          (rho * q) ^ gravitationalExponent * screening (lambda4 q) := by
  exact ⟨rhoQJointModularAnalyticFlow_eq_boostEigenphase rho q t hrho hq,
    rhoQJointModularAnalyticFlow_imaginaryStep rho q hrho hq,
    quarticCombinedResponse_det rho q⟩

#print axioms GravityScreening.rhoQBoostWeight_mul_rapidity
#print axioms GravityScreening.rhoQJointModularAnalyticFlow_eq_boostEigenphase
#print axioms GravityScreening.rhoQBoostWeight_pos
#print axioms GravityScreening.rhoQ_twoPiBoost_gravity_capstone

end GravityScreening
