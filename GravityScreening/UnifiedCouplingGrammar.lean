module
public import GravityScreening.Basic

@[expose] public section

/-!
# A shared determinant grammar for the electromagnetic and gravitational scales

This file isolates the exact algebra behind a compact comparison.  A scalar
response on `n` directions has determinant `scale^n`.  The electromagnetic
denominator uses `n = 15`.  The proposed gravitational denominator uses
`n = 224 = 15^2 - 1`, together with the determinant of the normalized quartic
two-channel block.

The dimension choices and the identification of these determinants with
physical couplings are not proved here.  The results prove the consequences of
those displayed choices without numerical fitting.
-/

namespace GravityScreening

/-- A scalar response on an `n`-dimensional real coordinate space. -/
noncomputable def scalarResponseMatrix (n : ℕ) (scale : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  scale • (1 : Matrix (Fin n) (Fin n) ℝ)

/-- The determinant of a scalar response is one power of the response per
coordinate direction. -/
theorem scalarResponseMatrix_det (n : ℕ) (scale : ℝ) :
    Matrix.det (scalarResponseMatrix n scale) = scale ^ n := by
  simp [scalarResponseMatrix]

/-- The electromagnetic exponent used in the PDT coupling formula. -/
def electromagneticExponent : ℕ := 15

/-- The gravitational exponent used in the PDT coupling formula. -/
def gravitationalExponent : ℕ := 224

/-- The complementary exponent in the exact electromagnetic/gravity split. -/
def gravitationalComplementExponent : ℕ := 209

/-- The gravitational exponent is the traceless-endomorphism dimension of a
15-dimensional vector space. -/
theorem gravitationalExponent_eq_square_sub_one :
    gravitationalExponent = electromagneticExponent ^ 2 - 1 := by
  norm_num [gravitationalExponent, electromagneticExponent]

/-- The same exponent splits into the electromagnetic orbit and its stated
complement. -/
theorem gravitationalExponent_split :
    gravitationalExponent =
      electromagneticExponent + gravitationalComplementExponent := by
  norm_num [gravitationalExponent, electromagneticExponent,
    gravitationalComplementExponent]

/-- The proposed dimensionless electromagnetic coupling. -/
noncomputable def electromagneticCoupling (rho q : ℝ) : ℝ :=
  Real.pi ^ 2 / (rho * q) ^ electromagneticExponent

/-- The proposed dimensionless gravitational coupling, including the quartic
two-channel determinant. -/
noncomputable def gravitationalCoupling (rho q : ℝ) : ℝ :=
  Real.pi ^ 4 /
    ((rho * q) ^ gravitationalExponent * screening (lambda4 q))

/-- The quartic two-channel determinant supplies exactly the extra screening
factor in the gravitational response denominator. -/
theorem quarticCombinedResponse_det (rho q : ℝ) :
    Matrix.det (scalarResponseMatrix gravitationalExponent (rho * q)) *
        Matrix.det (constitutiveBlock (lambda4 q)) =
      (rho * q) ^ gravitationalExponent * screening (lambda4 q) := by
  rw [scalarResponseMatrix_det, constitutiveBlock_det]

/-- Exact alpha-link factorization: after removing the 15-direction
electromagnetic determinant, gravity contains 209 further powers of the common
scale and one quartic two-channel determinant. -/
theorem gravitationalCoupling_eq_electromagnetic_link
    (rho q : ℝ)
    (hscreen : screening (lambda4 q) ≠ 0) :
    gravitationalCoupling rho q =
      electromagneticCoupling rho q * Real.pi ^ 2 /
        ((rho * q) ^ gravitationalComplementExponent *
          screening (lambda4 q)) := by
  unfold gravitationalCoupling electromagneticCoupling
  norm_num [gravitationalExponent, electromagneticExponent,
    gravitationalComplementExponent]
  field_simp [hscreen]

/-- The reciprocal gravitational coupling is the combined determinant divided
by the squared boundary-volume factor. -/
theorem gravitationalCoupling_inverse_eq_combinedResponse
    (rho q : ℝ)
    (hscale : rho * q ≠ 0)
    (hscreen : screening (lambda4 q) ≠ 0) :
    1 / gravitationalCoupling rho q =
      (Matrix.det (scalarResponseMatrix gravitationalExponent (rho * q)) *
        Matrix.det (constitutiveBlock (lambda4 q))) / Real.pi ^ 4 := by
  rw [quarticCombinedResponse_det]
  unfold gravitationalCoupling
  field_simp [hscale, hscreen, Real.pi_ne_zero]

#print axioms GravityScreening.scalarResponseMatrix_det
#print axioms GravityScreening.gravitationalExponent_eq_square_sub_one
#print axioms GravityScreening.gravitationalExponent_split
#print axioms GravityScreening.quarticCombinedResponse_det
#print axioms GravityScreening.gravitationalCoupling_eq_electromagnetic_link
#print axioms GravityScreening.gravitationalCoupling_inverse_eq_combinedResponse

end GravityScreening
