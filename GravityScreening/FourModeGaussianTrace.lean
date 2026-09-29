module
public import GravityScreening.ProjectiveModeShell
public import Mathlib.MeasureTheory.Integral.Gamma

@[expose] public section

/-!
# Four-dimensional radial and Gaussian-trace normalization

This file derives the `pi^2` normalization from an ordinary integral over
four-dimensional Euclidean mode space.  Generalized polar coordinates force
the angular factor `2*pi^2` and radial Jacobian `r^3`.  The standard Gaussian
radial moment is `1/2`, so the four-dimensional Gaussian integral is exactly
`pi^2`.

Consequently, a constant vertex multiplying the raw unit-scale Gaussian
profile acquires exactly the `pi^2` factor in `electromagneticCoupling`.  The
mathematics is unconditional.  Identifying this unnormalized Lebesgue/Gaussian
trace with the physical zero-momentum vertex measure, including the Fourier
convention and dimensional scale, remains a field-theory premise.  The file
also proves the different coefficient obtained with the common
`d^4k/(2*pi)^4` convention.
-/

namespace GravityScreening

noncomputable section

open MeasureTheory MeasureTheory.Measure Set

/-- Generalized polar coordinates in four real mode dimensions.  Both the
angular factor `2*pi^2` and the radial Jacobian `r^3` are forced by Lebesgue
measure. -/
theorem fourMode_radial_integral (f : ℝ → ℝ) :
    (∫ k : FourModeSpace, f ‖k‖) =
      (2 * Real.pi ^ 2) *
        ∫ r in Ioi (0 : ℝ), r ^ 3 * f r := by
  rw [integral_fun_norm_addHaar (μ := (volume : Measure FourModeSpace))]
  simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSubDiff,
    nsmul_eq_mul, smul_eq_mul]
  rw [← fourModeShellMeasure_real_univ, ← mul_assoc]
  have hsphere :
      ((4 : ℕ) : ℝ) *
          (volume : Measure FourModeSpace).real (Metric.ball 0 1) =
        fourModeShellMeasure.real univ := by
    rw [show ((4 : ℕ) : ℝ) = Module.finrank ℝ FourModeSpace by
      simp [FourModeSpace]]
    rw [← Measure.toSphere_real_apply_univ]
    rfl
  rw [hsphere]

/-- The third radial moment of the unit-scale Gaussian is `1/2`. -/
theorem gaussian_radial_moment_three :
    ∫ r in Ioi (0 : ℝ), r ^ 3 * Real.exp (-r ^ 2) = (1 / 2 : ℝ) := by
  have hGamma := integral_rpow_mul_exp_neg_rpow
    (p := (2 : ℝ)) (q := (3 : ℝ)) (by norm_num) (by norm_num)
  norm_num [Real.Gamma_two] at hGamma ⊢
  exact hGamma

/-- The standard unit-scale Gaussian mass in four real dimensions is exactly
`pi^2`. -/
theorem fourMode_gaussian_integral :
    (∫ k : FourModeSpace, Real.exp (-‖k‖ ^ 2)) = Real.pi ^ 2 := by
  calc
    (∫ k : FourModeSpace, Real.exp (-‖k‖ ^ 2)) =
        (2 * Real.pi ^ 2) *
          ∫ r in Ioi (0 : ℝ), r ^ 3 * Real.exp (-r ^ 2) :=
      fourMode_radial_integral (fun r => Real.exp (-r ^ 2))
    _ = Real.pi ^ 2 := by
      rw [gaussian_radial_moment_three]
      ring

/-- With the frequently used QFT convention `d^4k/(2*pi)^4`, the same
Gaussian has mass `1/(16*pi^2)`.  This exposes the normalization convention
that a physical derivation must fix. -/
theorem fourierNormalized_fourMode_gaussian_integral :
    (1 / (2 * Real.pi) ^ 4) *
        (∫ k : FourModeSpace, Real.exp (-‖k‖ ^ 2)) =
      1 / (16 * Real.pi ^ 2) := by
  rw [fourMode_gaussian_integral]
  field_simp [Real.pi_ne_zero]
  ring

/-- A constant zero-momentum vertex weighted by the raw unit-scale Gaussian
profile under Lebesgue measure. -/
noncomputable def gaussianModeVertexIntegral (vertex : ℝ) : ℝ :=
  ∫ k : FourModeSpace, vertex * Real.exp (-‖k‖ ^ 2)

/-- The raw four-dimensional Gaussian trace supplies exactly one factor of
`pi^2` to a constant vertex. -/
theorem gaussianModeVertexIntegral_eq_pi_sq_mul (vertex : ℝ) :
    gaussianModeVertexIntegral vertex = Real.pi ^ 2 * vertex := by
  rw [gaussianModeVertexIntegral, integral_const_mul, fourMode_gaussian_integral]
  ring

/-- The 15-channel scalar vertex under the raw four-dimensional Gaussian trace
reproduces the deposited electromagnetic expression exactly. -/
theorem conformalChannelVertex_gaussianMode_eq_electromagneticCoupling
    (rho q : ℝ) :
    gaussianModeVertexIntegral (conformalChannelVertex rho q) =
      electromagneticCoupling rho q := by
  rw [gaussianModeVertexIntegral_eq_pi_sq_mul]
  simp [conformalChannelVertex, electromagneticCoupling, div_eq_mul_inv]

/-- Conditional gravity factorization through the raw four-dimensional
Gaussian trace and the projective boundary volume.  All algebra after the
physical measure correspondence is exact. -/
theorem gravitationalCoupling_eq_gaussianMode_boundary_link
    (rho q : ℝ)
    (hScreen : screening (lambda4 q) ≠ 0) :
    gravitationalCoupling rho q =
      gaussianModeVertexIntegral (conformalChannelVertex rho q) *
        projectiveBoundaryVolume /
          ((rho * q) ^ gravitationalComplementExponent *
            screening (lambda4 q)) := by
  rw [conformalChannelVertex_gaussianMode_eq_electromagneticCoupling,
    projectiveBoundaryVolume_eq_pi_sq]
  exact gravitationalCoupling_eq_electromagnetic_link rho q hScreen

#print axioms GravityScreening.fourMode_radial_integral
#print axioms GravityScreening.gaussian_radial_moment_three
#print axioms GravityScreening.fourMode_gaussian_integral
#print axioms GravityScreening.fourierNormalized_fourMode_gaussian_integral
#print axioms GravityScreening.gaussianModeVertexIntegral_eq_pi_sq_mul
#print axioms GravityScreening.conformalChannelVertex_gaussianMode_eq_electromagneticCoupling
#print axioms GravityScreening.gravitationalCoupling_eq_gaussianMode_boundary_link

end

end GravityScreening
