module
public import GravityScreening.UnifiedCouplingGrammar
public import GravityScreening.TransverseTracelessCount
public import GravityScreening.TTResponseUniqueness

@[expose] public section

/-!
# The pi-fourth gravity numerator as a two-polarization boundary determinant

The polar surface measure of the unit three-sphere is `2*pi^2`; its numerical
half is `pi^2`, the volume predicted for the antipodal quotient `RP^3`.
Linearized gravity has exactly two transverse-traceless polarizations.  A
rotationally covariant self-adjoint response on their plane is scalar, so
assigning the projective boundary normalization to either polarization forces
the same normalization on both.  Its determinant is then

`(pi^2)^2 = pi^4`,

exactly the numerator appearing in `gravitationalCoupling`.

The geometric value, the two-polarization count, the scalar classification,
and the determinant identity are proved here.  The free antipodal action's
measure-halving and the premise that the physical gravitational response uses
this quotient normalization remain explicit physical/geometric inputs; the
latter is represented by the single displayed diagonal-entry hypothesis in
the uniqueness theorem.
-/

namespace GravityScreening

noncomputable section

open Fintype MeasureTheory MeasureTheory.Measure Real Metric Set
open scoped ENNReal

/-- General closed form for the total polar surface measure of the unit sphere
in a finite-dimensional Euclidean space. -/
theorem euclideanVolume_toSphere_univ
    (ι : Type*) [Nonempty ι] [Fintype ι] :
    (volume : Measure (EuclideanSpace ℝ ι)).toSphere Set.univ =
      ENNReal.ofReal
        (2 * Real.sqrt Real.pi ^ Fintype.card ι /
          Real.Gamma (Fintype.card ι / 2)) := by
  have hc2 : (Fintype.card ι : ℝ) / 2 ≠ 0 := by positivity
  rw [Measure.toSphere_apply_univ, finrank_euclideanSpace,
    EuclideanSpace.volume_ball, ENNReal.ofReal_one, one_pow, one_mul,
    ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  congr 1
  rw [Real.Gamma_add_one hc2]
  field_simp

/-- The polar surface measure of the unit `S^3` is exactly `2*pi^2`. -/
theorem unitS3_surfaceMeasure :
    (volume : Measure (EuclideanSpace ℝ (Fin 4))).toSphere Set.univ =
      ENNReal.ofReal (2 * Real.pi ^ 2) := by
  have hsq : Real.sqrt Real.pi ^ 4 = Real.pi ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul,
      Real.sq_sqrt Real.pi_pos.le]
  rw [euclideanVolume_toSphere_univ, Fintype.card_fin, hsq,
    show ((4 : ℕ) : ℝ) / 2 = 2 by norm_num,
    Real.Gamma_two, div_one]

/-- The real value of the unit-three-sphere boundary normalization. -/
noncomputable def sThreeBoundaryVolume : ℝ :=
  2 * Real.pi ^ 2

/-- The numerical half of the `S^3` boundary volume, corresponding to the
standard volume of its antipodal quotient `RP^3`. -/
noncomputable def projectiveBoundaryVolume : ℝ :=
  sThreeBoundaryVolume / 2

theorem projectiveBoundaryVolume_eq_pi_sq :
    projectiveBoundaryVolume = Real.pi ^ 2 := by
  unfold projectiveBoundaryVolume sThreeBoundaryVolume
  ring

/-- The radial factor for a projective fundamental domain:
`integral_0^(pi/2) sin(chi)^2 dchi = pi/4`. -/
theorem projectivePolarFactor :
    ∫ chi in (0 : ℝ)..(Real.pi / 2), Real.sin chi ^ 2 =
      Real.pi / 4 := by
  rw [integral_sin_sq, Real.sin_zero, Real.cos_pi_div_two]
  ring

/-- A second exact calculation of the projective boundary value: multiply
the radial fundamental-domain factor by the unit-two-sphere area `4*pi`. -/
theorem projectivePolarVolume_eq_pi_sq :
    (4 * Real.pi) *
        (∫ chi in (0 : ℝ)..(Real.pi / 2), Real.sin chi ^ 2) =
      Real.pi ^ 2 := by
  rw [projectivePolarFactor]
  ring

/-- Apply the same projective boundary normalization to both TT
polarizations. -/
noncomputable def ttBoundaryVolumeResponse : Matrix (Fin 2) (Fin 2) ℝ :=
  scalarResponseMatrix 2 projectiveBoundaryVolume

/-- The dimensionless screened Planck-to-electron ratio appearing in the
deposited gravity formula. -/
noncomputable def screenedPlanckElectronRatio (rho q : ℝ) : ℝ :=
  depositedBaselinePlanck 1 rho q *
    Real.sqrt (screening (lambda4 q))

/-- Primary source of the fourth power: the dimensionless gravitational
coupling is the inverse square of the screened Planck-to-electron ratio.
Squaring forces both `112 -> 224` and `pi^2 -> pi^4`. -/
theorem gravitationalCoupling_eq_inverse_screenedPlanckRatio_sq
    (rho q : ℝ)
    (hS : 0 ≤ screening (lambda4 q))
    (hS0 : screening (lambda4 q) ≠ 0) :
    gravitationalCoupling rho q =
      1 / screenedPlanckElectronRatio rho q ^ 2 := by
  unfold gravitationalCoupling screenedPlanckElectronRatio
    depositedBaselinePlanck
  norm_num [gravitationalExponent]
  field_simp [hS0, Real.pi_ne_zero]
  rw [Real.sq_sqrt hS]

/-- Symmetry forces any response with the displayed boundary normalization to
be the canonical two-polarization boundary response. -/
theorem ttBoundaryVolumeResponse_unique_of_symmetry
    (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hcomm :
      M * ttPolarizationQuarterTurn = ttPolarizationQuarterTurn * M)
    (hself : M.transpose = M)
    (hboundary : M 0 0 = projectiveBoundaryVolume) :
    M = ttBoundaryVolumeResponse := by
  rw [ttResponse_eq_scalar_identity_of_commutes_selfAdjoint M hcomm hself,
    hboundary]
  rfl

/-- The determinant over the two physical TT polarizations is `pi^4`. -/
theorem ttBoundaryVolumeResponse_det :
    Matrix.det ttBoundaryVolumeResponse = Real.pi ^ 4 := by
  rw [show ttBoundaryVolumeResponse =
      scalarResponseMatrix 2 projectiveBoundaryVolume from rfl,
    scalarResponseMatrix_det]
  rw [projectiveBoundaryVolume_eq_pi_sq]
  ring

/-- Before the antipodal quotient, the square of the full `S^3` surface
measure is `4*pi^4`, the numerator in the associated area-quantum form. -/
theorem sThreeBoundaryVolume_sq :
    sThreeBoundaryVolume ^ 2 = 4 * Real.pi ^ 4 := by
  unfold sThreeBoundaryVolume
  ring

/-- Exact rewrite of the gravity formula: its numerator is the determinant of
the `S^3` boundary measure on the two-polarization TT space. -/
theorem gravitationalCoupling_eq_boundaryDet_div_combinedResponse
    (rho q : ℝ) :
    gravitationalCoupling rho q =
      Matrix.det ttBoundaryVolumeResponse /
        (Matrix.det
            (scalarResponseMatrix gravitationalExponent (rho * q)) *
          Matrix.det (constitutiveBlock (lambda4 q))) := by
  rw [ttBoundaryVolumeResponse_det, quarticCombinedResponse_det]
  rfl

/-- Capstone: the `S^3` value, the two-polarization count, and the gravity
numerator close in one exact theorem. -/
theorem boundaryMeasure_twoPolarization_gravity_capstone :
    (volume : Measure (EuclideanSpace ℝ (Fin 4))).toSphere Set.univ =
        ENNReal.ofReal (2 * Real.pi ^ 2) ∧
      projectiveBoundaryVolume = Real.pi ^ 2 ∧
      (4 * Real.pi) *
          (∫ chi in (0 : ℝ)..(Real.pi / 2), Real.sin chi ^ 2) =
        Real.pi ^ 2 ∧
      Module.finrank ℝ ttSubspace = 2 ∧
      Matrix.det ttBoundaryVolumeResponse = Real.pi ^ 4 ∧
      sThreeBoundaryVolume ^ 2 = 4 * Real.pi ^ 4 := by
  exact ⟨unitS3_surfaceMeasure, projectiveBoundaryVolume_eq_pi_sq,
    projectivePolarVolume_eq_pi_sq, ttSubspace_finrank,
    ttBoundaryVolumeResponse_det,
    sThreeBoundaryVolume_sq⟩

#print axioms GravityScreening.euclideanVolume_toSphere_univ
#print axioms GravityScreening.unitS3_surfaceMeasure
#print axioms GravityScreening.projectiveBoundaryVolume_eq_pi_sq
#print axioms GravityScreening.projectivePolarFactor
#print axioms GravityScreening.projectivePolarVolume_eq_pi_sq
#print axioms GravityScreening.gravitationalCoupling_eq_inverse_screenedPlanckRatio_sq
#print axioms GravityScreening.ttBoundaryVolumeResponse_unique_of_symmetry
#print axioms GravityScreening.ttBoundaryVolumeResponse_det
#print axioms GravityScreening.sThreeBoundaryVolume_sq
#print axioms GravityScreening.gravitationalCoupling_eq_boundaryDet_div_combinedResponse
#print axioms GravityScreening.boundaryMeasure_twoPolarization_gravity_capstone

end

end GravityScreening
