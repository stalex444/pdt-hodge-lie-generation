module
public import GravityScreening.PerronOpticalRaychaudhuri
public import GravityScreening.ClockToGravityChain
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

/-!
# KMS selection of the optical horizon flow

The quartic modular weight, exchange symmetry of the two screen channels, and
unit diagonal normalization uniquely determine the endpoint response.  If the
screen propagates affinely from the identity, those same data determine the
entire Jacobi flow and its initial shear.  The unit boost-weighted quadratic
shear flux then equals the exact quartic screening deficit.

The only physical placement premise is named explicitly: the horizon screen's
unoriented exchange line carries the quartic KMS/core weight `1/q`.  The file
does not derive that identification from an embedding of the quartic graph
algebra into a physical interacting horizon algebra.
-/

namespace GravityScreening

/-- Affine interpolation from the identity screen to an endpoint response. -/
noncomputable def affineScreenFlow
    (M : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  (1 : Matrix (Fin 2) (Fin 2) ℝ) +
    t • (M - (1 : Matrix (Fin 2) (Fin 2) ℝ))

/-- Initial velocity of the affine screen interpolation. -/
noncomputable def affineScreenVelocity
    (M : Matrix (Fin 2) (Fin 2) ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  M - (1 : Matrix (Fin 2) (Fin 2) ℝ)

theorem affineScreenFlow_zero
    (M : Matrix (Fin 2) (Fin 2) ℝ) :
    affineScreenFlow M 0 = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  simp [affineScreenFlow]

theorem affineScreenFlow_one
    (M : Matrix (Fin 2) (Fin 2) ℝ) :
    affineScreenFlow M 1 = M := by
  simp [affineScreenFlow]

/-- Once the KMS line is placed on the even channel, symmetry and normalization
fix the initial shear rather than merely its determinant. -/
theorem evenKMSBoundary_forces_initialShear
    (M : Matrix (Fin 2) (Fin 2) ℝ) (q : ℝ)
    (hexchange : IsChannelExchangeSymmetric M)
    (hmean : HasUnitDiagonalMean M)
    (hcore : HasEvenCoreWeight M q) :
    affineScreenVelocity M = perronOpticalVelocity (lambda4 q) := by
  have hM := clockWeight_forces_constitutiveBlock
    M q hexchange hmean hcore
  rw [hM]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [affineScreenVelocity, perronOpticalVelocity, constitutiveBlock]

/-- The whole affine screen history is uniquely selected by the same boundary
data. -/
theorem evenKMSBoundary_forces_opticalFlow
    (M : Matrix (Fin 2) (Fin 2) ℝ) (q t : ℝ)
    (hexchange : IsChannelExchangeSymmetric M)
    (hmean : HasUnitDiagonalMean M)
    (hcore : HasEvenCoreWeight M q) :
    affineScreenFlow M t = perronOpticalJacobi (lambda4 q) t := by
  have hV := evenKMSBoundary_forces_initialShear
    M q hexchange hmean hcore
  rw [perronOpticalJacobi_eq_identity_add]
  simp only [affineScreenFlow, affineScreenVelocity] at hV ⊢
  rw [hV]

/-- At each affine time, an unoriented core weight places the response on one
of the two sign-related trace-free shear branches. -/
theorem unorientedKMSBoundary_forces_opticalFlow_or_flip
    (M : Matrix (Fin 2) (Fin 2) ℝ) (q t : ℝ)
    (hexchange : IsChannelExchangeSymmetric M)
    (hmean : HasUnitDiagonalMean M)
    (hcore : HasUnorientedCoreWeight M q) :
    affineScreenFlow M t = perronOpticalJacobi (lambda4 q) t ∨
      affineScreenFlow M t = perronOpticalJacobi (-lambda4 q) t := by
  rcases hcore with heven | hodd
  · exact Or.inl
      (evenKMSBoundary_forces_opticalFlow M q t hexchange hmean heven)
  · right
    have hM := oddClockWeight_forces_constitutiveBlock
      M q hexchange hmean hodd
    rw [hM]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [affineScreenFlow, perronOpticalJacobi, constitutiveBlock]

/-- Squared norm of the initial trace-free screen velocity. -/
theorem screenTensorSq_perronOpticalVelocity (l : ℝ) :
    screenTensorSq (perronOpticalVelocity l) = 2 * l ^ 2 := by
  simp [screenTensorSq, perronOpticalVelocity]
  ring

/-- The dimensionless boost-weighted shear flux on one affine unit.  The
linear boost weight is the one appearing in the one-sided horizon modular
Hamiltonian; the normalization suppresses the common geometric constants. -/
noncomputable def unitBoostWeightedInitialShearFlux (l : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1,
    t * screenTensorSq (perronOpticalVelocity l)

/-- Constant initial shear over one affine unit contributes exactly `l^2` to
the normalized boost flux. -/
theorem unitBoostWeightedInitialShearFlux_eq_sq (l : ℝ) :
    unitBoostWeightedInitialShearFlux l = l ^ 2 := by
  rw [unitBoostWeightedInitialShearFlux,
    screenTensorSq_perronOpticalVelocity]
  norm_num
  ring

/-- At the quartic KMS value, the defined boost-weighted shear flux is exactly
the missing area fraction of the Perron endpoint. -/
theorem quarticBoostShearFlux_eq_areaDeficit (q : ℝ) :
    unitBoostWeightedInitialShearFlux (lambda4 q) =
      1 - perronOpticalAreaRatio (lambda4 q) 1 := by
  rw [unitBoostWeightedInitialShearFlux_eq_sq,
    perronOpticalAreaRatio_one]
  ring

/-- Boundary-selection capstone.  A quartic KMS line on either exchange
eigenspace fixes the entire affine screen flow up to orientation.  Both
branches have zero initial expansion, identical quadratic shear
flux, the same endpoint area, and the exact horizon-constraint update. -/
theorem quarticKMSOpticalBoundarySelection_capstone
    (M : Matrix (Fin 2) (Fin 2) ℝ)
    (q charge K inverseG area : ℝ)
    (hq4 : q ^ 4 = q + 1) (hq1 : 1 < q)
    (hG : inverseG ≠ 0)
    (hexchange : IsChannelExchangeSymmetric M)
    (hmean : HasUnitDiagonalMean M)
    (hcore : HasUnorientedCoreWeight M q)
    (h0 : horizonConstraintResidual charge K inverseG area = 0) :
    ((∀ t, affineScreenFlow M t =
        perronOpticalJacobi (lambda4 q) t) ∨
      (∀ t, affineScreenFlow M t =
        perronOpticalJacobi (-lambda4 q) t)) ∧
      Matrix.det M = screening (lambda4 q) ∧
      lambda4 q = quarticBiResidualCoefficient q ∧
      0 < Matrix.det M ∧
      unitBoostWeightedInitialShearFlux (lambda4 q) =
        lambda4 q ^ 2 ∧
      unitBoostWeightedInitialShearFlux (lambda4 q) =
        1 - Matrix.det M ∧
      perronOpticalExpansion (lambda4 q) 0 = 0 ∧
      horizonConstraintResidual charge
          (K + perronOpticalModularEnergyIncrement
            inverseG area (lambda4 q))
          inverseG
          (Matrix.det M * area) = 0 := by
  have hdet : Matrix.det M = screening (lambda4 q) :=
    unorientedClockWeight_forces_screening
      M q hexchange hmean hcore
  have hresidual : lambda4 q = quarticBiResidualCoefficient q :=
    (quarticBiResidualCoefficient_eq_lambda4 q hq4 hq1).symm
  have hdetpos : 0 < Matrix.det M := by
    rw [hdet]
    exact quarticScreening_pos q hq1
  have hflow :
      (∀ t, affineScreenFlow M t =
        perronOpticalJacobi (lambda4 q) t) ∨
      (∀ t, affineScreenFlow M t =
        perronOpticalJacobi (-lambda4 q) t) := by
    rcases hcore with heven | hodd
    · left
      intro t
      exact evenKMSBoundary_forces_opticalFlow
        M q t hexchange hmean heven
    · right
      intro t
      have hM := oddClockWeight_forces_constitutiveBlock
        M q hexchange hmean hodd
      rw [hM]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [affineScreenFlow, perronOpticalJacobi, constitutiveBlock]
  refine ⟨hflow, hdet, hresidual, hdetpos,
    unitBoostWeightedInitialShearFlux_eq_sq _, ?_,
    (perronOptical_initial_data (lambda4 q)).1, ?_⟩
  · rw [unitBoostWeightedInitialShearFlux_eq_sq, hdet]
    simp [screening]
  · rw [hdet]
    have hupdate := horizonConstraint_perronOptical_update
      charge K inverseG area (lambda4 q) hG h0
    simpa [perronOpticalAreaRatio_one, screening] using hupdate

#print axioms GravityScreening.evenKMSBoundary_forces_initialShear
#print axioms GravityScreening.evenKMSBoundary_forces_opticalFlow
#print axioms GravityScreening.unorientedKMSBoundary_forces_opticalFlow_or_flip
#print axioms GravityScreening.screenTensorSq_perronOpticalVelocity
#print axioms GravityScreening.unitBoostWeightedInitialShearFlux_eq_sq
#print axioms GravityScreening.quarticBoostShearFlux_eq_areaDeficit
#print axioms GravityScreening.quarticKMSOpticalBoundarySelection_capstone

end GravityScreening
