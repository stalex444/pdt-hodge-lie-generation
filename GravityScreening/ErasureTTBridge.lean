module
public import GravityScreening.ErasureDilation
public import GravityScreening.TTResponseUniqueness

@[expose] public section

/-!
# The two-state erasure code is the TT exterior block

The finite Stinespring dilation was defined for arbitrary internal data
dimension.  This file specializes its data space to the two plus/cross
graviton coordinates.  The real retained amplitude is definitionally the
`sqrt(s) I₂` block selected independently by the TT uniqueness theorem.

The mathematical specialization is exact.  Identifying the two data labels
of the horizon code with the physical graviton polarizations remains the
physics premise.
-/

namespace GravityScreening

/-- Embed the two real TT polarization amplitudes in the two-dimensional
complex data space of the finite erasure dilation. -/
noncomputable def ttComplexAmplitude (x : TTCoordinates) : Fin 2 → ℂ :=
  fun i => (x i : ℂ)

/-- Read the retained real TT amplitudes from the exterior data port of the
finite erasure dilation. -/
noncomputable def erasureExteriorTTCoordinates
    (s : ℝ) (x : TTCoordinates) : TTCoordinates :=
  fun i => (erasureDilation s (ttComplexAmplitude x) (some i, none)).re

/-- The two-state exterior data port is exactly the real TT block
`sqrt(s) I₂`. -/
theorem erasureExteriorTTCoordinates_eq_ttExteriorCoordinates
    (s : ℝ) (x : TTCoordinates) :
    erasureExteriorTTCoordinates s x = ttExteriorCoordinates s x := by
  funext i
  simp [erasureExteriorTTCoordinates, erasureDilation,
    ttComplexAmplitude, ttExteriorCoordinates]

/-- Equivalently, the exterior coordinates are obtained by multiplying the
TT vector by the selected response matrix. -/
theorem erasureExteriorTTCoordinates_eq_mulVec
    (s : ℝ) (x : TTCoordinates) :
    erasureExteriorTTCoordinates s x = (ttExteriorBlock s).mulVec x := by
  rw [erasureExteriorTTCoordinates_eq_ttExteriorCoordinates,
    ttExteriorBlock_mulVec]

/-- The retained data amplitude commutes with every finite-dimensional linear
change of data coordinates.  This is the basis-independence behind its TT
rotational covariance. -/
theorem erasureDilation_exterior_mulVec_covariant {n : ℕ}
    (s : ℝ) (U : Matrix (Fin n) (Fin n) ℂ) (psi : Fin n → ℂ)
    (i : Fin n) :
    erasureDilation s (U.mulVec psi) (some i, none) =
      ∑ j, U i j * erasureDilation s psi (some j, none) := by
  simp only [erasureDilation, Matrix.mulVec, dotProduct]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The two-state erasure realization therefore commutes with the physical
plus/cross quarter-turn. -/
theorem erasureExteriorTTCoordinates_quarterTurn_covariant
    (s : ℝ) (x : TTCoordinates) :
    erasureExteriorTTCoordinates s
        (ttPolarizationQuarterTurn.mulVec x) =
      ttPolarizationQuarterTurn.mulVec
        (erasureExteriorTTCoordinates s x) := by
  funext i
  fin_cases i <;>
    simp [erasureExteriorTTCoordinates, erasureDilation,
      ttComplexAmplitude, ttPolarizationQuarterTurn, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ]

/-- Direct information-to-gravity capstone.  Once the two data labels of the
quartic erasure channel are the two TT graviton polarizations, matching the
same nonzero physical metric is equivalent to the inverse-screening Newton
response. -/
theorem quarticErasureTT_samePhysicalMetric_iff_newtonResponse
    (q kappa0 kappaQ G0 GQ : ℝ) (x : TTCoordinates)
    (hq : 1 < q) (hkappa0 : 0 ≤ kappa0) (hkappaQ : 0 ≤ kappaQ)
    (hkappa0_sq : kappa0 ^ 2 = 32 * Real.pi * G0)
    (hkappaQ_sq : kappaQ ^ 2 = 32 * Real.pi * GQ)
    (hmode : x 0 ≠ 0 ∨ x 1 ≠ 0) :
    physicalTTTensor kappaQ
          (erasureExteriorTTCoordinates (screening (lambda4 q)) x) =
        physicalTTTensor kappa0 x ↔
      GQ = G0 / ((2 * q - 1) / q ^ 2) := by
  rw [erasureExteriorTTCoordinates_eq_ttExteriorCoordinates]
  exact quarticTTExterior_samePhysicalMetric_iff_newtonResponse
    q kappa0 kappaQ G0 GQ x hq hkappa0 hkappaQ
      hkappa0_sq hkappaQ_sq hmode

#print axioms GravityScreening.erasureExteriorTTCoordinates_eq_ttExteriorCoordinates
#print axioms GravityScreening.erasureExteriorTTCoordinates_eq_mulVec
#print axioms GravityScreening.erasureDilation_exterior_mulVec_covariant
#print axioms GravityScreening.erasureExteriorTTCoordinates_quarterTurn_covariant
#print axioms GravityScreening.quarticErasureTT_samePhysicalMetric_iff_newtonResponse

end GravityScreening
