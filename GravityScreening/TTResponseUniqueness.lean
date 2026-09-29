module
public import GravityScreening.TTHorizonSplitter

@[expose] public section

/-!
# Uniqueness of the passive isotropic TT response

The plus/cross polarization plane carries its standard quarter-turn.  A real
response commuting with that turn has the form `a I + b J`.  Self-adjointness
removes the polarization-rotation term `b J`.  If the response has quadratic
weight `s` and lies on the nonnegative passive branch, it is therefore
uniquely `sqrt(s) I`.

This derives the matrix form used in `TTHorizonSplitter` from explicit
kinematic hypotheses.  It does not identify the physical Q interaction with
such a response; that remains a physics premise.
-/

namespace GravityScreening

/-- Quarter-turn on the plus/cross polarization coordinates.  It is also the
real polarization part of the generalized-curl symbol for momentum along the
third axis. -/
def ttPolarizationQuarterTurn : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, -1;
     1,  0]

theorem ttPolarizationQuarterTurn_sq :
    ttPolarizationQuarterTurn * ttPolarizationQuarterTurn =
      -(1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ttPolarizationQuarterTurn, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The commutant of the polarization quarter-turn consists exactly of the
real matrices `a I + b J`. -/
theorem commutes_ttPolarizationQuarterTurn_iff
    (M : Matrix (Fin 2) (Fin 2) ℝ) :
    M * ttPolarizationQuarterTurn = ttPolarizationQuarterTurn * M ↔
      M 0 0 = M 1 1 ∧ M 0 1 = -M 1 0 := by
  constructor
  · intro h
    have h00 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 0 0) h
    have h01 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 0 1) h
    constructor
    · simpa [ttPolarizationQuarterTurn, Matrix.mul_apply,
        Fin.sum_univ_succ] using h01
    · simpa [ttPolarizationQuarterTurn, Matrix.mul_apply,
        Fin.sum_univ_succ] using h00
  · rintro ⟨hdiag, hoff⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ttPolarizationQuarterTurn, Matrix.mul_apply,
        Fin.sum_univ_succ, hdiag, hoff]

/-- Rotational covariance and self-adjointness force a response to be a real
scalar on the whole two-polarization space. -/
theorem ttResponse_eq_scalar_identity_of_commutes_selfAdjoint
    (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hcomm :
      M * ttPolarizationQuarterTurn = ttPolarizationQuarterTurn * M)
    (hself : M.transpose = M) :
    M = (M 0 0) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  have hshape := (commutes_ttPolarizationQuarterTurn_iff M).1 hcomm
  have hsym01 : M 1 0 = M 0 1 := by
    have h := congrArg
      (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 0 1) hself
    simpa using h
  have hoff : M 0 1 = 0 := by
    rcases hshape with ⟨_, hanti⟩
    rw [hsym01] at hanti
    linarith
  rcases hshape with ⟨hdiag, _⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hdiag, hoff, hsym01]

/-- A self-adjoint rotationally covariant response with isotropic quadratic
weight `s` is uniquely the positive passive block `sqrt(s) I₂`. -/
theorem ttResponse_unique_of_symmetry_weight
    (M : Matrix (Fin 2) (Fin 2) ℝ) (s : ℝ)
    (hs : 0 ≤ s)
    (hcomm :
      M * ttPolarizationQuarterTurn = ttPolarizationQuarterTurn * M)
    (hself : M.transpose = M)
    (hweight :
      M.transpose * M = s • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (hpassive : 0 ≤ M 0 0) :
    M = ttExteriorBlock s := by
  have hscalar :=
    ttResponse_eq_scalar_identity_of_commutes_selfAdjoint M hcomm hself
  have ha2 : (M 0 0) ^ 2 = s := by
    have h00 := congrArg
      (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 0 0) hweight
    rw [hscalar] at h00
    simpa [Matrix.mul_apply, Fin.sum_univ_succ, pow_two] using h00
  have ha : M 0 0 = Real.sqrt s := by
    have hsqrt0 := Real.sqrt_nonneg s
    have hsqrt2 := Real.sq_sqrt hs
    nlinarith
  rw [hscalar, ha]
  rfl

/-- At the quartic value, the unique passive isotropic TT response has the
PDT weight `(2q-1)/q^2`. -/
theorem quarticTTResponse_unique_of_symmetry_weight
    (M : Matrix (Fin 2) (Fin 2) ℝ) (q : ℝ)
    (hq : 1 < q)
    (hcomm :
      M * ttPolarizationQuarterTurn = ttPolarizationQuarterTurn * M)
    (hself : M.transpose = M)
    (hweight :
      M.transpose * M =
        screening (lambda4 q) • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (hpassive : 0 ≤ M 0 0) :
    M = ttExteriorBlock (screening (lambda4 q)) := by
  have hS : 0 ≤ screening (lambda4 q) :=
    (quarticScreening_bounds q hq).1
  exact ttResponse_unique_of_symmetry_weight M (screening (lambda4 q))
    hS hcomm hself hweight hpassive

/-- The symmetry and weight hypotheses alone force the same-metric Newton
response for every nonzero TT wave.  The explicit matrix is eliminated from
the assumptions by the uniqueness theorem. -/
theorem ttSymmetryWeight_samePhysicalMetric_iff_newtonResponse
    (M : Matrix (Fin 2) (Fin 2) ℝ)
    (s kappa0 kappaQ G0 GQ : ℝ) (x : TTCoordinates)
    (hs : 0 < s) (hkappa0 : 0 ≤ kappa0) (hkappaQ : 0 ≤ kappaQ)
    (hkappa0_sq : kappa0 ^ 2 = 32 * Real.pi * G0)
    (hkappaQ_sq : kappaQ ^ 2 = 32 * Real.pi * GQ)
    (hmode : x 0 ≠ 0 ∨ x 1 ≠ 0)
    (hcomm :
      M * ttPolarizationQuarterTurn = ttPolarizationQuarterTurn * M)
    (hself : M.transpose = M)
    (hweight :
      M.transpose * M = s • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (hpassive : 0 ≤ M 0 0) :
    physicalTTTensor kappaQ (M.mulVec x) = physicalTTTensor kappa0 x ↔
      GQ = G0 / s := by
  have hM := ttResponse_unique_of_symmetry_weight
    M s (le_of_lt hs) hcomm hself hweight hpassive
  rw [hM, ttExteriorBlock_mulVec]
  exact ttExterior_samePhysicalMetric_iff_newtonResponse
    s kappa0 kappaQ G0 GQ x hs hkappa0 hkappaQ
      hkappa0_sq hkappaQ_sq hmode

/-- Quartic capstone: a passive, self-adjoint, rotationally covariant TT
response with the Q quadratic weight describes the same physical metric
exactly when Newton's coupling has the deposited inverse-screening response.
-/
theorem quarticTTSymmetryWeight_samePhysicalMetric_iff_newtonResponse
    (M : Matrix (Fin 2) (Fin 2) ℝ)
    (q kappa0 kappaQ G0 GQ : ℝ) (x : TTCoordinates)
    (hq : 1 < q) (hkappa0 : 0 ≤ kappa0) (hkappaQ : 0 ≤ kappaQ)
    (hkappa0_sq : kappa0 ^ 2 = 32 * Real.pi * G0)
    (hkappaQ_sq : kappaQ ^ 2 = 32 * Real.pi * GQ)
    (hmode : x 0 ≠ 0 ∨ x 1 ≠ 0)
    (hcomm :
      M * ttPolarizationQuarterTurn = ttPolarizationQuarterTurn * M)
    (hself : M.transpose = M)
    (hweight :
      M.transpose * M =
        screening (lambda4 q) • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (hpassive : 0 ≤ M 0 0) :
    physicalTTTensor kappaQ (M.mulVec x) = physicalTTTensor kappa0 x ↔
      GQ = G0 / ((2 * q - 1) / q ^ 2) := by
  have hM := quarticTTResponse_unique_of_symmetry_weight
    M q hq hcomm hself hweight hpassive
  rw [hM, ttExteriorBlock_mulVec]
  exact quarticTTExterior_samePhysicalMetric_iff_newtonResponse
    q kappa0 kappaQ G0 GQ x hq hkappa0 hkappaQ
      hkappa0_sq hkappaQ_sq hmode

/-- The selected block actually satisfies the symmetry, quadratic-weight,
and passive-branch hypotheses used in the uniqueness theorem. -/
theorem ttExteriorBlock_characterization
    (s : ℝ) (hs : 0 ≤ s) :
    (ttExteriorBlock s * ttPolarizationQuarterTurn =
        ttPolarizationQuarterTurn * ttExteriorBlock s) ∧
      (ttExteriorBlock s).transpose = ttExteriorBlock s ∧
      (ttExteriorBlock s).transpose * ttExteriorBlock s =
        s • (1 : Matrix (Fin 2) (Fin 2) ℝ) ∧
      0 ≤ ttExteriorBlock s 0 0 := by
  constructor
  · change
      ((Real.sqrt s) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) *
          ttPolarizationQuarterTurn =
        ttPolarizationQuarterTurn *
          ((Real.sqrt s) • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    simp
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [ttExteriorBlock]
  constructor
  · have hsqrt : Real.sqrt s * Real.sqrt s = s :=
      Real.mul_self_sqrt hs
    change
      (((Real.sqrt s) • (1 : Matrix (Fin 2) (Fin 2) ℝ)).transpose) *
          ((Real.sqrt s) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) =
        s • (1 : Matrix (Fin 2) (Fin 2) ℝ)
    simp only [Matrix.transpose_smul, Matrix.transpose_one,
      Matrix.mul_smul, Matrix.mul_one]
    rw [smul_smul, hsqrt]
  · simp [ttExteriorBlock, Real.sqrt_nonneg]

#print axioms GravityScreening.ttPolarizationQuarterTurn_sq
#print axioms GravityScreening.commutes_ttPolarizationQuarterTurn_iff
#print axioms GravityScreening.ttResponse_eq_scalar_identity_of_commutes_selfAdjoint
#print axioms GravityScreening.ttResponse_unique_of_symmetry_weight
#print axioms GravityScreening.quarticTTResponse_unique_of_symmetry_weight
#print axioms GravityScreening.ttSymmetryWeight_samePhysicalMetric_iff_newtonResponse
#print axioms GravityScreening.quarticTTSymmetryWeight_samePhysicalMetric_iff_newtonResponse
#print axioms GravityScreening.ttExteriorBlock_characterization

end GravityScreening
