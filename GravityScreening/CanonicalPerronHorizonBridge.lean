module
public import GravityScreening.PerronHorizonCarrier
public import GravityScreening.RhoQModularCompletion

@[expose] public section

/-!
# Canonical finite Perron-to-horizon bridge

This file removes the arbitrary response-matrix hypothesis from the finite
horizon model. The response is the canonical left/right Perron compression
of the directed quartic residual. A concrete two-state off-diagonal mode
carries the joint `rho*q` modular phase, and the quartic erasure restriction
preserves that spectral label while the same Perron-selected determinant
scales area, entropy, and exterior information.

The construction is an exact finite model. Identifying it with a physical LQG
horizon subalgebra remains the final representation-level correspondence.
-/

namespace GravityScreening

/-- A two-state diagonal phase whose first entry carries the joint cubic--
quartic modular flow and whose second entry is the reference phase. -/
noncomputable def rhoQHorizonPhase
    (rho q t : ℝ) : Fin 2 → ℂ :=
  ![rhoQJointModularAnalyticFlow rho q (t : ℂ), 1]

/-- The matrix-unit tangent joining the reference state to the joint modular
phase state. -/
def horizonOffDiagonalMode : Fin 2 → Fin 2 → ℂ :=
  !![(0 : ℂ), 1; 0, 0]

/-- The concrete off-diagonal mode has exactly the joint `rho*q` modular
eigenvalue. -/
theorem horizonOffDiagonalMode_joint_eigenmode
    (rho q t : ℝ) :
    phaseAction (rhoQHorizonPhase rho q t) horizonOffDiagonalMode =
      scaleTangent (rhoQJointModularAnalyticFlow rho q (t : ℂ))
        horizonOffDiagonalMode := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [phaseAction, rhoQHorizonPhase, horizonOffDiagonalMode,
      scaleTangent]

/-- Exterior restriction by the Perron-selected erasure channel preserves the
joint modular spectral line exactly. -/
theorem canonicalPerronErasure_preserves_joint_eigenmode
    (rho q t : ℝ) :
    let M := perronCompressedConstitutiveBlock q
    extendedPhaseAction (rhoQHorizonPhase rho q t)
        (tangentErasure (Matrix.det M) horizonOffDiagonalMode) =
      scaleTangent (rhoQJointModularAnalyticFlow rho q (t : ℂ))
        (tangentErasure (Matrix.det M) horizonOffDiagonalMode) := by
  dsimp only
  exact tangentErasure_preserves_phase_eigenmode
    (Matrix.det (perronCompressedConstitutiveBlock q))
    (rhoQHorizonPhase rho q t) horizonOffDiagonalMode
    (rhoQJointModularAnalyticFlow rho q (t : ℂ))
    (horizonOffDiagonalMode_joint_eigenmode rho q t)

/-- Apply the canonical Perron-compressed response to a tangential frame. -/
noncomputable def canonicalPerronHorizonFrameAfter
    (q : ℝ) (before : Fin 2 → ℝ) : Fin 2 → ℝ :=
  (perronCompressedConstitutiveBlock q).mulVec before

/-- The canonical compressed response scales positive horizon area by exactly
the quartic screening determinant. -/
theorem canonicalPerronHorizon_area
    (q : ℝ) (hq4 : q ^ 4 = q + 1) (hq1 : 1 < q)
    (before₀ before₁ : Fin 2 → ℝ) :
    triadSurfaceArea2
        (canonicalPerronHorizonFrameAfter q before₀)
        (canonicalPerronHorizonFrameAfter q before₁) =
      ((2 * q - 1) / q ^ 2) *
        triadSurfaceArea2 before₀ before₁ := by
  let M := perronCompressedConstitutiveBlock q
  have hq0 : q ≠ 0 := by linarith
  have hdet : Matrix.det M = screening (lambda4 q) := by
    exact perronCompressedConstitutiveBlock_det q hq4 hq1
  have hdet0 : 0 ≤ Matrix.det M := by
    rw [hdet]
    exact (quarticScreening_bounds q hq1).1
  have hcarrier : IsTangentialFrameResponse M before₀ before₁
      (canonicalPerronHorizonFrameAfter q before₀)
      (canonicalPerronHorizonFrameAfter q before₁) := by
    exact ⟨rfl, rfl⟩
  rw [tangentialFrameResponse_area_scale M before₀ before₁
    (canonicalPerronHorizonFrameAfter q before₀)
    (canonicalPerronHorizonFrameAfter q before₁) hcarrier hdet0,
    hdet, quartic_screening_identity q hq0]

/-- Bekenstein--Hawking entropy inherits the same canonical determinant. -/
theorem canonicalPerronHorizon_entropy
    (q G hbar : ℝ) (hq4 : q ^ 4 = q + 1) (hq1 : 1 < q)
    (before₀ before₁ : Fin 2 → ℝ) :
    horizonEntropyFromArea G hbar
        (triadSurfaceArea2
          (canonicalPerronHorizonFrameAfter q before₀)
          (canonicalPerronHorizonFrameAfter q before₁)) =
      ((2 * q - 1) / q ^ 2) *
        horizonEntropyFromArea G hbar
          (triadSurfaceArea2 before₀ before₁) := by
  rw [canonicalPerronHorizon_area q hq4 hq1 before₀ before₁]
  exact horizonEntropyFromArea_scale G hbar
    (triadSurfaceArea2 before₀ before₁) ((2 * q - 1) / q ^ 2)

/-- The canonical determinant simultaneously controls exterior information
and Jacobson's inverse coupling response, while the global diagonal observable
is conserved. -/
theorem canonicalPerronHorizon_information_Jacobson {n : ℕ}
    (q baselineG : ℝ) (hq4 : q ^ 4 = q + 1) (hq1 : 1 < q)
    (k : Fin n → ℝ) (psi : Fin n → ℂ) :
    let M := perronCompressedConstitutiveBlock q
    exteriorDataExpectation k (quarticErasureDilation q psi) =
        Matrix.det M * finiteDiagonalExpectation k psi ∧
      exteriorDataExpectation k (quarticErasureDilation q psi) +
          hiddenDataExpectation k (quarticErasureDilation q psi) =
        finiteDiagonalExpectation k psi ∧
      jacobsonScaledCoupling baselineG 1 (Matrix.det M) =
        baselineG / ((2 * q - 1) / q ^ 2) := by
  dsimp only
  have hq0 : q ≠ 0 := by linarith
  have hdet :
      Matrix.det (perronCompressedConstitutiveBlock q) =
        screening (lambda4 q) :=
    perronCompressedConstitutiveBlock_det q hq4 hq1
  refine ⟨?_, quarticErasureDilation_total_expectation q k psi hq1, ?_⟩
  · rw [hdet]
    unfold quarticErasureDilation
    exact erasureDilation_exterior_expectation
      (screening (lambda4 q)) k psi (quarticScreening_bounds q hq1).1
  · rw [hdet, jacobsonScaledCoupling_entropy_only,
      quartic_screening_identity q hq0]

/-- The canonical Perron-compressed block supplies the local determinant in
the complete displayed PDT gravity response; the joint `rho*q` block supplies
the independent 224-dimensional bulk determinant. -/
theorem canonicalPerron_fullGravity_determinant
    (rho q : ℝ) (hrho0 : rho ≠ 0)
    (hq4 : q ^ 4 = q + 1) (hq1 : 1 < q) :
    1 / gravitationalCoupling rho q =
      (Matrix.det
          (scalarResponseMatrix gravitationalExponent (rho * q)) *
        Matrix.det (perronCompressedConstitutiveBlock q)) /
        Real.pi ^ 4 := by
  have hq0 : q ≠ 0 := by linarith
  have hscale : rho * q ≠ 0 := mul_ne_zero hrho0 hq0
  have hscreen : screening (lambda4 q) ≠ 0 := by
    obtain ⟨hl0, hl1⟩ :=
      positiveQuarticResidualWeight_mem_unitInterval q hq1
    exact ne_of_gt (screening_pos ⟨by linarith, hl1⟩)
  have hbase := gravitationalCoupling_inverse_eq_combinedResponse
    rho q hscale hscreen
  have hblock :
      perronCompressedConstitutiveBlock q =
        constitutiveBlock (lambda4 q) := by
    unfold perronCompressedConstitutiveBlock
    rw [quarticBiResidualCoefficient_eq_lambda4 q hq4 hq1]
  rw [hblock]
  exact hbase

/-- Canonical finite bridge capstone. The cubic and quartic clocks have
incommensurate frequencies and a unitary joint real flow; a concrete tangent
carries that joint spectral line through exterior restriction; and the
Perron-selected quartic determinant is simultaneously the area, entropy,
exterior-information, and inverse-Jacobson response. -/
theorem canonicalPerronHorizonBridge_capstone {n : ℕ}
    (rho q t baselineG G hbar : ℝ)
    (hrho3 : rho ^ 3 = rho + 1) (hrho1 : 1 < rho)
    (hq4 : q ^ 4 = q + 1) (hq1 : 1 < q)
    (before₀ before₁ : Fin 2 → ℝ)
    (k : Fin n → ℝ) (psi : Fin n → ℂ) :
    Irrational (Real.log rho / Real.log q) ∧
      ‖rhoQJointModularAnalyticFlow rho q (t : ℂ)‖ = 1 ∧
      1 / gravitationalCoupling rho q =
        (Matrix.det
            (scalarResponseMatrix gravitationalExponent (rho * q)) *
          Matrix.det (perronCompressedConstitutiveBlock q)) /
          Real.pi ^ 4 ∧
      extendedPhaseAction (rhoQHorizonPhase rho q t)
          (tangentErasure
            (Matrix.det (perronCompressedConstitutiveBlock q))
            horizonOffDiagonalMode) =
        scaleTangent (rhoQJointModularAnalyticFlow rho q (t : ℂ))
          (tangentErasure
            (Matrix.det (perronCompressedConstitutiveBlock q))
            horizonOffDiagonalMode) ∧
      triadSurfaceArea2
          (canonicalPerronHorizonFrameAfter q before₀)
          (canonicalPerronHorizonFrameAfter q before₁) =
        ((2 * q - 1) / q ^ 2) *
          triadSurfaceArea2 before₀ before₁ ∧
      horizonEntropyFromArea G hbar
          (triadSurfaceArea2
            (canonicalPerronHorizonFrameAfter q before₀)
            (canonicalPerronHorizonFrameAfter q before₁)) =
        ((2 * q - 1) / q ^ 2) *
          horizonEntropyFromArea G hbar
            (triadSurfaceArea2 before₀ before₁) ∧
      exteriorDataExpectation k (quarticErasureDilation q psi) =
        Matrix.det (perronCompressedConstitutiveBlock q) *
          finiteDiagonalExpectation k psi ∧
      exteriorDataExpectation k (quarticErasureDilation q psi) +
          hiddenDataExpectation k (quarticErasureDilation q psi) =
        finiteDiagonalExpectation k psi ∧
      jacobsonScaledCoupling baselineG 1
          (Matrix.det (perronCompressedConstitutiveBlock q)) =
        baselineG / ((2 * q - 1) / q ^ 2) := by
  have hmod := rhoQ_modularCompletion_capstone
    rho q t hrho3 hrho1 hq4 hq1
  have hinfo := canonicalPerronHorizon_information_Jacobson
    q baselineG hq4 hq1 k psi
  have hrho0 : rho ≠ 0 := by linarith
  exact ⟨hmod.1, hmod.2.1,
    canonicalPerron_fullGravity_determinant rho q hrho0 hq4 hq1,
    canonicalPerronErasure_preserves_joint_eigenmode rho q t,
    canonicalPerronHorizon_area q hq4 hq1 before₀ before₁,
    canonicalPerronHorizon_entropy q G hbar hq4 hq1 before₀ before₁,
    hinfo.1, hinfo.2.1, hinfo.2.2⟩

#print axioms GravityScreening.horizonOffDiagonalMode_joint_eigenmode
#print axioms GravityScreening.canonicalPerronErasure_preserves_joint_eigenmode
#print axioms GravityScreening.canonicalPerronHorizon_area
#print axioms GravityScreening.canonicalPerronHorizon_entropy
#print axioms GravityScreening.canonicalPerronHorizon_information_Jacobson
#print axioms GravityScreening.canonicalPerron_fullGravity_determinant
#print axioms GravityScreening.canonicalPerronHorizonBridge_capstone

end GravityScreening
