module
public import GravityScreening.ErasureDilation

@[expose] public section

/-!
# Modular covariance of the fixed-erasure tangent channel

The derivative of a fixed-erasure channel sends a density-matrix tangent `X`
to `s X` in the retained block and zero in the state-independent flag block.
This file proves that the tangent channel commutes with every diagonal phase
action.  Consequently it preserves every modular spectral line while the
relative-entropy and Fisher metrics contract by `s`.
-/

namespace GravityScreening

/-- A density-matrix tangent under a fixed-erasure channel.  The erasure flag
has zero tangent because its weight is independent of the input state. -/
noncomputable def tangentErasure {n : ℕ} (s : ℝ)
    (X : Fin n → Fin n → ℂ) :
    Option (Fin n) → Option (Fin n) → ℂ
  | some i, some j => (s : ℂ) * X i j
  | _, _ => 0

/-- Conjugation of a matrix tangent by a diagonal phase. -/
noncomputable def phaseAction {n : ℕ} (u : Fin n → ℂ)
    (X : Fin n → Fin n → ℂ) : Fin n → Fin n → ℂ :=
  fun i j => u i * X i j * star (u j)

/-- Extend a data-space phase by fixing the erasure flag. -/
noncomputable def extendedPhase {n : ℕ} (u : Fin n → ℂ) :
    Option (Fin n) → ℂ
  | some i => u i
  | none => 1

/-- The corresponding phase action on the data-plus-erasure output. -/
noncomputable def extendedPhaseAction {n : ℕ} (u : Fin n → ℂ)
    (Y : Option (Fin n) → Option (Fin n) → ℂ) :
    Option (Fin n) → Option (Fin n) → ℂ :=
  fun i j => extendedPhase u i * Y i j * star (extendedPhase u j)

/-- A fixed-erasure tangent channel is covariant under every diagonal phase
action.  No special choice of phase or retention weight is required. -/
theorem tangentErasure_phase_covariant {n : ℕ}
    (s : ℝ) (u : Fin n → ℂ) (X : Fin n → Fin n → ℂ) :
    extendedPhaseAction u (tangentErasure s X) =
      tangentErasure s (phaseAction u X) := by
  funext i j
  cases i <;> cases j <;>
    simp [extendedPhaseAction, extendedPhase, tangentErasure, phaseAction]
  ring

/-- Pointwise scalar multiplication of a matrix tangent. -/
noncomputable def scaleTangent {I : Type*} (z : ℂ)
    (X : I → I → ℂ) : I → I → ℂ :=
  fun i j => z * X i j

/-- If an input tangent lies on a phase spectral line with eigenvalue `z`,
the erased tangent lies on the same spectral line. -/
theorem tangentErasure_preserves_phase_eigenmode {n : ℕ}
    (s : ℝ) (u : Fin n → ℂ) (X : Fin n → Fin n → ℂ) (z : ℂ)
    (hEigen : phaseAction u X = scaleTangent z X) :
    extendedPhaseAction u (tangentErasure s X) =
      scaleTangent z (tangentErasure s X) := by
  rw [tangentErasure_phase_covariant, hEigen]
  funext i j
  cases i <;> cases j <;> simp [tangentErasure, scaleTangent]
  ring

/-- Covariance and relative-entropy contraction hold simultaneously: the
channel preserves the spectral label and multiplies distinguishability by
its retained weight. -/
theorem covariantErasure_spectral_information {n : ℕ}
    (s : ℝ) (u : Fin n → ℂ) (X : Fin n → Fin n → ℂ) (z : ℂ)
    (p r : Fin n → ℝ)
    (hEigen : phaseAction u X = scaleTangent z X)
    (hs : s ≠ 0) (hr : ∀ i, r i ≠ 0) :
    extendedPhaseAction u (tangentErasure s X) =
        scaleTangent z (tangentErasure s X) ∧
      erasureRelativeEntropy s p r =
        s * diagonalRelativeEntropy p r := by
  exact ⟨tangentErasure_preserves_phase_eigenmode s u X z hEigen,
    erasureRelativeEntropy_eq s p r hs hr⟩

/-- At the quartic retention weight, modular covariance coexists with the
exact gravity-screening contraction `(2q-1)/q^2`. -/
theorem quarticCovariantErasure_spectral_information {n : ℕ}
    (q : ℝ) (u : Fin n → ℂ) (X : Fin n → Fin n → ℂ) (z : ℂ)
    (p r : Fin n → ℝ)
    (hEigen : phaseAction u X = scaleTangent z X)
    (hq0 : q ≠ 0) (hS : screening (lambda4 q) ≠ 0)
    (hr : ∀ i, r i ≠ 0) :
    extendedPhaseAction u (tangentErasure (screening (lambda4 q)) X) =
        scaleTangent z (tangentErasure (screening (lambda4 q)) X) ∧
      erasureRelativeEntropy (screening (lambda4 q)) p r =
        ((2 * q - 1) / q ^ 2) * diagonalRelativeEntropy p r := by
  exact ⟨tangentErasure_preserves_phase_eigenmode
      (screening (lambda4 q)) u X z hEigen,
    quarticErasureRelativeEntropy_eq q p r hq0 hS hr⟩

#print axioms GravityScreening.tangentErasure_phase_covariant
#print axioms GravityScreening.tangentErasure_preserves_phase_eigenmode
#print axioms GravityScreening.covariantErasure_spectral_information
#print axioms GravityScreening.quarticCovariantErasure_spectral_information

end GravityScreening
