module
public import GravityScreening.ObserverGaugeIntegration

@[expose] public section

/-!
# The projective four-mode shell

This file isolates an alternative mathematical source of the `pi^2` factor
that does not treat a redundant gauge orbit as a normalized average.  A real
field has Fourier amplitudes related by `h(-k) = conj (h k)`, hence equal power
at antipodal momenta.  On the unit shell in four real momentum coordinates,
the antipodal action is free.  Counting each real-mode pair once therefore
uses half of the kernel-checked `S^3` shell mass, namely `pi^2`.

The physical use of a Euclideanized unit shell as the zero-momentum coupling's
mode density remains a correspondence premise; the statements below prove
the exact geometry and the resulting conditional coupling identity.
-/

namespace GravityScreening

noncomputable section

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal

abbrev FourModeSpace := EuclideanSpace ℝ (Fin 4)

/-- Fourier reality condition for a real field. -/
def IsRealityConstrainedMode (amplitude : FourModeSpace → ℂ) : Prop :=
  ∀ k, amplitude (-k) = star (amplitude k)

/-- The nonnegative power carried by one complex Fourier amplitude. -/
noncomputable def modePower
    (amplitude : FourModeSpace → ℂ) (k : FourModeSpace) : ℝ :=
  Complex.normSq (amplitude k)

/-- Reality makes the mode power antipode-even. -/
theorem realityConstrained_modePower_antipode
    (amplitude : FourModeSpace → ℂ)
    (hReality : IsRealityConstrainedMode amplitude)
    (k : FourModeSpace) :
    modePower amplitude (-k) = modePower amplitude k := by
  rw [modePower, modePower, hReality]
  exact Complex.normSq_conj _

/-- There are no antipodal fixed points on the unit shell. -/
theorem unitModeShell_antipode_ne_self
    (k : FourModeSpace) (hUnit : ‖k‖ = 1) :
    -k ≠ k := by
  intro h
  have htwo : (2 : ℝ) • k = 0 := by
    calc
      (2 : ℝ) • k = k + k := two_smul ℝ k
      _ = k + (-k) := by rw [h]
      _ = 0 := by exact add_neg_cancel k
  have hk0 : k = 0 := by
    rcases smul_eq_zero.mp htwo with h2 | hk
    · norm_num at h2
    · exact hk
  subst k
  norm_num at hUnit

/-- Polar surface measure on the unit shell in four real mode coordinates. -/
abbrev FourModeShell := Metric.sphere (0 : FourModeSpace) 1

noncomputable def fourModeShellMeasure : Measure FourModeShell :=
  (volume : Measure FourModeSpace).toSphere

/-- Its total real mass is the unit-three-sphere value `2*pi^2`. -/
theorem fourModeShellMeasure_real_univ :
    fourModeShellMeasure.real Set.univ = 2 * Real.pi ^ 2 := by
  rw [measureReal_def, fourModeShellMeasure, unitS3_surfaceMeasure]
  simp
  positivity

/-- Count each antipodal real-mode pair once by taking half of the full shell
integral. -/
noncomputable def projectiveModeShellScalarIntegral (vertex : ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    ∫ _ : FourModeShell, vertex ∂fourModeShellMeasure

/-- A constant mode density integrates to exactly `pi^2` times the density
when each antipodal real-mode pair is counted once. -/
theorem projectiveModeShellScalarIntegral_eq_pi_sq_mul
    (vertex : ℝ) :
    projectiveModeShellScalarIntegral vertex = Real.pi ^ 2 * vertex := by
  rw [projectiveModeShellScalarIntegral, integral_const, smul_eq_mul,
    fourModeShellMeasure_real_univ]
  ring

/-- Applying the projective mode-shell count to the 15-channel scalar vertex
reproduces the deposited electromagnetic expression exactly. -/
theorem conformalChannelVertex_projectiveModeShell_eq_electromagneticCoupling
    (rho q : ℝ) :
    projectiveModeShellScalarIntegral (conformalChannelVertex rho q) =
      electromagneticCoupling rho q := by
  rw [projectiveModeShellScalarIntegral_eq_pi_sq_mul]
  simp [conformalChannelVertex, electromagneticCoupling, div_eq_mul_inv]

/-- Conditional gravity factorization through the projective four-mode shell.
All algebra after the shell-density premise is exact. -/
theorem gravitationalCoupling_eq_projectiveModeShell_link
    (rho q : ℝ)
    (hScreen : screening (lambda4 q) ≠ 0) :
    gravitationalCoupling rho q =
      projectiveModeShellScalarIntegral (conformalChannelVertex rho q) *
        projectiveBoundaryVolume /
          ((rho * q) ^ gravitationalComplementExponent *
            screening (lambda4 q)) := by
  rw [conformalChannelVertex_projectiveModeShell_eq_electromagneticCoupling,
    projectiveBoundaryVolume_eq_pi_sq]
  exact gravitationalCoupling_eq_electromagnetic_link rho q hScreen

#print axioms GravityScreening.realityConstrained_modePower_antipode
#print axioms GravityScreening.unitModeShell_antipode_ne_self
#print axioms GravityScreening.fourModeShellMeasure_real_univ
#print axioms GravityScreening.projectiveModeShellScalarIntegral_eq_pi_sq_mul
#print axioms GravityScreening.conformalChannelVertex_projectiveModeShell_eq_electromagneticCoupling
#print axioms GravityScreening.gravitationalCoupling_eq_projectiveModeShell_link

end

end GravityScreening
