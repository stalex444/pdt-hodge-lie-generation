module
public import GravityScreening.TimeDilation

@[expose] public section

/-!
# The quantum free-fall gauge phase

This file formalizes the elementary phase identity measured by the Quantum
Galileo Interferometer.  A ballistic path rises from height zero at time
`-T`, turns at time zero, and returns to height zero at time `T`.  In a
uniform gravitational field its Newtonian action is exactly
`-m*g^2*T^3/3`.  The change of the freely falling frame's gauge phase between
the same endpoints gives the identical quantity after division by `hbar`.

The result is pure mechanics and does not identify the experimental phase
with a PDT algebraic constant.  It supplies a proved equivalence-principle
interface for the phase-preservation results in `TimeDilation`.

Reference: O. Dobkowski et al., *Observation of quantum free fall and the
consistency with the equivalence principle*, arXiv:2502.14535v4, especially
Eqs. (1)--(2).  With endpoints at times `-T` and `T`, Eq. (2) is
`-m*g^2*T^3/(3*hbar)`.
-/

namespace GravityScreening

/-- Symmetric ballistic height: zero at `-T` and `T`, with a turning point at
time zero. -/
noncomputable def qgiBallisticHeight (g T t : ℝ) : ℝ :=
  g * (T ^ 2 - t ^ 2) / 2

/-- Velocity of the symmetric ballistic path. -/
def qgiBallisticVelocity (g t : ℝ) : ℝ :=
  -g * t

/-- Newtonian Lagrangian for a particle in the uniform potential `m*g*z`. -/
noncomputable def uniformGravityLagrangian (m g z velocity : ℝ) : ℝ :=
  m * velocity ^ 2 / 2 - m * g * z

/-- Along the symmetric ballistic path the Lagrangian is an explicit even
quadratic polynomial. -/
theorem qgiBallistic_lagrangian_eq (m g T t : ℝ) :
    uniformGravityLagrangian m g
        (qgiBallisticHeight g T t) (qgiBallisticVelocity g t) =
      m * g ^ 2 * t ^ 2 - m * g ^ 2 * T ^ 2 / 2 := by
  unfold uniformGravityLagrangian qgiBallisticHeight qgiBallisticVelocity
  ring

/-- A polynomial primitive of the ballistic-path Lagrangian. -/
noncomputable def qgiBallisticActionPrimitive (m g T t : ℝ) : ℝ :=
  m * g ^ 2 * t ^ 3 / 3 - m * g ^ 2 * T ^ 2 * t / 2

/-- The displayed primitive differentiates to the ballistic Lagrangian. -/
theorem qgiBallisticActionPrimitive_hasDerivAt (m g T t : ℝ) :
    HasDerivAt (qgiBallisticActionPrimitive m g T)
      (uniformGravityLagrangian m g
        (qgiBallisticHeight g T t) (qgiBallisticVelocity g t)) t := by
  rw [qgiBallistic_lagrangian_eq]
  unfold qgiBallisticActionPrimitive
  have hcubic := (hasDerivAt_pow 3 t).const_mul (m * g ^ 2 / 3)
  have hlinear := (hasDerivAt_id t).const_mul (m * g ^ 2 * T ^ 2 / 2)
  have hpath :
      HasDerivAt
        (fun x : ℝ =>
          m * g ^ 2 * x ^ 3 / 3 - m * g ^ 2 * T ^ 2 * x / 2)
        (m * g ^ 2 / 3 * (3 * t ^ (3 - 1)) -
          m * g ^ 2 * T ^ 2 / 2 * 1) t := by
    apply (hcubic.sub hlinear).congr_of_eventuallyEq
    filter_upwards with x
    change
      m * g ^ 2 * x ^ 3 / 3 - m * g ^ 2 * T ^ 2 * x / 2 =
        m * g ^ 2 / 3 * x ^ 3 - m * g ^ 2 * T ^ 2 / 2 * x
    ring
  apply hpath.congr_deriv
  ring

/-- Exact action accumulated between the two recombination endpoints. -/
noncomputable def qgiBallisticAction (m g T : ℝ) : ℝ :=
  qgiBallisticActionPrimitive m g T T -
    qgiBallisticActionPrimitive m g T (-T)

/-- The Newtonian action has the characteristic cubic free-fall law. -/
theorem qgiBallisticAction_eq (m g T : ℝ) :
    qgiBallisticAction m g T = -(m * g ^ 2 * T ^ 3) / 3 := by
  unfold qgiBallisticAction qgiBallisticActionPrimitive
  ring

/-- Gauge phase relating a freely falling frame to the laboratory frame in a
uniform field, in the sign convention used by this file. -/
noncomputable def qgiGaugePhase (m g hbar z t : ℝ) : ℝ :=
  -(m * g * z * t + m * g ^ 2 * t ^ 3 / 6) / hbar

/-- The gauge-phase change between the two zero-height endpoints. -/
theorem qgiGaugePhase_endpointDifference
    (m g hbar T : ℝ) :
    qgiGaugePhase m g hbar 0 T - qgiGaugePhase m g hbar 0 (-T) =
      -(m * g ^ 2 * T ^ 3) / (3 * hbar) := by
  unfold qgiGaugePhase
  ring

/-- Quantum phase obtained from the Newtonian action. -/
noncomputable def qgiActionPhase (m g hbar T : ℝ) : ℝ :=
  qgiBallisticAction m g T / hbar

/-- **Quantum Galileo identity.** For nonzero `hbar`, the action calculation
and the freely falling frame's gauge transformation give the same phase. -/
theorem qgi_actionPhase_eq_gaugePhase
    (m g hbar T : ℝ) (hhbar : hbar ≠ 0) :
    qgiActionPhase m g hbar T =
      qgiGaugePhase m g hbar 0 T -
        qgiGaugePhase m g hbar 0 (-T) := by
  rw [qgiGaugePhase_endpointDifference, qgiActionPhase,
    qgiBallisticAction_eq]
  field_simp

/-- The observable complex phase multiplier has unit norm. -/
noncomputable def qgiPhaseMultiplier (m g hbar T : ℝ) : ℂ :=
  Complex.exp (Complex.I * qgiActionPhase m g hbar T)

theorem qgiPhaseMultiplier_norm (m g hbar T : ℝ) :
    ‖qgiPhaseMultiplier m g hbar T‖ = 1 := by
  unfold qgiPhaseMultiplier qgiActionPhase
  rw [Complex.norm_exp]
  simp

/-- The same phase may be written in the generic interaction-phase language
used by the PDT clock module. -/
theorem qgiActionPhase_eq_interactionPhase
    (m g hbar T : ℝ) :
    qgiActionPhase m g hbar T =
      interactionPhase (1 / hbar) (qgiBallisticAction m g T) 1 := by
  unfold qgiActionPhase interactionPhase
  ring

/-- Consequently the generic lapse reparametrization preserves a
Quantum-Galileo action phase expressed in coordinate or proper variables. -/
theorem qgi_lapse_reparametrization_preserves_phase
    (m g hbar T lapse coordinateDuration : ℝ) :
    interactionPhase (1 / hbar)
        (coordinateGenerator lapse (qgiBallisticAction m g T))
        coordinateDuration =
      interactionPhase (1 / hbar) (qgiBallisticAction m g T)
        (properDuration lapse coordinateDuration) := by
  exact lapse_reparametrization_preserves_phase
    (1 / hbar) lapse (qgiBallisticAction m g T) coordinateDuration

/-- The complete formal interface: the ballistic action has the cubic law,
the action and frame calculations give the same quantum phase, the resulting
complex multiplier is norm-preserving, and lapse reparametrization leaves the
generic interaction phase unchanged. -/
theorem quantumGalileoEquivalencePhase_package
    (m g hbar T lapse coordinateDuration : ℝ) (hhbar : hbar ≠ 0) :
    qgiBallisticAction m g T = -(m * g ^ 2 * T ^ 3) / 3 ∧
    qgiActionPhase m g hbar T =
      qgiGaugePhase m g hbar 0 T - qgiGaugePhase m g hbar 0 (-T) ∧
    ‖qgiPhaseMultiplier m g hbar T‖ = 1 ∧
    interactionPhase (1 / hbar)
        (coordinateGenerator lapse (qgiBallisticAction m g T))
        coordinateDuration =
      interactionPhase (1 / hbar) (qgiBallisticAction m g T)
        (properDuration lapse coordinateDuration) := by
  exact ⟨qgiBallisticAction_eq m g T,
    qgi_actionPhase_eq_gaugePhase m g hbar T hhbar,
    qgiPhaseMultiplier_norm m g hbar T,
    qgi_lapse_reparametrization_preserves_phase
      m g hbar T lapse coordinateDuration⟩

#print axioms GravityScreening.qgiBallisticActionPrimitive_hasDerivAt
#print axioms GravityScreening.qgiBallisticAction_eq
#print axioms GravityScreening.qgiGaugePhase_endpointDifference
#print axioms GravityScreening.qgi_actionPhase_eq_gaugePhase
#print axioms GravityScreening.qgiPhaseMultiplier_norm
#print axioms GravityScreening.qgi_lapse_reparametrization_preserves_phase
#print axioms GravityScreening.quantumGalileoEquivalencePhase_package

end GravityScreening
