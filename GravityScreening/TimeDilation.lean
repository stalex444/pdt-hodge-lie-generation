module
public import GravityScreening.HorizonConstraint

@[expose] public section

/-!
# Clock phase under gravitational time reparametrization

The algebraic clock fixes a dimensionless phase accumulation.  A lapse converts
coordinate time into an observer's proper time and rescales the corresponding
coordinate generator.  Their product, and hence the phase, is unchanged.
This file records that kinematic fact without postulating a PDT lapse formula.
-/

namespace GravityScreening

/-- Proper duration for a constant-lapse segment. -/
def properDuration (lapse coordinateDuration : ℝ) : ℝ :=
  lapse * coordinateDuration

/-- Coordinate-time generator corresponding to a proper-time generator. -/
def coordinateGenerator (lapse properGenerator : ℝ) : ℝ :=
  lapse * properGenerator

/-- Dimensionless interaction phase accumulated by a coupling, generator,
and duration. -/
def interactionPhase
    (coupling generator duration : ℝ) : ℝ :=
  coupling * generator * duration

/-- Expressing the same local clock in coordinate time or proper time leaves
its accumulated interaction phase unchanged. -/
theorem lapse_reparametrization_preserves_phase
    (coupling lapse properGenerator coordinateDuration : ℝ) :
    interactionPhase coupling
        (coordinateGenerator lapse properGenerator) coordinateDuration =
      interactionPhase coupling properGenerator
        (properDuration lapse coordinateDuration) := by
  unfold interactionPhase coordinateGenerator properDuration
  ring

/-- For a nonzero lapse, a coordinate frequency converts to proper-time
frequency by division by the lapse. -/
noncomputable def properFrequency
    (coordinateFrequency lapse : ℝ) : ℝ :=
  coordinateFrequency / lapse

theorem properFrequency_mul_properDuration
    (coordinateFrequency lapse coordinateDuration : ℝ)
    (hLapse : lapse ≠ 0) :
    properFrequency coordinateFrequency lapse *
        properDuration lapse coordinateDuration =
      coordinateFrequency * coordinateDuration := by
  unfold properFrequency properDuration
  field_simp

/-- Two observers assigning lapses `N₁,N₂` to the same coordinate phase rate
measure the corresponding inverse-lapse ratio of proper-time frequencies. -/
theorem properFrequency_ratio
    (coordinateFrequency lapse1 lapse2 : ℝ)
    (hOmega : coordinateFrequency ≠ 0)
    (h1 : lapse1 ≠ 0) (h2 : lapse2 ≠ 0) :
    properFrequency coordinateFrequency lapse1 /
        properFrequency coordinateFrequency lapse2 =
      lapse2 / lapse1 := by
  unfold properFrequency
  field_simp

/-- A common rescaling of boost heat and boost temperature cancels from their
thermodynamic ratio.  This is why boost normalization or time dilation alone
cannot determine Newton's coupling in the Jacobson relation. -/
theorem boost_normalization_cancels
    (heat temperature boostScale : ℝ)
    (hTemperature : temperature ≠ 0)
    (hScale : boostScale ≠ 0) :
    (boostScale * heat) / (boostScale * temperature) =
      heat / temperature := by
  field_simp

#print axioms GravityScreening.lapse_reparametrization_preserves_phase
#print axioms GravityScreening.properFrequency_mul_properDuration
#print axioms GravityScreening.properFrequency_ratio
#print axioms GravityScreening.boost_normalization_cancels

end GravityScreening
