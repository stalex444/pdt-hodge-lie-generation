module
public import GravityScreening.RindlerClock

@[expose] public section

/-!
# Tolman-redshifted quartic modular clock

In the stationary near-horizon model, a positive lapse converts the Killing
surface-gravity scale to the local Rindler acceleration by division.  This
file proves that the local temperature and quartic energy obey the same
Tolman redshift, the local proper duration obeys the reciprocal dilation, and
the dimensionless modular phase and thermal weight remain unchanged.
-/

namespace GravityScreening

/-- Local Rindler acceleration in the stationary near-horizon lapse model. -/
noncomputable def localHorizonAcceleration
    (surfaceGravity lapse : ℝ) : ℝ :=
  surfaceGravity / lapse

/-- Local temperature of the stationary horizon observer. -/
noncomputable def localHorizonTemperature
    (surfaceGravity lapse : ℝ) : ℝ :=
  unruhTemperature (localHorizonAcceleration surfaceGravity lapse)

/-- Local energy of a modular line with eigenvalue `1/q`. -/
noncomputable def localQuarticClockEnergy
    (q surfaceGravity lapse : ℝ) : ℝ :=
  rindlerClockEnergy q (localHorizonAcceleration surfaceGravity lapse)

/-- Proper duration of one modular unit for the stationary horizon observer. -/
noncomputable def localModularUnitDuration
    (surfaceGravity lapse : ℝ) : ℝ :=
  rindlerModularUnitDuration
    (localHorizonAcceleration surfaceGravity lapse)

/-- The local acceleration is positive for positive surface gravity and lapse. -/
theorem localHorizonAcceleration_pos
    (surfaceGravity lapse : ℝ)
    (hSurface : 0 < surfaceGravity) (hLapse : 0 < lapse) :
    0 < localHorizonAcceleration surfaceGravity lapse := by
  exact div_pos hSurface hLapse

/-- Tolman's law: lapse times local horizon temperature is independent of the
observer's position in the stationary family. -/
theorem localHorizonTemperature_mul_lapse
    (surfaceGravity lapse : ℝ) (hLapse : lapse ≠ 0) :
    localHorizonTemperature surfaceGravity lapse * lapse =
      unruhTemperature surfaceGravity := by
  unfold localHorizonTemperature localHorizonAcceleration unruhTemperature
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  field_simp

/-- The distinguished modular-line energy has the same Tolman redshift as the
temperature. -/
theorem localQuarticClockEnergy_mul_lapse
    (q surfaceGravity lapse : ℝ) (hLapse : lapse ≠ 0) :
    localQuarticClockEnergy q surfaceGravity lapse * lapse =
      rindlerClockEnergy q surfaceGravity := by
  unfold localQuarticClockEnergy localHorizonAcceleration
    rindlerClockEnergy unruhTemperature
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  field_simp

/-- Gravitational redshift changes the local energy and local temperature
together, leaving their quartic modular ratio fixed. -/
theorem localQuarticClockEnergy_div_temperature
    (q surfaceGravity lapse : ℝ)
    (hSurface : 0 < surfaceGravity) (hLapse : 0 < lapse) :
    localQuarticClockEnergy q surfaceGravity lapse /
        localHorizonTemperature surfaceGravity lapse =
      Real.log q := by
  exact rindlerClockEnergy_div_temperature q
    (localHorizonAcceleration surfaceGravity lapse)
    (localHorizonAcceleration_pos surfaceGravity lapse hSurface hLapse)

/-- The local Boltzmann weight is the original modular eigenvalue `1/q`. -/
theorem localQuarticClock_thermalWeight_eq_inv
    (q surfaceGravity lapse : ℝ) (hq : 0 < q)
    (hSurface : 0 < surfaceGravity) (hLapse : 0 < lapse) :
    Real.exp
        (-(localQuarticClockEnergy q surfaceGravity lapse /
          localHorizonTemperature surfaceGravity lapse)) =
      1 / q := by
  exact rindlerClock_thermalWeight_eq_inv q
    (localHorizonAcceleration surfaceGravity lapse) hq
    (localHorizonAcceleration_pos surfaceGravity lapse hSurface hLapse)

/-- The redshifted thermal defect remains exactly `lambda4 q`. -/
theorem localQuarticClock_thermalDefect_eq_lambda4
    (q surfaceGravity lapse : ℝ) (hq : 0 < q)
    (hSurface : 0 < surfaceGravity) (hLapse : 0 < lapse) :
    1 - Real.exp
        (-(localQuarticClockEnergy q surfaceGravity lapse /
          localHorizonTemperature surfaceGravity lapse)) =
      lambda4 q := by
  rw [localQuarticClock_thermalWeight_eq_inv q surfaceGravity lapse hq
    hSurface hLapse]
  rfl

/-- The complete redshifted quartic chain retains the same screening
coefficient. -/
theorem localQuarticClock_screening_chain
    (q surfaceGravity lapse : ℝ) (hq : 0 < q)
    (hSurface : 0 < surfaceGravity) (hLapse : 0 < lapse) :
    1 -
        (1 - Real.exp
          (-(localQuarticClockEnergy q surfaceGravity lapse /
            localHorizonTemperature surfaceGravity lapse))) ^ 2 =
      screening (lambda4 q) := by
  rw [localQuarticClock_thermalDefect_eq_lambda4 q surfaceGravity lapse hq
    hSurface hLapse]
  rfl

/-- One modular unit takes a lapse-dilated proper duration. -/
theorem localModularUnitDuration_eq_lapse_mul
    (surfaceGravity lapse : ℝ)
    (hSurface : surfaceGravity ≠ 0) (hLapse : lapse ≠ 0) :
    localModularUnitDuration surfaceGravity lapse =
      lapse * rindlerModularUnitDuration surfaceGravity := by
  unfold localModularUnitDuration localHorizonAcceleration
    rindlerModularUnitDuration
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  field_simp

/-- Expressed in Killing time, the same modular interval is independent of
the local lapse. -/
theorem localModularUnit_coordinateDuration
    (surfaceGravity lapse : ℝ)
    (hSurface : surfaceGravity ≠ 0) (hLapse : lapse ≠ 0) :
    localModularUnitDuration surfaceGravity lapse / lapse =
      rindlerModularUnitDuration surfaceGravity := by
  rw [localModularUnitDuration_eq_lapse_mul surfaceGravity lapse hSurface
    hLapse]
  field_simp

/-- Local energy times local proper duration is the invariant modular phase
`log q`. -/
theorem localQuarticClockEnergy_mul_duration
    (q surfaceGravity lapse : ℝ)
    (hSurface : 0 < surfaceGravity) (hLapse : 0 < lapse) :
    localQuarticClockEnergy q surfaceGravity lapse *
        localModularUnitDuration surfaceGravity lapse =
      Real.log q := by
  exact rindlerClockEnergy_mul_modularUnitDuration q
    (localHorizonAcceleration surfaceGravity lapse)
    (localHorizonAcceleration_pos surfaceGravity lapse hSurface hLapse)

#print axioms GravityScreening.localHorizonTemperature_mul_lapse
#print axioms GravityScreening.localQuarticClockEnergy_mul_lapse
#print axioms GravityScreening.localQuarticClockEnergy_div_temperature
#print axioms GravityScreening.localQuarticClock_thermalWeight_eq_inv
#print axioms GravityScreening.localQuarticClock_thermalDefect_eq_lambda4
#print axioms GravityScreening.localQuarticClock_screening_chain
#print axioms GravityScreening.localModularUnitDuration_eq_lapse_mul
#print axioms GravityScreening.localModularUnit_coordinateDuration
#print axioms GravityScreening.localQuarticClockEnergy_mul_duration

end GravityScreening
