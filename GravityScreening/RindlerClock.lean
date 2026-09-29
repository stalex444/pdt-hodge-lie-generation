module
public import GravityScreening.TimeDilation

@[expose] public section

/-!
# Conditional Rindler interpretation of the quartic modular line

Under the standard Bisognano--Wichmann/Unruh normalization, a dimensionless
modular energy `log q` is converted for a proper acceleration `a` to the local
energy `(a / (2*pi)) * log q`.  This file proves the exact scalar chain from
that energy to the thermal weight `1/q`, the defect `lambda4 q`, and the
screening complement.
-/

namespace GravityScreening

/-- Unruh temperature in natural units for proper acceleration `a`. -/
noncomputable def unruhTemperature (a : ℝ) : ℝ :=
  a / (2 * Real.pi)

/-- Proper Rindler energy of a modular line with eigenvalue `1/q`. -/
noncomputable def rindlerClockEnergy (q a : ℝ) : ℝ :=
  unruhTemperature a * Real.log q

/-- The quartic clock energy is the Unruh temperature times its dimensionless
modular gap. -/
theorem rindlerClockEnergy_eq_temperature_mul_log (q a : ℝ) :
    rindlerClockEnergy q a = unruhTemperature a * Real.log q := rfl

/-- At nonzero acceleration, the clock energy in thermal units is exactly
`log q`; gravitational redshift changes energy and temperature together. -/
theorem rindlerClockEnergy_div_temperature
    (q a : ℝ) (ha : 0 < a) :
    rindlerClockEnergy q a / unruhTemperature a = Real.log q := by
  unfold rindlerClockEnergy unruhTemperature
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hT : a / (2 * Real.pi) ≠ 0 := div_ne_zero (ne_of_gt ha) hpi
  field_simp

/-- The Boltzmann weight of the Rindler clock line is exactly its modular
eigenvalue `1/q`. -/
theorem rindlerClock_thermalWeight_eq_inv
    (q a : ℝ) (hq : 0 < q) (ha : 0 < a) :
    Real.exp (-(rindlerClockEnergy q a / unruhTemperature a)) =
      1 / q := by
  rw [rindlerClockEnergy_div_temperature q a ha]
  rw [Real.exp_neg, Real.exp_log hq]
  simp [one_div]

/-- One minus the Rindler thermal weight is the quartic inverse-step defect. -/
theorem rindlerClock_thermalDefect_eq_lambda4
    (q a : ℝ) (hq : 0 < q) (ha : 0 < a) :
    1 - Real.exp (-(rindlerClockEnergy q a / unruhTemperature a)) =
      lambda4 q := by
  rw [rindlerClock_thermalWeight_eq_inv q a hq ha]
  rfl

/-- Completing the Rindler thermal defect as a normalized two-channel
amplitude gives exactly the screening coefficient. -/
theorem rindlerClock_screening_chain
    (q a : ℝ) (hq : 0 < q) (ha : 0 < a) :
    1 -
        (1 - Real.exp
          (-(rindlerClockEnergy q a / unruhTemperature a))) ^ 2 =
      screening (lambda4 q) := by
  rw [rindlerClock_thermalDefect_eq_lambda4 q a hq ha]
  rfl

/-- A unit of dimensionless modular time has proper duration `2*pi/a` in the
standard Rindler normalization. -/
noncomputable def rindlerModularUnitDuration (a : ℝ) : ℝ :=
  2 * Real.pi / a

/-- The energy accumulated through one Rindler modular unit is `log q`. -/
theorem rindlerClockEnergy_mul_modularUnitDuration
    (q a : ℝ) (ha : 0 < a) :
    rindlerClockEnergy q a * rindlerModularUnitDuration a =
      Real.log q := by
  unfold rindlerClockEnergy unruhTemperature rindlerModularUnitDuration
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have ha0 : a ≠ 0 := ne_of_gt ha
  field_simp

#print axioms GravityScreening.rindlerClockEnergy_eq_temperature_mul_log
#print axioms GravityScreening.rindlerClockEnergy_div_temperature
#print axioms GravityScreening.rindlerClock_thermalWeight_eq_inv
#print axioms GravityScreening.rindlerClock_thermalDefect_eq_lambda4
#print axioms GravityScreening.rindlerClock_screening_chain
#print axioms GravityScreening.rindlerClockEnergy_mul_modularUnitDuration

end GravityScreening
