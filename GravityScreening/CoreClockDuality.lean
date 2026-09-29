module
public import GravityScreening.KillingRedshift

@[expose] public section

/-!
# Character pairing between observer time and the continuous-core dual action

For the crossed product by modular flow, the dual action at displacement `s`
acts on the implementing clock unitary labelled by `t` through the character
`exp (-i*s*t)` (with the displayed sign convention).  At `s = log q`, this is
the quartic modular phase.  The same displacement scales the core trace by
`exp (-s)`, hence by `1/q`.  This file kernel-checks those scalar consequences
and their compatibility with the stationary lapse map.
-/

namespace GravityScreening

/-- The scalar character in the dual-action convention
`theta_s(lambda_t) = character(s,t) * lambda_t`. -/
noncomputable def coreDualCharacter (s t : ℝ) : ℂ :=
  Complex.exp (-(Complex.I * ((s * t : ℝ) : ℂ)))

/-- The Perron/KMS phase carried by the quartic modular line. -/
noncomputable def quarticModularPhase (q t : ℝ) : ℂ :=
  Complex.exp (-(Complex.I * ((t * Real.log q : ℝ) : ℂ)))

/-- The logarithmic dual displacement produces exactly the quartic modular
character. -/
theorem coreDualCharacter_log_eq_quarticPhase (q t : ℝ) :
    coreDualCharacter (Real.log q) t = quarticModularPhase q t := by
  unfold coreDualCharacter quarticModularPhase
  congr 2
  push_cast
  ring

/-- Every dual character has unit norm. -/
theorem coreDualCharacter_norm (s t : ℝ) :
    ‖coreDualCharacter s t‖ = 1 := by
  unfold coreDualCharacter
  rw [Complex.norm_exp]
  simp

/-- The character is additive in the observer-time label. -/
theorem coreDualCharacter_add (s t u : ℝ) :
    coreDualCharacter s (t + u) =
      coreDualCharacter s t * coreDualCharacter s u := by
  unfold coreDualCharacter
  rw [← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- The character is also additive in the dual displacement. -/
theorem coreDualCharacter_add_displacement (s u t : ℝ) :
    coreDualCharacter (s + u) t =
      coreDualCharacter s t * coreDualCharacter u t := by
  unfold coreDualCharacter
  rw [← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- At the quartic displacement, the character and the core trace carry the
phase `exp(-i*t*log q)` and weight `1/q` simultaneously. -/
theorem quartic_core_clock_trace_pair
    (q t mass : ℝ) (hq : 0 < q) :
    coreDualCharacter (Real.log q) t = quarticModularPhase q t ∧
      coreTraceScale (Real.log q) mass = mass / q := by
  exact ⟨coreDualCharacter_log_eq_quarticPhase q t,
    coreTraceScale_log q mass hq⟩

/-- The same logarithmic displacement gives the quartic phase and the
normalized trace defect `lambda4 q`. -/
theorem quartic_core_clock_defect_pair
    (q t mass : ℝ) (hq : 0 < q) (hmass : mass ≠ 0) :
    coreDualCharacter (Real.log q) t = quarticModularPhase q t ∧
      (mass - coreTraceScale (Real.log q) mass) / mass = lambda4 q := by
  exact ⟨coreDualCharacter_log_eq_quarticPhase q t,
    coreTraceDefect_log q mass hq hmass⟩

/-- Applying the trace-ray defect twice and taking its complement pairs the
same quartic phase with the proposed screening survivor. -/
theorem quartic_core_clock_screening_pair
    (q t mass : ℝ) (hq : 0 < q) (hmass : mass ≠ 0) :
    coreDualCharacter (Real.log q) t = quarticModularPhase q t ∧
      (2 * coreTraceScale (Real.log q) mass -
          coreTraceScale (2 * Real.log q) mass) / mass =
        screening (lambda4 q) := by
  exact ⟨coreDualCharacter_log_eq_quarticPhase q t,
    coreSelfDefect_survivor q mass hq hmass⟩

/-! ## Redshift versus an intrinsic modular shift -/

/-- Shifting the dual displacement from `log q` to `log q + delta` multiplies
the quartic character by the extra phase at `delta`. -/
theorem shiftedQuarticCharacter_factor (q δ t : ℝ) :
    coreDualCharacter (Real.log q + δ) t =
      quarticModularPhase q t * coreDualCharacter δ t := by
  rw [coreDualCharacter_add_displacement]
  rw [coreDualCharacter_log_eq_quarticPhase]

/-- The same intrinsic displacement shift multiplies the quartic core-trace
weight by `exp (-delta)`. -/
theorem coreTraceScale_shift_log
    (q δ mass : ℝ) (hq : 0 < q) :
    coreTraceScale (Real.log q + δ) mass =
      Real.exp (-δ) * (mass / q) := by
  unfold coreTraceScale
  have hneg : -(Real.log q + δ) = -Real.log q + -δ := by ring
  rw [hneg, Real.exp_add, Real.exp_neg, Real.exp_log hq]
  field_simp [ne_of_gt hq]

/-- Unlike lapse reparametrization, an intrinsic shift of the core dual
displacement preserves the quartic trace defect exactly only when it is zero. -/
theorem coreTraceDefect_shift_eq_lambda4_iff
    (q δ mass : ℝ) (hq : 0 < q) (hmass : mass ≠ 0) :
    (mass - coreTraceScale (Real.log q + δ) mass) / mass =
        lambda4 q ↔
      δ = 0 := by
  have hnormalized :
      (mass - coreTraceScale (Real.log q + δ) mass) / mass =
        detailedBalanceDefect 1 (Real.log q + δ) := by
    unfold coreTraceScale detailedBalanceDefect
    field_simp
  rw [hnormalized]
  exact quartic_response_shift_eq_iff q δ hq

/-- Dimensionless modular time accumulated during a local proper-time
interval in the stationary near-horizon model. -/
noncomputable def localModularParameter
    (surfaceGravity lapse properTime : ℝ) : ℝ :=
  localHorizonTemperature surfaceGravity lapse * properTime

/-- The locally redshifted quartic phase. -/
noncomputable def localQuarticModularPhase
    (q surfaceGravity lapse properTime : ℝ) : ℂ :=
  coreDualCharacter (Real.log q)
    (localModularParameter surfaceGravity lapse properTime)

/-- The core character is the ordinary energy-time phase after the local
Rindler energy conversion. -/
theorem localQuarticModularPhase_eq_energyPhase
    (q surfaceGravity lapse properTime : ℝ) :
    localQuarticModularPhase q surfaceGravity lapse properTime =
      Complex.exp
        (-(Complex.I *
          ((localQuarticClockEnergy q surfaceGravity lapse * properTime : ℝ) : ℂ))) := by
  unfold localQuarticModularPhase coreDualCharacter localModularParameter
    localQuarticClockEnergy localHorizonTemperature rindlerClockEnergy
  congr 2
  push_cast
  ring

/-- One local modular unit has accumulated modular parameter exactly one. -/
theorem localModularParameter_unitDuration
    (surfaceGravity lapse : ℝ)
    (hSurface : 0 < surfaceGravity) (hLapse : 0 < lapse) :
    localModularParameter surfaceGravity lapse
        (localModularUnitDuration surfaceGravity lapse) = 1 := by
  unfold localModularParameter localHorizonTemperature
    localModularUnitDuration
  unfold unruhTemperature rindlerModularUnitDuration
  have ha := localHorizonAcceleration_pos surfaceGravity lapse hSurface hLapse
  have ha0 : localHorizonAcceleration surfaceGravity lapse ≠ 0 := ne_of_gt ha
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  field_simp

/-- After one local modular unit, the phase is the lapse-independent quartic
character at parameter one. -/
theorem localQuarticModularPhase_unitDuration
    (q surfaceGravity lapse : ℝ)
    (hSurface : 0 < surfaceGravity) (hLapse : 0 < lapse) :
    localQuarticModularPhase q surfaceGravity lapse
        (localModularUnitDuration surfaceGravity lapse) =
      quarticModularPhase q 1 := by
  unfold localQuarticModularPhase
  rw [localModularParameter_unitDuration surfaceGravity lapse hSurface hLapse]
  exact coreDualCharacter_log_eq_quarticPhase q 1

/-- A common Killing-coordinate interval accumulates the same modular
parameter for every positive lapse when converted to local proper time. -/
theorem localModularParameter_properDuration
    (surfaceGravity lapse coordinateTime : ℝ)
    (hLapse : lapse ≠ 0) :
    localModularParameter surfaceGravity lapse
        (properDuration lapse coordinateTime) =
      unruhTemperature surfaceGravity * coordinateTime := by
  unfold localModularParameter properDuration
  calc
    localHorizonTemperature surfaceGravity lapse *
        (lapse * coordinateTime) =
      (localHorizonTemperature surfaceGravity lapse * lapse) *
        coordinateTime := by ring
    _ = unruhTemperature surfaceGravity * coordinateTime := by
      rw [localHorizonTemperature_mul_lapse surfaceGravity lapse hLapse]

/-- The locally read quartic phase is independent of lapse when all observers
refer to the same Killing-coordinate interval. -/
theorem localQuarticModularPhase_properDuration
    (q surfaceGravity lapse coordinateTime : ℝ)
    (hLapse : lapse ≠ 0) :
    localQuarticModularPhase q surfaceGravity lapse
        (properDuration lapse coordinateTime) =
      coreDualCharacter (Real.log q)
        (unruhTemperature surfaceGravity * coordinateTime) := by
  unfold localQuarticModularPhase
  rw [localModularParameter_properDuration surfaceGravity lapse coordinateTime
    hLapse]

#print axioms GravityScreening.coreDualCharacter_log_eq_quarticPhase
#print axioms GravityScreening.coreDualCharacter_norm
#print axioms GravityScreening.coreDualCharacter_add
#print axioms GravityScreening.coreDualCharacter_add_displacement
#print axioms GravityScreening.quartic_core_clock_trace_pair
#print axioms GravityScreening.quartic_core_clock_defect_pair
#print axioms GravityScreening.quartic_core_clock_screening_pair
#print axioms GravityScreening.shiftedQuarticCharacter_factor
#print axioms GravityScreening.coreTraceScale_shift_log
#print axioms GravityScreening.coreTraceDefect_shift_eq_lambda4_iff
#print axioms GravityScreening.localQuarticModularPhase_eq_energyPhase
#print axioms GravityScreening.localModularParameter_unitDuration
#print axioms GravityScreening.localQuarticModularPhase_unitDuration
#print axioms GravityScreening.localModularParameter_properDuration
#print axioms GravityScreening.localQuarticModularPhase_properDuration

end GravityScreening
