module
public import GravityScreening.HorizonConstraint

@[expose] public section

/-!
# Commuting microscopic/effective horizon evolution

This file models the two independent directions isolated by the horizon
constraint.  Vertical evolution changes modular energy and area at fixed
inverse Newton coupling.  Horizontal matching scales the charge, modular
energy, and inverse coupling together at fixed area.  When the modular-energy
increment is matched by the same coefficient, the two routes give the same
area and preserve the constraint.
-/

namespace GravityScreening

/-- Area at the next cut after a modular-energy increment `deltaK`, with the
inverse Newton coupling held fixed. -/
noncomputable def evolvedHorizonArea
    (inverseG area deltaK : ℝ) : ℝ :=
  area - 4 * deltaK / inverseG

/-- The area update is exactly the one required to preserve the horizon
constraint during a cut-to-cut change of modular energy. -/
theorem horizonConstraintResidual_evolve
    (charge K inverseG area deltaK : ℝ)
    (hG : inverseG ≠ 0) :
    horizonConstraintResidual charge (K + deltaK) inverseG
        (evolvedHorizonArea inverseG area deltaK) =
      horizonConstraintResidual charge K inverseG area := by
  unfold horizonConstraintResidual evolvedHorizonArea
  field_simp
  ring

/-- Scaling both the inverse coupling and the modular-energy increment by the
same nonzero factor leaves the geometric area update unchanged. -/
theorem evolvedHorizonArea_scale_commutes
    (inverseG area deltaK s : ℝ)
    (hG : inverseG ≠ 0) (hs : s ≠ 0) :
    evolvedHorizonArea (s * inverseG) area (s * deltaK) =
      evolvedHorizonArea inverseG area deltaK := by
  unfold evolvedHorizonArea
  field_simp

/-- The microscopic/effective square commutes: evolve at the microscopic
coupling and then scale the whole charge constraint, or first scale the
description and then evolve by the correspondingly scaled modular increment.
Both routes reach the same area and satisfy the effective constraint. -/
theorem matched_horizon_evolution_preserves_constraint
    (charge K inverseG area deltaK s : ℝ)
    (hG : inverseG ≠ 0)
    (h0 : horizonConstraintResidual charge K inverseG area = 0) :
    horizonConstraintResidual (s * charge) (s * (K + deltaK))
        (s * inverseG) (evolvedHorizonArea inverseG area deltaK) = 0 := by
  apply scaledDescription_preserves_constraint
  rw [horizonConstraintResidual_evolve charge K inverseG area deltaK hG]
  exact h0

/-- The endpoint area obtained by effective evolution is the same endpoint
area obtained by microscopic evolution, provided the matching factor is
nonzero. -/
theorem matched_horizon_evolution_same_area
    (inverseG area deltaK s : ℝ)
    (hG : inverseG ≠ 0) (hs : s ≠ 0) :
    evolvedHorizonArea (s * inverseG) area (s * deltaK) =
      evolvedHorizonArea inverseG area deltaK :=
  evolvedHorizonArea_scale_commutes inverseG area deltaK s hG hs

#print axioms GravityScreening.horizonConstraintResidual_evolve
#print axioms GravityScreening.evolvedHorizonArea_scale_commutes
#print axioms GravityScreening.matched_horizon_evolution_preserves_constraint
#print axioms GravityScreening.matched_horizon_evolution_same_area

end GravityScreening
