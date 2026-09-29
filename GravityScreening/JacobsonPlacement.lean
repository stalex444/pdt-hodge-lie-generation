module
public import GravityScreening.ErasureCovariance

@[expose] public section

/-!
# Placement of a response factor in Jacobson's Clausius relation

If the physical heat flux is multiplied by `h` while the horizon
entropy-per-area coefficient is multiplied by `e`, the gravitational coupling
relative to its baseline is multiplied by `h/e`.  This file records the exact
algebraic consequences needed to distinguish a genuine area-density response
from a common rescaling that cancels out of the Clausius relation.
-/

namespace GravityScreening

/-- Relative Jacobson coupling when the heat-flux side is scaled by `h` and
the entropy-density side is scaled by `e`. -/
noncomputable def jacobsonScaledCoupling
    (baselineG heatScale entropyScale : ℝ) : ℝ :=
  heatScale * baselineG / entropyScale

/-- Scaling heat flux and entropy density by the same nonzero number leaves
the gravitational coupling unchanged. -/
theorem jacobsonScaledCoupling_common_cancels
    (baselineG s : ℝ) (hs : s ≠ 0) :
    jacobsonScaledCoupling baselineG s s = baselineG := by
  unfold jacobsonScaledCoupling
  field_simp

/-- Scaling only the entropy-per-area coefficient gives the inverse response
required by the PDT gravity formula. -/
theorem jacobsonScaledCoupling_entropy_only
    (baselineG s : ℝ) :
    jacobsonScaledCoupling baselineG 1 s = baselineG / s := by
  simp [jacobsonScaledCoupling]

/-- Scaling only the physical heat flux gives a direct, rather than inverse,
response of the gravitational coupling. -/
theorem jacobsonScaledCoupling_heat_only
    (baselineG s : ℝ) :
    jacobsonScaledCoupling baselineG s 1 = s * baselineG := by
  simp [jacobsonScaledCoupling]

/-- With nonzero baseline coupling and entropy scale, obtaining the inverse
coupling while fixing the entropy scale to `s` uniquely requires an unscaled
physical heat flux. -/
theorem inverse_response_forces_unscaled_heat
    (baselineG heatScale s : ℝ)
    (hG : baselineG ≠ 0) (hs : s ≠ 0) :
    jacobsonScaledCoupling baselineG heatScale s = baselineG / s ↔
      heatScale = 1 := by
  unfold jacobsonScaledCoupling
  constructor
  · intro h
    field_simp [hG, hs] at h
    exact h
  · intro h
    simp [h]

/-- At the quartic weight, applying the factor on both sides cancels exactly. -/
theorem quartic_common_scaling_cancels
    (q baselineG : ℝ) (hS : screening (lambda4 q) ≠ 0) :
    jacobsonScaledCoupling baselineG
        (screening (lambda4 q)) (screening (lambda4 q)) = baselineG := by
  exact jacobsonScaledCoupling_common_cancels baselineG
    (screening (lambda4 q)) hS

/-- At the quartic weight, placing the response in entropy density alone gives
the exact inverse screening factor. -/
theorem quartic_entropy_placement
    (q baselineG : ℝ) :
    jacobsonScaledCoupling baselineG 1 (screening (lambda4 q)) =
      baselineG / screening (lambda4 q) := by
  exact jacobsonScaledCoupling_entropy_only baselineG
    (screening (lambda4 q))

#print axioms GravityScreening.jacobsonScaledCoupling_common_cancels
#print axioms GravityScreening.jacobsonScaledCoupling_entropy_only
#print axioms GravityScreening.jacobsonScaledCoupling_heat_only
#print axioms GravityScreening.inverse_response_forces_unscaled_heat
#print axioms GravityScreening.quartic_common_scaling_cancels
#print axioms GravityScreening.quartic_entropy_placement

end GravityScreening
