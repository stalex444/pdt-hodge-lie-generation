module
public import GravityScreening.HodgeResponseCovariance
public import GravityScreening.TraceFreeResponseUniqueness

@[expose] public section

/-! Response rigidity and one-mode calibration on the geometrically generated
224-dimensional trace-free algebra. Covariance and calibration are explicit
application premises; neither is inferred from a dimension count. -/

namespace GravityScreening.GeometricResponseRigidity

open HodgeResponseCovariance

variable (K : Type*) [Field K]

/-- The sixteen geometric covariance conditions force a scalar response on
the actual trace-free algebra, with determinant given by its dimension. -/
theorem geometric_response_scalar_and_determinant (htwo : (2 : K) ≠ 0)
    (R : ResponseAlgebra K →ₗ[K] ResponseAlgebra K)
    (ha : ∀ p x, R ⁅adjointGenerator K p, x⁆ = ⁅adjointGenerator K p, R x⁆)
    (hh : ∀ x, R ⁅hodgeGenerator K, x⁆ = ⁅hodgeGenerator K, R x⁆) :
    ∃ c : K, R = c • LinearMap.id ∧ LinearMap.det R = c ^ 224 :=
  TraceFreeResponseUniqueness.sl15_scalar_response_determinant htwo R
    (covariant_of_generators K htwo R ha hh)

/-- One nonzero calibration to the proposed ruler fixes the same response's
scalar and determinant. The ruler and its physical calibration are inputs. -/
theorem geometric_response_calibrated_determinant (htwo : (2 : K) ≠ 0)
    (R : ResponseAlgebra K →ₗ[K] ResponseAlgebra K)
    (ha : ∀ p x, R ⁅adjointGenerator K p, x⁆ = ⁅adjointGenerator K p, R x⁆)
    (hh : ∀ x, R ⁅hodgeGenerator K, x⁆ = ⁅hodgeGenerator K, R x⁆)
    (rho q : K) (X : ResponseAlgebra K) (hX : X ≠ 0)
    (hcal : R X = (rho * q) • X) :
    R = (rho * q) • LinearMap.id ∧ LinearMap.det R = (rho * q) ^ 224 :=
  TraceFreeResponseUniqueness.sl15_calibrated_response_determinant htwo R
    (covariant_of_generators K htwo R ha hh) rho q X hX hcal

#print axioms geometric_response_scalar_and_determinant
#print axioms geometric_response_calibrated_determinant

end GravityScreening.GeometricResponseRigidity
