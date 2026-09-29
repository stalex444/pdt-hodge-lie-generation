module
public import GravityScreening.SymplecticReduction
public import GravityScreening.SpinTwoDegreeAudit

@[expose] public section

/-!
# Source coupling in the first-order canonical realization

The quartic response equations can arise from one canonical position-momentum
pair rather than from two independent second-order fields.  This file proves
the exact variations and identifies them with the doubled electric and partner
equations after the determinant-one constitutive normalization.
-/

namespace GravityScreening

section FirstOrderSource

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The first-order bilinear mode with a source coupled only to the canonical
position coordinate. -/
noncomputable def firstOrderBilinearSourcedMode
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (J : V →ₗ[ℝ] ℝ)
    (a c s : ℝ) (position velocity momentum : V) : ℝ :=
  firstOrderBilinearMode B a c s position velocity momentum + J position

/-- Formal first variation in the position direction. -/
noncomputable def firstOrderPositionVariation
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (J : V →ₗ[ℝ] ℝ)
    (a c s : ℝ) (position momentum variation : V) : ℝ :=
  a * (-c * B variation position + s * B variation momentum) + J variation

/-- Exact finite increment in the position direction. -/
theorem firstOrderBilinearSourcedMode_varyPosition
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (J : V →ₗ[ℝ] ℝ)
    (hsymm : ∀ x y, B x y = B y x)
    (a c s : ℝ) (position velocity momentum variation : V) (t : ℝ) :
    firstOrderBilinearSourcedMode B J a c s
        (position + t • variation) velocity momentum =
      firstOrderBilinearSourcedMode B J a c s
          position velocity momentum +
        t * firstOrderPositionVariation B J a c s
          position momentum variation -
        a * c * t ^ 2 / 2 * B variation variation := by
  unfold firstOrderBilinearSourcedMode firstOrderBilinearMode
    firstOrderPositionVariation
  simp only [map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul]
  rw [hsymm position variation]
  ring

/-- Exact finite increment in the canonical-momentum direction. -/
theorem firstOrderBilinearSourcedMode_varyMomentum
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (J : V →ₗ[ℝ] ℝ)
    (hsymm : ∀ x y, B x y = B y x)
    (a c s : ℝ) (position velocity momentum variation : V) (t : ℝ) :
    firstOrderBilinearSourcedMode B J a c s
        position velocity (momentum + t • variation) =
      firstOrderBilinearSourcedMode B J a c s
          position velocity momentum +
        t * momentumVariation B a c s
          position velocity momentum variation -
        a * c * t ^ 2 / 2 * B variation variation := by
  unfold firstOrderBilinearSourcedMode firstOrderBilinearMode
    momentumVariation
  simp only [map_add, map_sub, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul]
  rw [hsymm position variation, hsymm momentum variation]
  ring

/-- With the determinant-one constitutive shape and common scale `d`, the
position equation is exactly the negative doubled electric equation. -/
theorem normalized_firstOrder_positionVariation_eq_doubled
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (J : V →ₗ[ℝ] ℝ)
    (l d : ℝ) (position momentum variation : V) (hd0 : d ≠ 0) :
    firstOrderPositionVariation B J d (1 / d) (l / d)
        position momentum variation =
      -doubledElectricFirstVariation l B J
        position momentum variation := by
  unfold firstOrderPositionVariation doubledElectricFirstVariation
  field_simp [hd0]
  ring

/-- At zero velocity, the canonical-momentum equation is exactly the negative
doubled source-free partner equation. -/
theorem normalized_firstOrder_momentumVariation_eq_doubled
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (l d : ℝ) (position momentum variation : V) (hd0 : d ≠ 0) :
    momentumVariation B d (1 / d) (l / d)
        position 0 momentum variation =
      -doubledPartnerFirstVariation l B
        position momentum variation := by
  unfold momentumVariation doubledPartnerFirstVariation
  simp only [zero_add, map_sub, map_smul, smul_eq_mul]
  field_simp [hd0]
  ring

/-- The stationary Euler equations of the normalized first-order action are
equivalent to the two doubled variational equations.  This realizes the two
entries as one canonical pair rather than two independent configuration
fields. -/
theorem normalized_firstOrder_stationary_iff_doubled
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (J : V →ₗ[ℝ] ℝ)
    (l d : ℝ) (position momentum : V) (hd0 : d ≠ 0) :
    (∀ variation,
        firstOrderPositionVariation B J d (1 / d) (l / d)
          position momentum variation = 0) ∧
      (∀ variation,
        momentumVariation B d (1 / d) (l / d)
          position 0 momentum variation = 0) ↔
    (∀ variation,
        doubledElectricFirstVariation l B J
          position momentum variation = 0) ∧
      (∀ variation,
        doubledPartnerFirstVariation l B
          position momentum variation = 0) := by
  constructor
  · rintro ⟨hposition, hmomentum⟩
    constructor
    · intro variation
      have h := hposition variation
      rw [normalized_firstOrder_positionVariation_eq_doubled
        B J l d position momentum variation hd0] at h
      linarith
    · intro variation
      have h := hmomentum variation
      rw [normalized_firstOrder_momentumVariation_eq_doubled
        B l d position momentum variation hd0] at h
      linarith
  · rintro ⟨helectric, hpartner⟩
    constructor
    · intro variation
      rw [normalized_firstOrder_positionVariation_eq_doubled
        B J l d position momentum variation hd0]
      simp [helectric variation]
    · intro variation
      rw [normalized_firstOrder_momentumVariation_eq_doubled
        B l d position momentum variation hd0]
      simp [hpartner variation]

#print axioms GravityScreening.firstOrderBilinearSourcedMode_varyPosition
#print axioms GravityScreening.firstOrderBilinearSourcedMode_varyMomentum
#print axioms GravityScreening.normalized_firstOrder_positionVariation_eq_doubled
#print axioms GravityScreening.normalized_firstOrder_momentumVariation_eq_doubled
#print axioms GravityScreening.normalized_firstOrder_stationary_iff_doubled

end FirstOrderSource

end GravityScreening
