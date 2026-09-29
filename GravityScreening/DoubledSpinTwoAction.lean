module
public import GravityScreening.DoubledSpinTwoOperator

@[expose] public section

/-!
# Quadratic action behind the doubled spin-two operator

This file proves the variational and positivity algebra of the minimal
two-channel completion for an arbitrary symmetric bilinear form.  In a field
theory the bilinear form is obtained by pairing a field with the output of a
formally self-adjoint differential operator.
-/

namespace GravityScreening

section DoubledAction

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Source-free quadratic part of the doubled action. -/
noncomputable def doubledQuadraticEnergy
    (l : ℝ) (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (field partner : V) : ℝ :=
  (B field field + B partner partner -
    l * (B field partner + B partner field)) / 2

/-- Quadratic action with the external source coupled only to the ordinary
field. -/
noncomputable def doubledQuadraticAction
    (l : ℝ) (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (J : V →ₗ[ℝ] ℝ)
    (field partner : V) : ℝ :=
  doubledQuadraticEnergy l B field partner - J field

/-- First variation in the ordinary-field direction. -/
noncomputable def doubledElectricFirstVariation
    (l : ℝ) (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (J : V →ₗ[ℝ] ℝ)
    (field partner variation : V) : ℝ :=
  B variation field - l * B variation partner - J variation

/-- First variation in the source-free partner direction. -/
noncomputable def doubledPartnerFirstVariation
    (l : ℝ) (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (field partner variation : V) : ℝ :=
  B variation partner - l * B variation field

/-- Exact finite increment of the action in an ordinary-field direction.
The coefficient of `t` is the electric Euler equation and the remainder is
quadratic in `t`. -/
theorem doubledQuadraticAction_varyElectric
    (l : ℝ) (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (J : V →ₗ[ℝ] ℝ)
    (hsymm : ∀ x y, B x y = B y x)
    (field partner variation : V) (t : ℝ) :
    doubledQuadraticAction l B J (field + t • variation) partner =
      doubledQuadraticAction l B J field partner +
        t * doubledElectricFirstVariation l B J
          field partner variation +
        t ^ 2 / 2 * B variation variation := by
  unfold doubledQuadraticAction doubledQuadraticEnergy
    doubledElectricFirstVariation
  simp only [map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul]
  rw [hsymm field variation, hsymm partner variation]
  ring

/-- Exact finite increment in a partner-field direction. -/
theorem doubledQuadraticAction_varyPartner
    (l : ℝ) (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (J : V →ₗ[ℝ] ℝ)
    (hsymm : ∀ x y, B x y = B y x)
    (field partner variation : V) (t : ℝ) :
    doubledQuadraticAction l B J field (partner + t • variation) =
      doubledQuadraticAction l B J field partner +
        t * doubledPartnerFirstVariation l B
          field partner variation +
        t ^ 2 / 2 * B variation variation := by
  unfold doubledQuadraticAction doubledQuadraticEnergy
    doubledPartnerFirstVariation
  simp only [map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul]
  rw [hsymm field variation, hsymm partner variation]
  ring

/-- The source-free quadratic energy is a completed square plus the exact
screening remainder. -/
theorem doubledQuadraticEnergy_completedSquare
    (l : ℝ) (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsymm : ∀ x y, B x y = B y x)
    (field partner : V) :
    2 * doubledQuadraticEnergy l B field partner =
      B (field - l • partner) (field - l • partner) +
        screening l * B partner partner := by
  unfold doubledQuadraticEnergy
  simp only [map_sub, map_smul, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul]
  rw [hsymm partner field]
  unfold screening
  ring

/-- On any positive-semidefinite physical mode space, `|l|≤1` makes the
doubled source-free energy nonnegative. -/
theorem doubledQuadraticEnergy_nonneg
    (l : ℝ) (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsymm : ∀ x y, B x y = B y x)
    (hpositive : ∀ x, 0 ≤ B x x)
    (hscreen : 0 ≤ screening l)
    (field partner : V) :
    0 ≤ doubledQuadraticEnergy l B field partner := by
  have hsquare : 0 ≤ B (field - l • partner) (field - l • partner) :=
    hpositive (field - l • partner)
  have hpartner : 0 ≤ screening l * B partner partner :=
    mul_nonneg hscreen (hpositive partner)
  have hsum :
      0 ≤ B (field - l • partner) (field - l • partner) +
        screening l * B partner partner := add_nonneg hsquare hpartner
  rw [← doubledQuadraticEnergy_completedSquare l B hsymm field partner]
    at hsum
  linarith

/-- In the quartic regime `q>1`, the Q mixing is automatically within the
positive range and the doubled energy is nonnegative on every positive
physical mode space. -/
theorem quartic_doubledQuadraticEnergy_nonneg
    (q : ℝ) (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hq : 1 < q)
    (hsymm : ∀ x y, B x y = B y x)
    (hpositive : ∀ x, 0 ≤ B x x)
    (field partner : V) :
    0 ≤ doubledQuadraticEnergy (lambda4 q) B field partner := by
  have hq0 : 0 < q := by linarith
  have hinvpos : 0 < 1 / q := one_div_pos.mpr hq0
  have hinvlt : 1 / q < 1 := by
    rw [div_lt_one hq0]
    exact hq
  have hlower : -1 < lambda4 q := by
    unfold lambda4
    linarith
  have hupper : lambda4 q < 1 := by
    unfold lambda4
    linarith
  exact doubledQuadraticEnergy_nonneg (lambda4 q) B hsymm hpositive
    (le_of_lt (screening_pos ⟨hlower, hupper⟩)) field partner

#print axioms GravityScreening.doubledQuadraticAction_varyElectric
#print axioms GravityScreening.doubledQuadraticAction_varyPartner
#print axioms GravityScreening.doubledQuadraticEnergy_completedSquare
#print axioms GravityScreening.doubledQuadraticEnergy_nonneg
#print axioms GravityScreening.quartic_doubledQuadraticEnergy_nonneg

end DoubledAction

end GravityScreening
