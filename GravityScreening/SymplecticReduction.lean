module
public import GravityScreening.EffectiveGravityClosure

@[expose] public section

/-!
# Uniform symplectic reduction over an arbitrary self-adjoint spatial form

The scalar first-order mode calculation extends without choosing a Fourier
basis.  This file treats the spatial derivative operator only through its
symmetric bilinear form.  The internal determinant-one squeeze then reduces
uniformly over every vector in the field space.

This proves the propagating-sector operator algebra.  It does not identify the
bilinear form with the sourced Pauli--Fierz constraint complex.
-/

namespace GravityScreening

section BilinearReduction

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- A first-order doubled action density over an arbitrary real bilinear form.
The first vector is the selected field, the second is its velocity, and the
third is the canonical dual partner. -/
noncomputable def firstOrderBilinearMode
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (a c s : ℝ) (position velocity momentum : V) : ℝ :=
  a * (B momentum velocity -
    (c * B position position - 2 * s * B position momentum +
      c * B momentum momentum) / 2)

/-- The canonical partner selected by its stationary equation. -/
noncomputable def stationaryBilinearMomentum
    (c s : ℝ) (position velocity : V) : V :=
  (1 / c) • (velocity + s • position)

/-- The formal first variation of the doubled action in a momentum
direction.  This isolates the equation used to eliminate the dual partner. -/
noncomputable def momentumVariation
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (a c s : ℝ) (position velocity momentum variation : V) : ℝ :=
  a * B variation (velocity + s • position - c • momentum)

/-- The displayed canonical partner annihilates the momentum variation for
every test direction. -/
theorem stationaryBilinearMomentum_is_stationary
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (a c s : ℝ) (position velocity variation : V) (hc : c ≠ 0) :
    momentumVariation B a c s position velocity
        (stationaryBilinearMomentum c s position velocity) variation = 0 := by
  unfold momentumVariation stationaryBilinearMomentum
  have hcinv : c * (1 / c) = 1 := by field_simp
  rw [smul_smul, hcinv, one_smul]
  simp

/-- Eliminating the canonical partner works for every symmetric bilinear
spatial operator at once.  No diagonalization or mode-by-mode assumption is
used in the statement. -/
theorem firstOrderBilinearMode_at_stationary
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsymm : ∀ x y, B x y = B y x)
    (a c s : ℝ) (position velocity : V)
    (hc : c ≠ 0) (hcs : c ^ 2 - s ^ 2 = 1) :
    firstOrderBilinearMode B a c s position velocity
        (stationaryBilinearMomentum c s position velocity) =
      a / (2 * c) *
        (B velocity velocity - B position position +
          2 * s * B position velocity) := by
  have hvs : B velocity position = B position velocity :=
    hsymm velocity position
  have hc2 : c ^ 2 = 1 + s ^ 2 := by linarith
  unfold firstOrderBilinearMode stationaryBilinearMomentum
  simp only [map_smul, map_add, LinearMap.smul_apply,
    LinearMap.add_apply, smul_eq_mul]
  rw [hvs]
  field_simp [hc]
  rw [hc2]
  ring

/-- With the determinant defect `d` used both as the common action scale and
to normalize the constitutive shape, the even operator coefficient is exactly
`1-l²`, uniformly on the whole field space. -/
theorem quarticScale_bilinear_reduction
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsymm : ∀ x y, B x y = B y x)
    (l d : ℝ) (position velocity : V)
    (hd : d ^ 2 = screening l) (hd0 : d ≠ 0) :
    firstOrderBilinearMode B d (1 / d) (l / d) position velocity
        (stationaryBilinearMomentum (1 / d) (l / d)
          position velocity) =
      screening l / 2 *
        (B velocity velocity - B position position +
          2 * (l / d) * B position velocity) := by
  have hc : (1 / d : ℝ) ≠ 0 := one_div_ne_zero hd0
  have hcs : (1 / d : ℝ) ^ 2 - (l / d) ^ 2 = 1 := by
    unfold screening at hd
    field_simp [hd0]
    nlinarith
  rw [firstOrderBilinearMode_at_stationary B hsymm d (1 / d) (l / d)
    position velocity hc hcs]
  rw [← hd]
  field_simp [hd0]

/-- Pairing the two opposite orientations cancels the polarization boundary
term.  The orientation-even reduced action is therefore precisely `a/c`
times the undeformed second-order action for any symmetric spatial operator. -/
theorem orientationEven_bilinear_reduction
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsymm : ∀ x y, B x y = B y x)
    (a c s : ℝ) (position velocity : V)
    (hc : c ≠ 0) (hcs : c ^ 2 - s ^ 2 = 1) :
    (firstOrderBilinearMode B a c s position velocity
          (stationaryBilinearMomentum c s position velocity) +
        firstOrderBilinearMode B a c (-s) position velocity
          (stationaryBilinearMomentum c (-s) position velocity)) / 2 =
      a / (2 * c) *
        (B velocity velocity - B position position) := by
  rw [firstOrderBilinearMode_at_stationary B hsymm a c s
    position velocity hc hcs]
  have hcs_neg : c ^ 2 - (-s) ^ 2 = 1 := by nlinarith
  rw [firstOrderBilinearMode_at_stationary B hsymm a c (-s)
    position velocity hc hcs_neg]
  ring

/-- At the determinant-defect normalization, the orientation-even operator
reduction carries exactly the full screening coefficient `1-l²`. -/
theorem quarticScale_orientationEven_bilinear_reduction
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsymm : ∀ x y, B x y = B y x)
    (l d : ℝ) (position velocity : V)
    (hd : d ^ 2 = screening l) (hd0 : d ≠ 0) :
    (firstOrderBilinearMode B d (1 / d) (l / d) position velocity
          (stationaryBilinearMomentum (1 / d) (l / d)
            position velocity) +
        firstOrderBilinearMode B d (1 / d) (-(l / d)) position velocity
          (stationaryBilinearMomentum (1 / d) (-(l / d))
            position velocity)) / 2 =
      screening l / 2 *
        (B velocity velocity - B position position) := by
  have hc : (1 / d : ℝ) ≠ 0 := one_div_ne_zero hd0
  have hcs : (1 / d : ℝ) ^ 2 - (l / d) ^ 2 = 1 := by
    unfold screening at hd
    field_simp [hd0]
    nlinarith
  rw [orientationEven_bilinear_reduction B hsymm d (1 / d) (l / d)
    position velocity hc hcs]
  rw [← hd]
  field_simp [hd0]

/-- Symmetry makes the parity-odd mixed term the polarization derivative of
the quadratic spatial form: `B(v,q)+B(q,v)=2B(q,v)`.  Thus, whenever `v` is
the time derivative of `q` and `B` is time independent, the mixed term is a
boundary term. -/
theorem symmetric_mixed_term_is_polarization
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsymm : ∀ x y, B x y = B y x)
    (position velocity : V) :
    B velocity position + B position velocity =
      2 * B position velocity := by
  rw [hsymm velocity position]
  ring

#print axioms GravityScreening.firstOrderBilinearMode_at_stationary
#print axioms GravityScreening.stationaryBilinearMomentum_is_stationary
#print axioms GravityScreening.quarticScale_bilinear_reduction
#print axioms GravityScreening.orientationEven_bilinear_reduction
#print axioms GravityScreening.quarticScale_orientationEven_bilinear_reduction
#print axioms GravityScreening.symmetric_mixed_term_is_polarization

end BilinearReduction

end GravityScreening
