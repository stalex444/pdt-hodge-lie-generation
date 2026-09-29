module
public import GravityScreening.CanonicalEnergy

@[expose] public section

/-!
# Horizon-cut evolution versus coupling renormalization

The semiclassical crossed-product horizon identity has scalar form

`q + K + inverseG * A / 4 = 0`,

where `q` is the asymptotic charge, `K` is the one-sided modular Hamiltonian,
and `A/(4G)` is the area term.  This file separates evolution between cuts at
fixed coupling from a change of coupling between descriptions.
-/

namespace GravityScreening

/-- Scalar residual of the horizon-cut constraint. -/
noncomputable def horizonConstraintResidual
    (charge modularEnergy inverseG area : ℝ) : ℝ :=
  charge + modularEnergy + inverseG * area / 4

/-- With common asymptotic charge and fixed inverse coupling, the change of
area charge is minus the change of one-sided modular energy. -/
theorem fixedCoupling_cut_balance
    (charge K0 K1 inverseG A0 A1 : ℝ)
    (h0 : horizonConstraintResidual charge K0 inverseG A0 = 0)
    (h1 : horizonConstraintResidual charge K1 inverseG A1 = 0) :
    inverseG * (A1 - A0) / 4 = -(K1 - K0) := by
  unfold horizonConstraintResidual at h0 h1
  linarith

/-- If the later modular contribution is retained with weight `s`, the area
change at fixed coupling carries the complementary weight `1-s`. -/
theorem retainedModularEnergy_cut_balance
    (charge K inverseG A0 A1 s : ℝ)
    (h0 : horizonConstraintResidual charge K inverseG A0 = 0)
    (h1 : horizonConstraintResidual charge (s * K) inverseG A1 = 0) :
    inverseG * (A1 - A0) / 4 = (1 - s) * K := by
  have h := fixedCoupling_cut_balance charge K (s * K)
    inverseG A0 A1 h0 h1
  linarith

/-- Scaling the modular term and inverse coupling together while keeping the
same asymptotic charge leaves a residual `(1-s)q`. -/
theorem commonCharge_uniformScaling_residual
    (charge K inverseG area s : ℝ)
    (h0 : horizonConstraintResidual charge K inverseG area = 0) :
    horizonConstraintResidual charge (s * K) (s * inverseG) area =
      (1 - s) * charge := by
  unfold horizonConstraintResidual at h0 ⊢
  calc
    charge + s * K + s * inverseG * area / 4 =
        s * (charge + K + inverseG * area / 4) + (1 - s) * charge := by ring
    _ = (1 - s) * charge := by rw [h0]; ring

/-- Consequently a nontrivial uniform response cannot satisfy both
constraints while a nonzero asymptotic charge is held fixed. -/
theorem commonCharge_blocks_uniformScaling
    (charge K inverseG area s : ℝ)
    (hs : s ≠ 1)
    (h0 : horizonConstraintResidual charge K inverseG area = 0)
    (h1 : horizonConstraintResidual charge (s * K)
      (s * inverseG) area = 0) :
    charge = 0 := by
  rw [commonCharge_uniformScaling_residual charge K inverseG area s h0] at h1
  have hne : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs)
  exact (mul_eq_zero.mp h1).resolve_left hne

/-- If the asymptotic charge is scaled together with the modular and area
coefficients, the homogeneous constraint is preserved. -/
theorem scaledDescription_preserves_constraint
    (charge K inverseG area s : ℝ)
    (h0 : horizonConstraintResidual charge K inverseG area = 0) :
    horizonConstraintResidual (s * charge) (s * K)
      (s * inverseG) area = 0 := by
  unfold horizonConstraintResidual at h0 ⊢
  calc
    s * charge + s * K + s * inverseG * area / 4 =
        s * (charge + K + inverseG * area / 4) := by ring
    _ = 0 := by rw [h0]; ring

/-- In the charge-subtracted local relation, scaling the modular and inverse
coupling terms together preserves the constraint at the same area. -/
theorem localSubtracted_uniformScaling
    (K inverseG area s : ℝ)
    (h0 : horizonConstraintResidual 0 K inverseG area = 0) :
    horizonConstraintResidual 0 (s * K) (s * inverseG) area = 0 := by
  simpa using scaledDescription_preserves_constraint 0 K inverseG area s h0

#print axioms GravityScreening.fixedCoupling_cut_balance
#print axioms GravityScreening.retainedModularEnergy_cut_balance
#print axioms GravityScreening.commonCharge_uniformScaling_residual
#print axioms GravityScreening.commonCharge_blocks_uniformScaling
#print axioms GravityScreening.scaledDescription_preserves_constraint
#print axioms GravityScreening.localSubtracted_uniformScaling

end GravityScreening
