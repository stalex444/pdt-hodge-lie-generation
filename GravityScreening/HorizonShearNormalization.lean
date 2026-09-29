module
public import GravityScreening.HorizonShearBridge

@[expose] public section

/-!
# Physical versus canonically normalized horizon shear

In perturbative gravity one writes the physical metric fluctuation with
`kappa^2 = 32*pi*G`, while the canonically normalized horizon shear variable
has a quadratic null-energy density independent of `G`.  This file proves the
exact conversion between the physical shear norm and the canonical graviton
energy and then specializes the same-physical-shear comparison to the quartic
screening factor.
-/

namespace GravityScreening

/-- The physical shear norm obtained when the canonically normalized shear
coordinate is multiplied by `kappa/2`. -/
noncomputable def physicalShearNormSq
    (kappa canonicalShearNormSq : ℝ) : ℝ :=
  (kappa ^ 2 / 4) * canonicalShearNormSq

/-- With `kappa^2=32*pi*G`, physical shear squared is exactly
`8*pi*G` times the canonically normalized graviton shear energy. -/
theorem physicalShearNormSq_eq_eight_pi_G
    (kappa G canonicalShearNormSq : ℝ)
    (hkappa : kappa ^ 2 = 32 * Real.pi * G) :
    physicalShearNormSq kappa canonicalShearNormSq =
      8 * Real.pi * G * canonicalShearNormSq := by
  unfold physicalShearNormSq
  rw [hkappa]
  ring

/-- Canonical graviton shear energy reconstructed from a fixed physical shear
norm.  This is `physicalShearNormSq/(8*pi*G)`. -/
noncomputable def canonicalEnergyFromPhysicalShear
    (G physicalNormSq : ℝ) : ℝ :=
  canonicalEnergyModel (1 / G) 1 (physicalNormSq / (8 * Real.pi))

/-- The physical/canonical conversion is exactly invertible for nonzero `G`.
-/
theorem canonicalEnergyFromPhysicalShear_recovers
    (kappa G canonicalShearNormSq : ℝ)
    (hG : G ≠ 0) (hkappa : kappa ^ 2 = 32 * Real.pi * G) :
    canonicalEnergyFromPhysicalShear G
        (physicalShearNormSq kappa canonicalShearNormSq) =
      canonicalShearNormSq := by
  rw [physicalShearNormSq_eq_eight_pi_G
    kappa G canonicalShearNormSq hkappa]
  unfold canonicalEnergyFromPhysicalShear canonicalEnergyModel
  field_simp [hG, Real.pi_ne_zero]

/-- For the same nonzero physical shear, a quartic contraction of canonical
graviton energy is equivalent to the screened Newton response.  The fixed
quantity here is the geometric shear, not the canonically rescaled field. -/
theorem quarticCanonicalEnergy_samePhysicalShear_iff_newtonResponse
    (q G0 GQ physicalNormSq : ℝ)
    (hq1 : 1 < q) (hG0 : G0 ≠ 0) (hGQ : GQ ≠ 0)
    (hphysical : physicalNormSq ≠ 0) :
    canonicalEnergyFromPhysicalShear GQ physicalNormSq =
        screening (lambda4 q) *
          canonicalEnergyFromPhysicalShear G0 physicalNormSq ↔
      GQ = G0 / ((2 * q - 1) / q ^ 2) := by
  have hq0 : q ≠ 0 := by linarith
  have hSpos : 0 < screening (lambda4 q) := by
    rw [quartic_screening_identity q hq0]
    have hnum : 0 < 2 * q - 1 := by linarith
    have hden : 0 < q ^ 2 := by positivity
    exact div_pos hnum hden
  have hS : screening (lambda4 q) ≠ 0 := ne_of_gt hSpos
  have hshape : physicalNormSq / (8 * Real.pi) ≠ 0 := by
    exact div_ne_zero hphysical (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  unfold canonicalEnergyFromPhysicalShear
  rw [quarticCanonicalEnergy_coupling_iff
    q G0 GQ 1 (physicalNormSq / (8 * Real.pi))
    one_ne_zero hshape hG0 hGQ hS]
  rw [quartic_screening_identity q hq0]

#print axioms GravityScreening.physicalShearNormSq_eq_eight_pi_G
#print axioms GravityScreening.canonicalEnergyFromPhysicalShear_recovers
#print axioms GravityScreening.quarticCanonicalEnergy_samePhysicalShear_iff_newtonResponse

end GravityScreening
