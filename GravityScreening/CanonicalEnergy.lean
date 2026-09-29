module
public import GravityScreening.InformationArea

@[expose] public section

/-!
# Canonical-energy interpretation of Fisher contraction

This file isolates the normalization ambiguity in reading a Fisher metric as
gravitational canonical energy.  Canonical energy is modeled as an inverse
coupling times a squared perturbation amplitude times a fixed shape pairing.
An information contraction fixes the inverse coupling only when the same
normalized geometric perturbation is compared on both sides.
-/

namespace GravityScreening

/-- Scalar normalization model for a gravitational canonical-energy pairing. -/
def canonicalEnergyModel
    (inverseG amplitude shapePairing : ℝ) : ℝ :=
  inverseG * amplitude ^ 2 * shapePairing

/-- For the same nonzero normalized mode, scaling canonical energy by `s` is
equivalent to scaling the inverse gravitational coupling by `s`. -/
theorem canonicalEnergy_same_mode_iff
    (inverseG0 inverseG1 amplitude shapePairing s : ℝ)
    (ha : amplitude ≠ 0) (hshape : shapePairing ≠ 0) :
    canonicalEnergyModel inverseG1 amplitude shapePairing =
        s * canonicalEnergyModel inverseG0 amplitude shapePairing ↔
      inverseG1 = s * inverseG0 := by
  have hfactor : amplitude ^ 2 * shapePairing ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 ha) hshape
  constructor
  · intro h
    apply mul_right_cancel₀ hfactor
    simpa [canonicalEnergyModel, mul_assoc] using h
  · intro h
    simp [canonicalEnergyModel, h]
    ring

/-- At fixed nonzero inverse coupling and shape, the same energy contraction
can instead be absorbed entirely into the squared mode amplitude. -/
theorem canonicalEnergy_fixed_coupling_iff
    (inverseG amplitude0 amplitude1 shapePairing s : ℝ)
    (hG : inverseG ≠ 0) (hshape : shapePairing ≠ 0) :
    canonicalEnergyModel inverseG amplitude1 shapePairing =
        s * canonicalEnergyModel inverseG amplitude0 shapePairing ↔
      amplitude1 ^ 2 = s * amplitude0 ^ 2 := by
  have hfactor : inverseG * shapePairing ≠ 0 := mul_ne_zero hG hshape
  constructor
  · intro h
    apply mul_left_cancel₀ hfactor
    simpa [canonicalEnergyModel, mul_assoc, mul_left_comm, mul_comm] using h
  · intro h
    simp [canonicalEnergyModel, h]
    ring

/-- Scaling inverse Newton coupling by `s` is equivalent to the inverse
screening response `G1=G0/s`. -/
theorem inverseCoupling_scale_iff
    (G0 G1 s : ℝ) (hG0 : G0 ≠ 0) (hG1 : G1 ≠ 0) (hs : s ≠ 0) :
    1 / G1 = s * (1 / G0) ↔ G1 = G0 / s := by
  constructor
  · intro h
    field_simp [hG0, hG1, hs] at h ⊢
    nlinarith
  · intro h
    field_simp [hG0, hG1, hs] at h ⊢
    nlinarith

/-- Conditional quartic canonical-energy bridge: if the quartic Fisher
contraction is identified with the canonical energy of the same nonzero
geometric mode, the gravitational coupling has the exact inverse response. -/
theorem quarticCanonicalEnergy_coupling_iff
    (q G0 G1 amplitude shapePairing : ℝ)
    (ha : amplitude ≠ 0) (hshape : shapePairing ≠ 0)
    (hG0 : G0 ≠ 0) (hG1 : G1 ≠ 0)
    (hS : screening (lambda4 q) ≠ 0) :
    canonicalEnergyModel (1 / G1) amplitude shapePairing =
        screening (lambda4 q) *
          canonicalEnergyModel (1 / G0) amplitude shapePairing ↔
      G1 = G0 / screening (lambda4 q) := by
  rw [canonicalEnergy_same_mode_iff (1 / G0) (1 / G1)
    amplitude shapePairing (screening (lambda4 q)) ha hshape]
  exact inverseCoupling_scale_iff G0 G1 (screening (lambda4 q))
    hG0 hG1 hS

#print axioms GravityScreening.canonicalEnergy_same_mode_iff
#print axioms GravityScreening.canonicalEnergy_fixed_coupling_iff
#print axioms GravityScreening.inverseCoupling_scale_iff
#print axioms GravityScreening.quarticCanonicalEnergy_coupling_iff

end GravityScreening
