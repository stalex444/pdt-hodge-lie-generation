module
public import GravityScreening.CanonicalEnergy
public import GravityScreening.ClockGravityFactorization

@[expose] public section

/-!
# Direct information-metric route to the Newton response

The finite erasure theorem and the canonical-energy normalization theorem are
composed here without an intervening constitutive matrix.  The explicitly
named physics input is the same-mode Fisher/canonical-energy dictionary at the
microscopic and effective endpoints.  Once the geometric mode, its amplitude,
and its shape pairing are fixed on both sides, the quartic Fisher contraction
forces the inverse Newton coefficient to contract by the same factor.
-/

namespace GravityScreening

/-- A direct capstone for the information-geometric route.  The hypotheses
`hbaselineDictionary` and `heffectiveDictionary` express the restricted
physics identification that the two Fisher metrics are canonical energies of
the same independently normalized gravitational perturbation. -/
theorem quarticInformationMetric_forces_newtonResponse
    {n : ℕ} (q : ℝ) (p tangent : Fin n → ℝ)
    (G0 GQ amplitude shapePairing : ℝ)
    (hq1 : 1 < q) (hp : ∀ i, p i ≠ 0)
    (hG0 : G0 ≠ 0) (hGQ : GQ ≠ 0)
    (hamplitude : amplitude ≠ 0) (hshape : shapePairing ≠ 0)
    (hbaselineDictionary :
      diagonalFisherPair p tangent tangent =
        canonicalEnergyModel (1 / G0) amplitude shapePairing)
    (heffectiveDictionary :
      erasureFisherPair (screening (lambda4 q)) p tangent tangent =
        canonicalEnergyModel (1 / GQ) amplitude shapePairing) :
    GQ = G0 / ((2 * q - 1) / q ^ 2) := by
  have hq0 : q ≠ 0 := by linarith
  have hSpos : 0 < screening (lambda4 q) := by
    rw [quartic_screening_identity q hq0]
    have hnum : 0 < 2 * q - 1 := by linarith
    have hden : 0 < q ^ 2 := by positivity
    exact div_pos hnum hden
  have hS : screening (lambda4 q) ≠ 0 := ne_of_gt hSpos
  have hfisher := erasureFisherPair_eq
    (screening (lambda4 q)) p tangent tangent hS hp
  have henergy :
      canonicalEnergyModel (1 / GQ) amplitude shapePairing =
        screening (lambda4 q) *
          canonicalEnergyModel (1 / G0) amplitude shapePairing := by
    calc
      canonicalEnergyModel (1 / GQ) amplitude shapePairing =
          erasureFisherPair (screening (lambda4 q)) p tangent tangent :=
        heffectiveDictionary.symm
      _ = screening (lambda4 q) *
          diagonalFisherPair p tangent tangent := hfisher
      _ = screening (lambda4 q) *
          canonicalEnergyModel (1 / G0) amplitude shapePairing := by
        rw [hbaselineDictionary]
  have hcoupling :=
    (quarticCanonicalEnergy_coupling_iff q G0 GQ amplitude shapePairing
      hamplitude hshape hG0 hGQ hS).mp henergy
  rw [quartic_screening_identity q hq0] at hcoupling
  exact hcoupling

#print axioms GravityScreening.quarticInformationMetric_forces_newtonResponse

end GravityScreening
