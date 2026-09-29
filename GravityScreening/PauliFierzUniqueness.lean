module
public import GravityScreening.ElectricSourceFrame

@[expose] public section

/-!
# Uniqueness of the flat massless spin-two normalization

For the standard five-term, local, two-derivative operator on a symmetric
rank-two field, the linearized divergence identity gives three coefficient
relations.  Formal self-adjointness gives the fourth.  This file proves the
resulting algebraic fact: every coefficient is fixed by the coefficient of
the wave term.

The tensor-calculus derivation of the four hypotheses is not encoded here.
The result isolates the finite-dimensional coefficient theorem used by that
standard derivation.
-/

namespace GravityScreening

/-- The four Ward/self-adjointness relations for the standard five-term
massless spin-two operator leave only its overall scale.  With the convention
that symmetrization includes a factor `1/2`, the coefficient pattern is
`(a,-2a,a,a,-a)`. -/
theorem pauliFierz_coefficients_unique
    (a b c d e : ℝ)
    (hdivergenceWave : a + b / 2 = 0)
    (hdivergenceDouble : b / 2 + d = 0)
    (hdivergenceTrace : c + e = 0)
    (hselfAdjoint : c = d) :
    b = -2 * a ∧ c = a ∧ d = a ∧ e = -a := by
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- Conversely, the Pauli--Fierz coefficient pattern satisfies all three
divergence relations and the self-adjointness relation for every scale. -/
theorem pauliFierz_scaledPattern_satisfies_relations
    (scale : ℝ) :
    scale + (-2 * scale) / 2 = 0 ∧
      (-2 * scale) / 2 + scale = 0 ∧
      scale + (-scale) = 0 ∧
      scale = scale := by
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

/-- Once the wave-term coefficient is the screening factor, the Ward and
self-adjointness relations force the complete linear spin-two operator to be
the same screening factor times the Pauli--Fierz operator. -/
theorem waveNormalization_forces_fullPauliFierzNormalization
    (l a b c d e : ℝ)
    (hwave : a = screening l)
    (hdivergenceWave : a + b / 2 = 0)
    (hdivergenceDouble : b / 2 + d = 0)
    (hdivergenceTrace : c + e = 0)
    (hselfAdjoint : c = d) :
    a = screening l ∧
      b = -2 * screening l ∧
      c = screening l ∧
      d = screening l ∧
      e = -screening l := by
  have hunique := pauliFierz_coefficients_unique a b c d e
    hdivergenceWave hdivergenceDouble hdivergenceTrace hselfAdjoint
  rcases hunique with ⟨hb, hc, hd, he⟩
  subst a
  exact ⟨rfl, hb, hc, hd, he⟩

/-- Quartic specialization: fixing the propagating wave coefficient to the
Q-residue coefficient fixes every coefficient of the standard massless
spin-two operator to the same overall quartic scale. -/
theorem quartic_waveNormalization_forces_fullPauliFierzNormalization
    (q a b c d e : ℝ) (hq : q ≠ 0)
    (hwave : a = screening (lambda4 q))
    (hdivergenceWave : a + b / 2 = 0)
    (hdivergenceDouble : b / 2 + d = 0)
    (hdivergenceTrace : c + e = 0)
    (hselfAdjoint : c = d) :
    a = (2 * q - 1) / q ^ 2 ∧
      b = -2 * ((2 * q - 1) / q ^ 2) ∧
      c = (2 * q - 1) / q ^ 2 ∧
      d = (2 * q - 1) / q ^ 2 ∧
      e = -((2 * q - 1) / q ^ 2) := by
  have hfull := waveNormalization_forces_fullPauliFierzNormalization
    (lambda4 q) a b c d e hwave hdivergenceWave hdivergenceDouble
      hdivergenceTrace hselfAdjoint
  rw [quartic_screening_identity q hq] at hfull
  exact hfull

#print axioms GravityScreening.pauliFierz_coefficients_unique
#print axioms GravityScreening.pauliFierz_scaledPattern_satisfies_relations
#print axioms GravityScreening.waveNormalization_forces_fullPauliFierzNormalization
#print axioms GravityScreening.quartic_waveNormalization_forces_fullPauliFierzNormalization

end GravityScreening
