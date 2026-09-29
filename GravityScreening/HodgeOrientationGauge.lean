module
public import GravityScreening.HodgeGaussianUniqueness

@[expose] public section

/-!
# Hodge orientation as a response-basis gauge

The real doubled response has two sign branches, `R(l)` and `R(-l)`.  This
file proves that they are related by an orthogonal involution which fixes the
physical TT coordinates and reverses both Hodge-partner coordinates.  It
exchanges the two realified chiral planes and conjugates one response branch
to the other.

Consequently every orientation-even quantity used in the screened linear
gravity calculation factors through the quotient `l ~ -l`.  Selecting a sign
is required only for an orientation-odd observable; it is not an additional
premise for the determinant, Gaussian mass, Fisher scalar, or screened source
coefficient.
-/

namespace GravityScreening

/-- Fix the physical TT pair and reverse the independent Hodge partner pair. -/
def hodgePartnerFlip : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1,0,0,0; 0,1,0,0; 0,0,-1,0; 0,0,0,-1]

/-- The Hodge-partner flip is self-adjoint. -/
theorem hodgePartnerFlip_transpose :
    hodgePartnerFlip.transpose = hodgePartnerFlip := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [hodgePartnerFlip, Matrix.transpose_apply]

/-- The Hodge-partner flip is an involution, hence orthogonal. -/
theorem hodgePartnerFlip_sq :
    hodgePartnerFlip * hodgePartnerFlip = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [hodgePartnerFlip, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Conjugation by the flip reverses realified chirality. -/
theorem hodgePartnerFlip_conj_chirality :
    hodgePartnerFlip * realifiedChirality * hodgePartnerFlip =
      -realifiedChirality := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [hodgePartnerFlip, realifiedChirality,
      Matrix.mul_apply, Fin.sum_univ_succ]

/-- The flip exchanges the plus and minus realified chiral planes. -/
theorem hodgePartnerFlip_plus (x₁ x₂ : ℝ) :
    hodgePartnerFlip.mulVec (realifiedPlus x₁ x₂) =
      realifiedMinus x₁ x₂ := by
  funext i
  fin_cases i <;>
    norm_num [hodgePartnerFlip, realifiedPlus, realifiedMinus,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- The flip exchanges the minus and plus realified chiral planes. -/
theorem hodgePartnerFlip_minus (x₁ x₂ : ℝ) :
    hodgePartnerFlip.mulVec (realifiedMinus x₁ x₂) =
      realifiedPlus x₁ x₂ := by
  funext i
  fin_cases i <;>
    norm_num [hodgePartnerFlip, realifiedPlus, realifiedMinus,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- The two signs of the doubled response are orthogonally conjugate. -/
theorem realDoubledResponse_neg_conjugate (l : ℝ) :
    hodgePartnerFlip.transpose * realDoubledResponse l * hodgePartnerFlip =
      realDoubledResponse (-l) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [hodgePartnerFlip, realDoubledResponse,
      Matrix.transpose_apply, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The same change of basis converts the real quadratic kinetic form at
`l` into the form at `-l`. -/
theorem doubledHodgeKinetic_partnerFlip
    (l x₁ x₂ y₁ y₂ : ℝ) :
    doubledHodgeKinetic l x₁ x₂ (-y₁) (-y₂) =
      doubledHodgeKinetic (-l) x₁ x₂ y₁ y₂ := by
  simp [doubledHodgeKinetic, hodgePairNormSq, hodgePairCross]
  ring

/-- The parity-even response data used by the gravity calculation factor
through the sign quotient. -/
theorem orientationEven_response_sign_quotient (l : ℝ) :
    screening (-l) = screening l ∧
      doubledTTGaussianMass (-l) = doubledTTGaussianMass l ∧
      doubledTTGaussianFisher (-l) = doubledTTGaussianFisher l := by
  constructor
  · simp [screening]
  constructor
  · simp [doubledTTGaussianMass, screening]
  · exact doubledTTGaussianFisher_neg l

/-- At the quartic point, choosing the opposite Hodge labeling changes the
matrix sign branch but changes none of the orientation-even screening data. -/
theorem quartic_orientation_sign_is_gauge
    (q : ℝ) :
    hodgePartnerFlip.transpose *
        realDoubledResponse (lambda4 q) * hodgePartnerFlip =
          realDoubledResponse (-lambda4 q) ∧
      screening (-lambda4 q) = screening (lambda4 q) ∧
      doubledTTGaussianMass (-lambda4 q) =
        doubledTTGaussianMass (lambda4 q) ∧
      doubledTTGaussianFisher (-lambda4 q) =
        doubledTTGaussianFisher (lambda4 q) := by
  exact ⟨realDoubledResponse_neg_conjugate (lambda4 q),
    orientationEven_response_sign_quotient (lambda4 q)⟩

#print axioms GravityScreening.hodgePartnerFlip_transpose
#print axioms GravityScreening.hodgePartnerFlip_sq
#print axioms GravityScreening.hodgePartnerFlip_conj_chirality
#print axioms GravityScreening.hodgePartnerFlip_plus
#print axioms GravityScreening.hodgePartnerFlip_minus
#print axioms GravityScreening.realDoubledResponse_neg_conjugate
#print axioms GravityScreening.doubledHodgeKinetic_partnerFlip
#print axioms GravityScreening.orientationEven_response_sign_quotient
#print axioms GravityScreening.quartic_orientation_sign_is_gauge

end GravityScreening
