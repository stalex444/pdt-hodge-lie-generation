module
public import GravityScreening.Basic

@[expose] public section

/-!
# Hodge bulk/screen factorization

This file records two distinct orientation-pair identities on one
complexified Lorentzian Hodge pair.  A weighted chiral divide assigns `rho`
and `Q` to the two chiral projectors; multiplying it by its orientation flip
gives the joint scalar `rho * Q`.  A separately normalized chiral response
and its flip give the quartic screening scalar `1 - (lambda4 Q)^2`.

The identities are exact operator algebra.  Interpreting the first operator
as a bulk curvature divide and the second as a physical horizon response is
an explicit PDT placement, not a consequence of the algebra alone.
-/

namespace GravityScreening

open Complex Matrix

noncomputable section

abbrev HodgeSide := Fin 2

/-- Real matrix model of Lorentzian Hodge star on one complexified pair. -/
def hodgeRotation : Matrix HodgeSide HodgeSide ℂ := !![0, -1; 1, 0]

/-- The chirality involution `-i star`. -/
def hodgeChirality : Matrix HodgeSide HodgeSide ℂ :=
  (-Complex.I) • hodgeRotation

def hodgePlus : Matrix HodgeSide HodgeSide ℂ :=
  (2 : ℂ)⁻¹ • (1 + hodgeChirality)

def hodgeMinus : Matrix HodgeSide HodgeSide ℂ :=
  (2 : ℂ)⁻¹ • (1 - hodgeChirality)

/-- The conditional arithmetic divide: `rho` weights one chirality and `Q`
the other. -/
def hodgeDivide (rho q : ℝ) : Matrix HodgeSide HodgeSide ℂ :=
  (rho : ℂ) • hodgePlus + (q : ℂ) • hodgeMinus

/-- Orientation reversal exchanges the two arithmetic weights. -/
def hodgeDivideFlip (rho q : ℝ) : Matrix HodgeSide HodgeSide ℂ :=
  (q : ℂ) • hodgePlus + (rho : ℂ) • hodgeMinus

/-- Pairing the weighted divide with its orientation flip recovers the joint
bulk scalar `rho * Q`. -/
theorem hodgeDivide_mul_flip (rho q : ℝ) :
    hodgeDivide rho q * hodgeDivideFlip rho q =
      ((rho * q : ℝ) : ℂ) • (1 : Matrix HodgeSide HodgeSide ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hodgeDivide, hodgeDivideFlip, hodgePlus, hodgeMinus,
      hodgeChirality, hodgeRotation, Matrix.mul_apply, Fin.sum_univ_two]
    <;> ring_nf
    <;> simp [Complex.I_sq]
    <;> ring

/-- A separately normalized response on the same Hodge pair. -/
def hodgeResponse (l : ℝ) : Matrix HodgeSide HodgeSide ℂ :=
  (1 : Matrix HodgeSide HodgeSide ℂ) + (l : ℂ) • hodgeChirality

def hodgeResponseFlip (l : ℝ) : Matrix HodgeSide HodgeSide ℂ :=
  (1 : Matrix HodgeSide HodgeSide ℂ) - (l : ℂ) • hodgeChirality

/-- Pairing the normalized response with its orientation flip gives the
difference-of-squares screening scalar. -/
theorem hodgeResponse_mul_flip (l : ℝ) :
    hodgeResponse l * hodgeResponseFlip l =
      ((1 - l ^ 2 : ℝ) : ℂ) •
        (1 : Matrix HodgeSide HodgeSide ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hodgeResponse, hodgeResponseFlip, hodgeChirality, hodgeRotation,
      Matrix.mul_apply, Fin.sum_univ_two]
    <;> ring_nf
    <;> simp [Complex.I_sq]
    <;> ring

/-- The two exact products displayed together.  They remain distinct
operators: the first exposes the joint `rho Q` bulk scalar, while the second
exposes the quartic screen factor. -/
theorem hodgeBulkAndQuarticScreen (rho q : ℝ) (hq0 : q ≠ 0) :
    hodgeDivide rho q * hodgeDivideFlip rho q =
        ((rho * q : ℝ) : ℂ) •
          (1 : Matrix HodgeSide HodgeSide ℂ) ∧
      hodgeResponse (lambda4 q) * hodgeResponseFlip (lambda4 q) =
        ((((2 * q - 1) / q ^ 2 : ℝ)) : ℂ) •
          (1 : Matrix HodgeSide HodgeSide ℂ) := by
  constructor
  · exact hodgeDivide_mul_flip rho q
  · rw [hodgeResponse_mul_flip]
    rw [show 1 - lambda4 q ^ 2 = (2 * q - 1) / q ^ 2 by
      exact quartic_screening_identity q hq0]

#print axioms GravityScreening.hodgeBulkAndQuarticScreen

end

end GravityScreening
