module
public import GravityScreening.ClockToGravityChain

@[expose] public section

/-!
# The clock contraction and the gravitational canonical squeeze

The raw clock weight and the determinant-one gravitational squeeze are
related but are not the same transformation.  This file proves the exact
scale-shape factorization.  The clock contraction `1/q` splits into a common
action scale `d` and an even eigenvalue of a symplectic constitutive shape;
the odd eigenvalue is its reciprocal.
-/

namespace GravityScreening

/-- Orientation-even and orientation-odd internal channel vectors. -/
def evenChannelVector : Fin 2 → ℝ := ![1, 1]
def oddChannelVector : Fin 2 → ℝ := ![1, -1]

/-- Even eigenweight of the determinant-one gravitational shape. -/
noncomputable def gravitySqueezeEvenWeight (q d : ℝ) : ℝ :=
  (1 / q) / d

/-- Odd eigenweight of the determinant-one gravitational shape. -/
noncomputable def gravitySqueezeOddWeight (q d : ℝ) : ℝ :=
  (2 - 1 / q) / d

/-- The raw clock-forced block carries the clock contraction on the even
channel. -/
theorem quarticConstitutive_even_eigenvector (q : ℝ) :
    (constitutiveBlock (lambda4 q)).mulVec evenChannelVector =
      (1 / q) • evenChannelVector := by
  ext i
  fin_cases i <;>
    simp [constitutiveBlock, lambda4, evenChannelVector, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ]

/-- Trace preservation places the missing even-channel response in the odd
channel, whose raw weight is `2-1/q = 1+lambda4`. -/
theorem quarticConstitutive_odd_eigenvector (q : ℝ) :
    (constitutiveBlock (lambda4 q)).mulVec oddChannelVector =
      (2 - 1 / q) • oddChannelVector := by
  ext i
  fin_cases i <;>
    simp [constitutiveBlock, lambda4, oddChannelVector, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ] <;>
    ring

/-- After removing the common scale `d`, the even channel has the normalized
squeeze weight `(1/q)/d`. -/
theorem unimodularConstitutive_even_eigenvector
    (q d : ℝ) (hd0 : d ≠ 0) :
    (unimodularConstitutive (lambda4 q) d).mulVec evenChannelVector =
      gravitySqueezeEvenWeight q d • evenChannelVector := by
  ext i
  fin_cases i <;>
    simp [unimodularConstitutive, constitutiveBlock, lambda4,
      gravitySqueezeEvenWeight, evenChannelVector, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] <;>
    field_simp [hd0] <;>
    ring

/-- The normalized odd-channel weight is `(2-1/q)/d`. -/
theorem unimodularConstitutive_odd_eigenvector
    (q d : ℝ) (hd0 : d ≠ 0) :
    (unimodularConstitutive (lambda4 q) d).mulVec oddChannelVector =
      gravitySqueezeOddWeight q d • oddChannelVector := by
  ext i
  fin_cases i <;>
    simp [unimodularConstitutive, constitutiveBlock, lambda4,
      gravitySqueezeOddWeight, oddChannelVector, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] <;>
    field_simp [hd0] <;>
    ring

/-- The common scale times the normalized even weight reconstructs the Q-clock
retention exactly. -/
theorem clockWeight_eq_scale_mul_squeezeEven
    (q d : ℝ) (hd0 : d ≠ 0) :
    1 / q = d * gravitySqueezeEvenWeight q d := by
  unfold gravitySqueezeEvenWeight
  field_simp [hd0]

/-- The same common scale reconstructs the trace-complementary odd weight. -/
theorem clockPartner_eq_scale_mul_squeezeOdd
    (q d : ℝ) (hd0 : d ≠ 0) :
    2 - 1 / q = d * gravitySqueezeOddWeight q d := by
  unfold gravitySqueezeOddWeight
  field_simp [hd0]

/-- If `d^2=S_Q`, the two normalized squeeze weights are reciprocal, as a
one-canonical-pair symplectic deformation requires. -/
theorem gravitySqueezeWeights_reciprocal
    (q d : ℝ) (hq0 : q ≠ 0) (hd0 : d ≠ 0)
    (hd : d ^ 2 = screening (lambda4 q)) :
    gravitySqueezeEvenWeight q d * gravitySqueezeOddWeight q d = 1 := by
  unfold gravitySqueezeEvenWeight gravitySqueezeOddWeight
  calc
    (1 / q / d) * ((2 - 1 / q) / d) =
        ((2 * q - 1) / q ^ 2) / d ^ 2 := by
      field_simp [hq0, hd0]
    _ = d ^ 2 / d ^ 2 := by
      rw [← quartic_screening_identity q hq0, ← hd]
    _ = 1 := by field_simp [hd0]

/-- The canonical squeeze ratio forced by the clock-completed block is
`2q-1`. -/
theorem gravitySqueezeWeight_ratio
    (q d : ℝ) (hq0 : q ≠ 0) (hd0 : d ≠ 0) :
    gravitySqueezeOddWeight q d / gravitySqueezeEvenWeight q d =
      2 * q - 1 := by
  unfold gravitySqueezeEvenWeight gravitySqueezeOddWeight
  field_simp [hq0, hd0]

/-- Reverse audit: for `q>1`, the gravitational squeeze ratio `2q-1` is not
the square `q^2` of the clock dilation.  Hence a clock step by `log q` cannot
be identified with the canonical squeeze itself. -/
theorem quarticClock_dilation_ne_gravitySqueezeRatio
    (q : ℝ) (hq1 : 1 < q) :
    (1 + lambda4 q) / (1 - lambda4 q) ≠ q ^ 2 := by
  rw [quartic_squeeze_ratio q (by linarith)]
  intro heq
  have hpos : 0 < (q - 1) ^ 2 := by positivity
  nlinarith

#print axioms GravityScreening.quarticConstitutive_even_eigenvector
#print axioms GravityScreening.quarticConstitutive_odd_eigenvector
#print axioms GravityScreening.unimodularConstitutive_even_eigenvector
#print axioms GravityScreening.unimodularConstitutive_odd_eigenvector
#print axioms GravityScreening.clockWeight_eq_scale_mul_squeezeEven
#print axioms GravityScreening.clockPartner_eq_scale_mul_squeezeOdd
#print axioms GravityScreening.gravitySqueezeWeights_reciprocal
#print axioms GravityScreening.gravitySqueezeWeight_ratio
#print axioms GravityScreening.quarticClock_dilation_ne_gravitySqueezeRatio

end GravityScreening
