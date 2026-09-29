module
public import GravityScreening.DoubledTTGaussian
public import GravityScreening.TetrahedralFisherCone

@[expose] public section

/-!
# Information geometry of the doubled TT Gaussian

The real doubled response `R(l) = I + l C` is a precision matrix, where the
realified chirality `C` is a symmetric involution.  This file records three
exact consequences.

* the inverse precision is `R(-l)/(1-l^2)`;
* the affine-invariant Gaussian Fisher metric in the coupling direction is
  `2(1+l^2)/(1-l^2)^2`;
* on `0 <= l < 1`, that scalar is injective, so running the construction
  backwards recovers the Hodge coupling uniquely.

At the quartic residue `l = lambda4 q`, the same Fisher scalar is therefore an
information-geometric fingerprint of the quartic response.  These are purely
mathematical statements; they do not by themselves identify the Gaussian
family with physical gravity.
-/

namespace GravityScreening

/-- The algebraic inverse candidate for the real doubled precision matrix. -/
noncomputable def realDoubledResponseInverse (l : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  (screening l)⁻¹ • realDoubledResponse (-l)

/-- The inverse candidate is a right inverse away from the Hodge boundary. -/
theorem realDoubledResponse_mul_inverse
    (l : ℝ) (hs : screening l ≠ 0) :
    realDoubledResponse l * realDoubledResponseInverse l = 1 := by
  have hs' : 1 - l ^ 2 ≠ 0 := by simpa [screening] using hs
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [realDoubledResponseInverse, realDoubledResponse, screening,
      Matrix.mul_apply, Fin.sum_univ_succ] <;>
    field_simp [hs'] <;> ring

/-- The inverse candidate is also a left inverse away from the Hodge boundary. -/
theorem realDoubledResponse_inverse_mul
    (l : ℝ) (hs : screening l ≠ 0) :
    realDoubledResponseInverse l * realDoubledResponse l = 1 := by
  have hs' : 1 - l ^ 2 ≠ 0 := by simpa [screening] using hs
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [realDoubledResponseInverse, realDoubledResponse, screening,
      Matrix.mul_apply, Fin.sum_univ_succ] <;>
    field_simp [hs'] <;> ring

/-- The precision-score endomorphism in the coupling direction.  Since
`dR/dl = C`, this is `R(l)⁻¹ C`. -/
noncomputable def doubledTTPrecisionScore (l : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  realDoubledResponseInverse l * realifiedChirality

/-- The one-parameter Gaussian Fisher metric for a zero-mean Gaussian with
precision `R(l)`: one half of `Tr((R⁻¹ dR/dl)^2)`. -/
noncomputable def doubledTTGaussianFisher (l : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Matrix.trace
    (doubledTTPrecisionScore l * doubledTTPrecisionScore l)

/-- Closed form of the Gaussian Fisher metric. -/
theorem doubledTTGaussianFisher_eq (l : ℝ) :
    doubledTTGaussianFisher l =
      2 * (1 + l ^ 2) / screening l ^ 2 := by
  norm_num [doubledTTGaussianFisher, doubledTTPrecisionScore,
    realDoubledResponseInverse, realDoubledResponse, realifiedChirality,
    Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ]
  simp only [div_eq_mul_inv]
  rw [← inv_pow]
  ring

/-- The information curvature and the normalized determinant response are
locked by a quadratic relation.  Writing `r = 1/(1-l^2)`, the exact relation
is `F = 4*r^2 - 2*r`. -/
theorem doubledTTGaussianFisher_eq_responsePolynomial (l : ℝ) :
    doubledTTGaussianFisher l =
      4 * (1 / screening l) ^ 2 - 2 * (1 / screening l) := by
  rw [doubledTTGaussianFisher_eq]
  by_cases hs : screening l = 0
  · simp [hs]
  · field_simp [hs]
    simp only [screening]
    ring

/-- Equivalently, Fisher curvature is the sum of the squared plus- and
minus-chiral susceptibilities. -/
theorem doubledTTGaussianFisher_eq_chiral
    (l : ℝ) (hplus : 1 + l ≠ 0) (hminus : 1 - l ≠ 0) :
    doubledTTGaussianFisher l =
      1 / (1 + l) ^ 2 + 1 / (1 - l) ^ 2 := by
  have hden : 1 - l ^ 2 ≠ 0 := by
    rw [show 1 - l ^ 2 = (1 - l) * (1 + l) by ring]
    exact mul_ne_zero hminus hplus
  rw [doubledTTGaussianFisher_eq]
  simp only [screening]
  field_simp [hden, hplus, hminus]
  ring

/-- The Fisher scalar is at least its uncoupled value on the interior. -/
theorem doubledTTGaussianFisher_ge_two
    (l : ℝ) (hl0 : 0 ≤ l) (hl1 : l < 1) :
    2 ≤ doubledTTGaussianFisher l := by
  rw [doubledTTGaussianFisher_eq]
  have hs : 0 < screening l := screening_pos ⟨by linarith, hl1⟩
  have hs2 : 0 < screening l ^ 2 := sq_pos_of_pos hs
  apply (le_div_iff₀ hs2).2
  have hl_sq : l ^ 2 < 1 := by nlinarith
  have hnonneg : 0 ≤ l ^ 2 * (3 - l ^ 2) :=
    mul_nonneg (sq_nonneg l) (by nlinarith)
  simp only [screening]
  nlinarith

/-- Fisher curvature is blind to reversal of the Hodge orientation. -/
theorem doubledTTGaussianFisher_neg (l : ℝ) :
    doubledTTGaussianFisher (-l) = doubledTTGaussianFisher l := by
  rw [doubledTTGaussianFisher_eq, doubledTTGaussianFisher_eq]
  simp [screening]

/-- Replacing a coupling by its magnitude leaves the Fisher curvature
unchanged. -/
theorem doubledTTGaussianFisher_abs (l : ℝ) :
    doubledTTGaussianFisher |l| = doubledTTGaussianFisher l := by
  rw [doubledTTGaussianFisher_eq, doubledTTGaussianFisher_eq]
  rw [sq_abs]
  simp only [screening]
  rw [sq_abs]

/-- Algebraic factorization underlying reverse recovery of the coupling. -/
theorem fisher_cross_difference_factorization (l m : ℝ) :
    (1 + l ^ 2) * (1 - m ^ 2) ^ 2 -
        (1 + m ^ 2) * (1 - l ^ 2) ^ 2 =
      (l ^ 2 - m ^ 2) *
        (3 - l ^ 2 - m ^ 2 - l ^ 2 * m ^ 2) := by
  ring

/-- Running the information geometry backwards: on the physical branch
`0 <= l < 1`, the Gaussian Fisher scalar determines `l` uniquely. -/
theorem doubledTTGaussianFisher_injective
    {l m : ℝ} (hl0 : 0 ≤ l) (hl1 : l < 1)
    (hm0 : 0 ≤ m) (hm1 : m < 1)
    (hF : doubledTTGaussianFisher l = doubledTTGaussianFisher m) :
    l = m := by
  have hsl : 0 < screening l := screening_pos ⟨by linarith, hl1⟩
  have hsm : 0 < screening m := screening_pos ⟨by linarith, hm1⟩
  rw [doubledTTGaussianFisher_eq, doubledTTGaussianFisher_eq] at hF
  have hcross :
      (1 + l ^ 2) * (1 - m ^ 2) ^ 2 =
        (1 + m ^ 2) * (1 - l ^ 2) ^ 2 := by
    have hsl2 : screening l ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos hsl)
    have hsm2 : screening m ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos hsm)
    field_simp [hsl2, hsm2] at hF
    simpa [screening, mul_comm] using hF
  have hfactor :
      (l ^ 2 - m ^ 2) *
          (3 - l ^ 2 - m ^ 2 - l ^ 2 * m ^ 2) = 0 := by
    rw [← fisher_cross_difference_factorization]
    linarith
  have hpositive :
      0 < 3 - l ^ 2 - m ^ 2 - l ^ 2 * m ^ 2 := by
    have hl_sq : l ^ 2 < 1 := by nlinarith
    have hm_sq : m ^ 2 < 1 := by nlinarith
    have hxy_le : l ^ 2 * m ^ 2 ≤ l ^ 2 :=
      mul_le_of_le_one_right (sq_nonneg l) (le_of_lt hm_sq)
    have hxy_lt : l ^ 2 * m ^ 2 < 1 := lt_of_le_of_lt hxy_le hl_sq
    linarith
  have hsq : l ^ 2 = m ^ 2 := by
    rcases mul_eq_zero.mp hfactor with h | h
    · linarith
    · exfalso
      exact (ne_of_gt hpositive) h
  nlinarith

/-- Without an orientation choice, information geometry recovers exactly
the magnitude of an interior coupling. -/
theorem doubledTTGaussianFisher_recovers_abs
    {l m : ℝ} (hl : |l| < 1) (hm : |m| < 1)
    (hF : doubledTTGaussianFisher l = doubledTTGaussianFisher m) :
    |l| = |m| := by
  apply doubledTTGaussianFisher_injective (abs_nonneg l) hl (abs_nonneg m) hm
  calc
    doubledTTGaussianFisher |l| = doubledTTGaussianFisher l :=
      doubledTTGaussianFisher_abs l
    _ = doubledTTGaussianFisher m := hF
    _ = doubledTTGaussianFisher |m| :=
      (doubledTTGaussianFisher_abs m).symm

/-- Exact quartic specialization of the Fisher fingerprint. -/
theorem quarticDoubledTTGaussianFisher
    (q : ℝ) (hq : 1 < q) :
    doubledTTGaussianFisher (lambda4 q) =
      2 * q ^ 2 * (2 * q ^ 2 - 2 * q + 1) / (2 * q - 1) ^ 2 := by
  rw [doubledTTGaussianFisher_eq]
  have hq0 : q ≠ 0 := by linarith
  have hden : 2 * q - 1 ≠ 0 := by linarith
  rw [quartic_screening_identity q hq0]
  unfold lambda4
  field_simp [hq0, hden]
  ring

/-- At the quartic point, the Fisher curvature is the same quadratic
function of the actual normalized TT tensor-metric Gaussian response. -/
theorem quarticFisher_eq_tensorGaussianResponsePolynomial
    (q : ℝ) (hq : 1 < q) :
    doubledTTGaussianFisher (lambda4 q) =
      4 * ((∫ z : DoubledTTModeCoordinates,
        Real.exp
          (-doubledQuadraticEnergy (lambda4 q) ttTensorMetricBilinear
            (doubledTTPhysicalPair z) (doubledTTHodgePartnerPair z))) /
        (∫ z : DoubledTTModeCoordinates,
          Real.exp (-∑ i, (z i) ^ 2))) ^ 2 -
      2 * ((∫ z : DoubledTTModeCoordinates,
        Real.exp
          (-doubledQuadraticEnergy (lambda4 q) ttTensorMetricBilinear
            (doubledTTPhysicalPair z) (doubledTTHodgePartnerPair z))) /
        (∫ z : DoubledTTModeCoordinates,
          Real.exp (-∑ i, (z i) ^ 2))) := by
  rw [quarticTensorMetricGaussian_relativeResponse q hq]
  exact doubledTTGaussianFisher_eq_responsePolynomial (lambda4 q)

/-- The quartic Fisher fingerprint uniquely recovers the quartic Hodge
coupling among all nonnegative interior couplings. -/
theorem quartic_fisher_fingerprint_unique
    (q l : ℝ) (hq : 1 < q) (hl0 : 0 ≤ l) (hl1 : l < 1)
    (hF : doubledTTGaussianFisher l =
      doubledTTGaussianFisher (lambda4 q)) :
    l = lambda4 q := by
  have hq0 : 0 < q := by linarith
  have hlambda0 : 0 ≤ lambda4 q := by
    unfold lambda4
    have : 1 / q < 1 := (div_lt_one hq0).2 hq
    linarith
  have hlambda1 : lambda4 q < 1 := by
    unfold lambda4
    have : 0 < 1 / q := one_div_pos.mpr hq0
    linarith
  exact doubledTTGaussianFisher_injective hl0 hl1 hlambda0 hlambda1 hF

/-- The exact unnormalized mass of the four-real-mode Gaussian. -/
noncomputable def doubledTTGaussianMass (l : ℝ) : ℝ :=
  Real.pi ^ 2 / screening l

/-- The signed radial velocity of the unnormalized Gaussian mass as the
Hodge coupling varies.  Unlike the normalized Fisher scalar, this quantity
is odd in the coupling. -/
noncomputable def doubledTTGaussianMassVelocity (l : ℝ) : ℝ :=
  2 * Real.pi ^ 2 * l / screening l ^ 2

/-- The displayed mass velocity is the exact derivative of the Gaussian
mass away from the Hodge boundary. -/
theorem doubledTTGaussianMass_hasDerivAt
    (l : ℝ) (hs : screening l ≠ 0) :
    HasDerivAt doubledTTGaussianMass (doubledTTGaussianMassVelocity l) l := by
  have hscreen : HasDerivAt screening (-2 * l) l := by
    change HasDerivAt (fun x : ℝ => 1 - x ^ 2) (-2 * l) l
    exact (HasDerivAt.const_sub (1 : ℝ)
      ((hasDerivAt_id l).pow 2)).congr_deriv (by simp [id_eq])
  have hpi : HasDerivAt (fun _ : ℝ => Real.pi ^ 2) 0 l :=
    hasDerivAt_const (x := l) (c := Real.pi ^ 2)
  have hquot := hpi.div hscreen hs
  exact hquot.congr_deriv (by
    simp [doubledTTGaussianMassVelocity]
    ring)

/-- Reversing Hodge orientation reverses the radial mass velocity. -/
theorem doubledTTGaussianMassVelocity_neg (l : ℝ) :
    doubledTTGaussianMassVelocity (-l) =
      -doubledTTGaussianMassVelocity l := by
  simp [doubledTTGaussianMassVelocity, screening]
  ring

/-- Inside the nonsingular Hodge interval, the sign of the radial mass
velocity is exactly the sign of the coupling. -/
theorem doubledTTGaussianMassVelocity_pos_iff
    (l : ℝ) (hl : |l| < 1) :
    0 < doubledTTGaussianMassVelocity l ↔ 0 < l := by
  have hs : 0 < screening l := screening_pos (abs_lt.mp hl)
  have hden : 0 < screening l ^ 2 := sq_pos_of_pos hs
  unfold doubledTTGaussianMassVelocity
  rw [div_pos_iff]
  constructor
  · intro h
    rcases h with h | h
    · have hpi : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
      nlinarith
    · exact (not_lt_of_ge (le_of_lt hden) h.2).elim
  · intro hl0
    left
    exact ⟨by positivity, hden⟩

/-- In mass/shape coordinates the normalized shape direction is orthogonal
to the radial direction, but the physical coupling path also changes the
mass.  Its mixed pairing with the outward log-mass direction is therefore
exactly the signed mass velocity. -/
theorem doubledTTGaussian_fisherCone_mixed_eq_massVelocity
    {n : ℕ} (l : ℝ) (p dp : Fin n → ℝ)
    (hl : |l| < 1) (hp : ∀ i, p i ≠ 0)
    (hsum : ∑ i, p i = 1) (hdp : ∑ i, dp i = 0) :
    diagonalFisherPair
        (coneWeight (doubledTTGaussianMass l) p)
        (coneTangent (doubledTTGaussianMass l)
          (doubledTTGaussianMass l) p (fun _ => 0))
        (coneTangent (doubledTTGaussianMass l)
          (doubledTTGaussianMassVelocity l) p dp) =
      doubledTTGaussianMassVelocity l := by
  have hs : 0 < screening l := screening_pos (abs_lt.mp hl)
  have hm : doubledTTGaussianMass l ≠ 0 := by
    unfold doubledTTGaussianMass
    positivity
  rw [fisherCone_pair_decomposition
    (doubledTTGaussianMass l) (doubledTTGaussianMass l)
    (doubledTTGaussianMassVelocity l) p (fun _ => 0) dp
    hm hp hsum (by simp) hdp]
  simp [diagonalFisherPair, hm]

/-- The quartic branch points outward in the positive-measure Fisher cone. -/
theorem quarticDoubledTTGaussianMassVelocity_pos
    (q : ℝ) (hq : 1 < q) :
    0 < doubledTTGaussianMassVelocity (lambda4 q) := by
  have hq0 : 0 < q := by linarith
  have hl0 : 0 < lambda4 q := by
    unfold lambda4
    have : 1 / q < 1 := (div_lt_one hq0).2 hq
    linarith
  have hl1 : lambda4 q < 1 := by
    unfold lambda4
    have : 0 < 1 / q := one_div_pos.mpr hq0
    linarith
  exact (doubledTTGaussianMassVelocity_pos_iff
    (lambda4 q) (abs_lt.mpr ⟨by linarith, hl1⟩)).2 hl0

/-- The analytic Gaussian integral is exactly the information-cone mass. -/
theorem doubledTTMode_gaussian_integral_eq_mass
    (l d : ℝ) (hd : d ^ 2 = screening l) (hdpos : 0 < d) :
    (∫ z : DoubledTTModeCoordinates,
        Real.exp (-doubledTTModeQuadratic l z)) =
      doubledTTGaussianMass l := by
  simpa [doubledTTGaussianMass] using
    doubledTTMode_gaussian_integral l d hd hdpos

/-- The Gaussian partition mass is a radial coordinate retained by the
positive-measure Fisher cone.  Its pure radial squared line element is
`dm^2/m`; conditioning the measure would discard this coordinate. -/
theorem doubledTTGaussian_fisherCone_radial_term
    {n : ℕ} (l dm : ℝ) (p : Fin n → ℝ)
    (hl : -1 < l ∧ l < 1) (hp : ∀ i, p i ≠ 0)
    (hsum : ∑ i, p i = 1) :
    diagonalFisherPair
        (coneWeight (doubledTTGaussianMass l) p)
        (coneTangent (doubledTTGaussianMass l) dm p (fun _ => 0))
        (coneTangent (doubledTTGaussianMass l) dm p (fun _ => 0)) =
      dm ^ 2 / doubledTTGaussianMass l := by
  have hs : 0 < screening l := screening_pos hl
  have hm : doubledTTGaussianMass l ≠ 0 := by
    unfold doubledTTGaussianMass
    positivity
  have h := fisherCone_pair_decomposition
    (doubledTTGaussianMass l) dm dm p (fun _ => 0) (fun _ => 0)
    hm hp hsum (by simp) (by simp)
  simpa [diagonalFisherPair, pow_two] using h

#print axioms GravityScreening.realDoubledResponse_mul_inverse
#print axioms GravityScreening.realDoubledResponse_inverse_mul
#print axioms GravityScreening.doubledTTGaussianFisher_eq
#print axioms GravityScreening.doubledTTGaussianFisher_eq_responsePolynomial
#print axioms GravityScreening.doubledTTGaussianFisher_eq_chiral
#print axioms GravityScreening.doubledTTGaussianFisher_ge_two
#print axioms GravityScreening.doubledTTGaussianFisher_neg
#print axioms GravityScreening.doubledTTGaussianFisher_abs
#print axioms GravityScreening.doubledTTGaussianFisher_injective
#print axioms GravityScreening.doubledTTGaussianFisher_recovers_abs
#print axioms GravityScreening.quarticDoubledTTGaussianFisher
#print axioms GravityScreening.quarticFisher_eq_tensorGaussianResponsePolynomial
#print axioms GravityScreening.quartic_fisher_fingerprint_unique
#print axioms GravityScreening.doubledTTGaussianMass_hasDerivAt
#print axioms GravityScreening.doubledTTGaussianMassVelocity_neg
#print axioms GravityScreening.doubledTTGaussianMassVelocity_pos_iff
#print axioms GravityScreening.doubledTTGaussian_fisherCone_mixed_eq_massVelocity
#print axioms GravityScreening.quarticDoubledTTGaussianMassVelocity_pos
#print axioms GravityScreening.doubledTTGaussian_fisherCone_radial_term

end GravityScreening
