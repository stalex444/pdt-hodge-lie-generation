module
public import GravityScreening.CoreClockDuality

@[expose] public section

/-!
# From the modular core weight to the Hodge response

The dual action translates the dimensionless gravitational area charge. Its
self-defect polynomial therefore acts trivially on affine charge observables,
although it acts with the quartic screening eigenvalue on the exponential
area weight. On a single Hodge pair, requiring the other chiral stiffness to
preserve the orientation-blind mean then completes the core weight `1/q`
uniquely to the pair `1-lambda4 q`, `1+lambda4 q`.

The mathematical statements do not identify this completed Hodge response
with the physical gravitational kinetic operator.
-/

namespace GravityScreening

/-! ## Translation of the gravitational area charge -/

/-- Pullback of a scalar observable by the dual translation `x ↦ x-s`. -/
def dualTranslationPullback (s : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun x => f (x - s)

/-- Defect of the dual translation on scalar observables. -/
def dualTranslationDefect (s : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun x => f x - dualTranslationPullback s f x

/-- Complement of applying the translation defect twice. -/
def dualSelfDefectComplement (s : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun x => f x - dualTranslationDefect s (dualTranslationDefect s f) x

/-- An affine observable of the dimensionless area charge. -/
def affineChargeObservable (a b : ℝ) : ℝ → ℝ :=
  fun x => a * x + b

/-- The translation defect of an affine charge observable is a constant. -/
theorem dualTranslationDefect_affine (s a b x : ℝ) :
    dualTranslationDefect s (affineChargeObservable a b) x = a * s := by
  simp [dualTranslationDefect, dualTranslationPullback,
    affineChargeObservable]
  ring

/-- A second translation defect annihilates every affine charge observable. -/
theorem dualTranslationDefect_sq_affine (s a b x : ℝ) :
    dualTranslationDefect s
        (dualTranslationDefect s (affineChargeObservable a b)) x = 0 := by
  have hfirst :
      dualTranslationDefect s (affineChargeObservable a b) =
        fun _ => a * s := by
    funext y
    exact dualTranslationDefect_affine s a b y
  rw [hfirst]
  simp [dualTranslationDefect, dualTranslationPullback]

/-- Hence the quartic self-defect complement cannot multiplicatively screen a
linear area charge: it is the identity on every affine observable. -/
theorem dualSelfDefectComplement_affine (s a b x : ℝ) :
    dualSelfDefectComplement s (affineChargeObservable a b) x =
      affineChargeObservable a b x := by
  simp [dualSelfDefectComplement, dualTranslationDefect_sq_affine]

/-- The dimensionless horizon-cut area term in the gravitational constraint. -/
def horizonAreaCharge (asymptoticCharge modularEnergy : ℝ) : ℝ :=
  -asymptoticCharge - modularEnergy

/-- Translating the asymptotic charge by `q ↦ q-s`, while fixing the modular
energy, translates the horizon-cut area charge by `+s`. -/
theorem horizonAreaCharge_dualTranslation (q K s : ℝ) :
    horizonAreaCharge (q - s) K = horizonAreaCharge q K + s := by
  simp [horizonAreaCharge]
  ring

/-- The difference of two horizon-cut area charges is invariant under the
common dual translation. -/
theorem horizonAreaDifference_dualTranslation
    (q K₀ K₁ s : ℝ) :
    horizonAreaCharge (q - s) K₁ - horizonAreaCharge (q - s) K₀ =
      horizonAreaCharge q K₁ - horizonAreaCharge q K₀ := by
  simp [horizonAreaCharge]

/-! ## The exponential area weight is the eigenobject -/

/-- Boltzmann-type exponential of the dimensionless area charge. -/
noncomputable def areaBoltzmannWeight (x : ℝ) : ℝ := Real.exp x

/-- Under dual translation by `log q`, the exponential area weight has
eigenvalue `1/q`. -/
theorem areaBoltzmannWeight_dualTranslation_log
    (q x : ℝ) (hq : 0 < q) :
    dualTranslationPullback (Real.log q) areaBoltzmannWeight x =
      (1 / q) * areaBoltzmannWeight x := by
  unfold dualTranslationPullback areaBoltzmannWeight
  rw [show x - Real.log q = x + (-Real.log q) by ring,
    Real.exp_add, Real.exp_neg, Real.exp_log hq]
  ring

/-- The first translation defect of the exponential weight is the quartic
residue amplitude. -/
theorem areaBoltzmannWeight_dualDefect_log
    (q x : ℝ) (hq : 0 < q) :
    dualTranslationDefect (Real.log q) areaBoltzmannWeight x =
      lambda4 q * areaBoltzmannWeight x := by
  unfold dualTranslationDefect
  rw [areaBoltzmannWeight_dualTranslation_log q x hq]
  unfold lambda4
  ring

/-- The complement of the repeated defect acts on the exponential area weight
with the exact screening eigenvalue. -/
theorem areaBoltzmannWeight_selfDefect_log
    (q x : ℝ) (hq : 0 < q) :
    dualSelfDefectComplement (Real.log q) areaBoltzmannWeight x =
      screening (lambda4 q) * areaBoltzmannWeight x := by
  unfold dualSelfDefectComplement
  have hfirst :
      dualTranslationDefect (Real.log q) areaBoltzmannWeight =
        fun y => lambda4 q * areaBoltzmannWeight y := by
    funext y
    exact areaBoltzmannWeight_dualDefect_log q y hq
  rw [hfirst]
  have hscaled :
      dualTranslationDefect (Real.log q)
          (fun y => lambda4 q * areaBoltzmannWeight y) x =
        lambda4 q ^ 2 * areaBoltzmannWeight x := by
    unfold dualTranslationDefect dualTranslationPullback
    have hshift :
        areaBoltzmannWeight (x - Real.log q) =
          (1 / q) * areaBoltzmannWeight x := by
      simpa [dualTranslationPullback] using
        areaBoltzmannWeight_dualTranslation_log q x hq
    change
      lambda4 q * areaBoltzmannWeight x -
          lambda4 q * areaBoltzmannWeight (x - Real.log q) =
        lambda4 q ^ 2 * areaBoltzmannWeight x
    rw [hshift]
    unfold lambda4
    ring
  rw [hscaled]
  simp [screening]
  ring

/-! ## Unique mean-preserving Hodge completion -/

/-- The modular-core weight is the minus-chiral affine weight. -/
theorem coreWeight_eq_one_sub_lambda4 (q : ℝ) :
    1 / q = 1 - lambda4 q := by
  unfold lambda4
  ring

/-- If one chiral stiffness is the core weight `1/q` and the arithmetic mean
of the two stiffnesses is the normalized baseline one, the partner stiffness
is uniquely `1+lambda4 q`. -/
theorem meanPreserving_coreWeight_partner_unique
    (q partner : ℝ) (hq : q ≠ 0)
    (hmean : (partner + 1 / q) / 2 = 1) :
    partner = 1 + lambda4 q := by
  unfold lambda4
  field_simp [hq] at hmean ⊢
  linarith

/-- The unique mean-preserving pair has the exact screening product. -/
theorem meanPreserving_coreWeight_product
    (q partner : ℝ) (hq : q ≠ 0)
    (hmean : (partner + 1 / q) / 2 = 1) :
    partner * (1 / q) = screening (lambda4 q) := by
  rw [meanPreserving_coreWeight_partner_unique q partner hq hmean]
  rw [coreWeight_eq_one_sub_lambda4 q]
  simp [screening]
  ring

/-- The simple equilibrium-gravity formula: a core stiffness `1/q`, its
unique mean-preserving partner, and an orientation-blind inverse response give
the exact reciprocal screening factor. -/
theorem meanPreserving_coreWeight_evenCompliance
    (q partner : ℝ) (hq : 1 < q)
    (hmean : (partner + 1 / q) / 2 = 1) :
    (1 / 2 : ℝ) * (1 / partner + 1 / (1 / q)) =
      q ^ 2 / (2 * q - 1) := by
  have hq0 : q ≠ 0 := by linarith
  rw [meanPreserving_coreWeight_partner_unique q partner hq0 hmean]
  rw [coreWeight_eq_one_sub_lambda4 q]
  exact quartic_orientationEven_chiralCompliance q hq

/-- At the quartic residue, the Hodge response is exactly the diagonal
mean-preserving completion of the modular-core weight. -/
theorem chiralAreaResponse_eq_coreWeightCompletion
    (q : ℝ) (hq : q ≠ 0) :
    chiralAreaResponse (lambda4 q) =
      !![((2 - 1 / q : ℝ) : ℂ), 0; 0, ((1 / q : ℝ) : ℂ)] := by
  rw [chiralAreaResponse_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lambda4] <;> field_simp [hq] <;> ring

/-- Consequently the determinant of the uniquely completed Hodge pair is the
quartic core self-defect coefficient. -/
theorem coreWeightCompletion_det
    (q : ℝ) :
    Matrix.det (chiralAreaResponse (lambda4 q)) =
      (screening (lambda4 q) : ℂ) := by
  exact chiralAreaResponse_det (lambda4 q)

#print axioms GravityScreening.dualTranslationDefect_affine
#print axioms GravityScreening.dualTranslationDefect_sq_affine
#print axioms GravityScreening.dualSelfDefectComplement_affine
#print axioms GravityScreening.horizonAreaCharge_dualTranslation
#print axioms GravityScreening.horizonAreaDifference_dualTranslation
#print axioms GravityScreening.areaBoltzmannWeight_dualTranslation_log
#print axioms GravityScreening.areaBoltzmannWeight_dualDefect_log
#print axioms GravityScreening.areaBoltzmannWeight_selfDefect_log
#print axioms GravityScreening.coreWeight_eq_one_sub_lambda4
#print axioms GravityScreening.meanPreserving_coreWeight_partner_unique
#print axioms GravityScreening.meanPreserving_coreWeight_product
#print axioms GravityScreening.meanPreserving_coreWeight_evenCompliance
#print axioms GravityScreening.chiralAreaResponse_eq_coreWeightCompletion
#print axioms GravityScreening.coreWeightCompletion_det

end GravityScreening
