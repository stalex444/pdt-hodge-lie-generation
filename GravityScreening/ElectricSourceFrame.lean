module
public import GravityScreening.SourcedConstraint

@[expose] public section

/-!
# Source-preserving triangular frame for the quartic squeeze

The determinant-one constitutive shape admits a lower-triangular factor whose
inverse preserves the electric source ray.  This resolves the apparent
electric-to-magnetic source mixing: the internal response acquires a partner,
but the transformed external source still has exactly zero magnetic component.
-/

namespace GravityScreening

/-- A lower-triangular determinant-one frame.  Under `r^2=d` and
`d^2=1-l^2`, its Gram matrix is the normalized constitutive block. -/
noncomputable def electricFrameTransform
    (l r : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![r, 0; -l / r, 1 / r]

/-- The displayed inverse of the electric source frame. -/
noncomputable def electricFrameInverse
    (l r : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 / r, 0; l / r, r]

/-- A source with electric component `source` and no magnetic component. -/
def electricSourceVector (source : ℝ) : Fin 2 → ℝ :=
  ![source, 0]

/-- The electric frame has determinant one and is therefore symplectic in two
dimensions. -/
theorem electricFrameTransform_det
    (l r : ℝ) (hr : r ≠ 0) :
    Matrix.det (electricFrameTransform l r) = 1 := by
  simp [electricFrameTransform, Matrix.det_fin_two]
  field_simp [hr]

/-- Direct symplecticity receipt for the source-preserving frame. -/
theorem electricFrameTransform_symplectic
    (l r : ℝ) (hr : r ≠ 0) :
    (electricFrameTransform l r).transpose * symplecticBlock *
        electricFrameTransform l r = symplecticBlock := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [electricFrameTransform, symplecticBlock,
      Matrix.transpose_apply, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    field_simp [hr] <;>
    ring

/-- The lower-triangular frame and the displayed inverse multiply to the
identity in the source-to-field order. -/
theorem electricFrameTransform_mul_inverse
    (l r : ℝ) (hr : r ≠ 0) :
    electricFrameTransform l r * electricFrameInverse l r = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [electricFrameTransform, electricFrameInverse,
      Matrix.mul_apply, Fin.sum_univ_succ] <;>
    field_simp [hr] <;>
    ring

/-- The inverse also multiplies the frame to the identity in the opposite
order. -/
theorem electricFrameInverse_mul_transform
    (l r : ℝ) (hr : r ≠ 0) :
    electricFrameInverse l r * electricFrameTransform l r = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [electricFrameTransform, electricFrameInverse,
      Matrix.mul_apply, Fin.sum_univ_succ] <;>
    field_simp [hr] <;>
    ring

/-- If `r^2=d` and `d^2=1-l^2`, the frame Gram matrix is exactly the
determinant-one constitutive shape. -/
theorem electricFrameTransform_gram
    (l d r : ℝ)
    (hr : r ≠ 0) (hrd : r ^ 2 = d)
    (hd : d ^ 2 = screening l) (hd0 : d ≠ 0) :
    (electricFrameTransform l r).transpose * electricFrameTransform l r =
      unimodularConstitutive l d := by
  subst d
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [electricFrameTransform, unimodularConstitutive,
      constitutiveBlock, Matrix.transpose_apply, Matrix.mul_apply,
      Fin.sum_univ_succ] <;>
    unfold screening at hd <;>
    field_simp [hr] <;>
    nlinarith [hd]

/-- Among positive determinant-one Gram factors, preserving the electric
source ray fixes the lower-triangular frame uniquely.  Here `b=0` is exactly
the condition that the inverse-transpose does not give an electric covector a
magnetic component. -/
theorem positive_sourcePreserving_gramFactor_unique
    (l d r a b c e : ℝ)
    (hr : 0 < r) (hrd : r ^ 2 = d) (hd0 : d ≠ 0)
    (he : 0 < e)
    (hsource : b = 0)
    (hdet : a * e - b * c = 1)
    (hcross : a * b + c * e = -l / d)
    (hmagdiag : b ^ 2 + e ^ 2 = 1 / d) :
    a = r ∧ b = 0 ∧ c = -l / r ∧ e = 1 / r := by
  subst b
  simp only [zero_mul, sub_zero] at hdet
  simp only [mul_zero, zero_add] at hcross
  norm_num at hmagdiag
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hedmul : e ^ 2 * d = 1 := by
    have hmagdiag' : e ^ 2 = 1 / d := by
      simpa [div_eq_mul_inv] using hmagdiag
    exact (eq_div_iff hd0).1 hmagdiag'
  have hersq : (e * r) ^ 2 = 1 := by
    rw [← hrd] at hedmul
    nlinarith [hedmul]
  have herpos : 0 < e * r := mul_pos he hr
  have her : e * r = 1 := by
    nlinarith [sq_nonneg (e * r - 1)]
  have heq : e = 1 / r := (eq_div_iff hr0).2 her
  have hae : a = r := by
    rw [heq] at hdet
    field_simp [hr0] at hdet
    exact hdet
  have hce : c = -l / r := by
    rw [heq, ← hrd] at hcross
    field_simp [hr0] at hcross ⊢
    nlinarith
  exact ⟨hae, rfl, hce, heq⟩

/-- Pulling an ordinary electric source through the inverse frame changes
only its magnitude.  No magnetic source component is generated. -/
theorem electricFrame_preserves_source_ray
    (l r source : ℝ) :
    (electricFrameInverse l r).transpose.mulVec
        (electricSourceVector source) =
      electricSourceVector (source / r) := by
  funext i
  fin_cases i <;>
    simp [electricFrameInverse, electricSourceVector, Matrix.transpose_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, div_eq_mul_inv,
      mul_comm]

/-- In the canonically normalized frame, a diagonal stiffness `d` responds to
the transformed electric source `source/r` with the displayed pure-electric
coordinate. -/
noncomputable def canonicalElectricResponse
    (d r source : ℝ) : Fin 2 → ℝ :=
  ![source / (r * d), 0]

/-- Mapping the canonical response back to the physical electric frame gives
the full inverse determinant response.  The second coordinate is a
constitutive partner, while the external source remained purely electric. -/
theorem electricFrame_full_source_response
    (l d r source : ℝ)
    (hr : r ≠ 0) (hrd : r ^ 2 = d)
    (hd : d ^ 2 = screening l) :
    (electricFrameInverse l r).mulVec
        (canonicalElectricResponse d r source) =
      ![source / screening l, l * (source / screening l)] := by
  funext i
  fin_cases i <;>
    simp [electricFrameInverse, canonicalElectricResponse,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
    rw [← hd, ← hrd] <;>
    field_simp [hr]

/-- The back-transformed response obeys the original mixed constraint block
with an electric source and exactly zero magnetic source equation. -/
theorem electricFrame_constraint_closure
    (l d r source : ℝ)
    (hr : r ≠ 0) (hrd : r ^ 2 = d)
    (hd : d ^ 2 = screening l) (hd0 : d ≠ 0) :
    let response := (electricFrameInverse l r).mulVec
      (canonicalElectricResponse d r source)
    electricConstraintResponse l (response 0) (response 1) = source ∧
      magneticConstraintResponse l (response 0) (response 1) = 0 := by
  dsimp
  rw [electricFrame_full_source_response l d r source hr hrd hd]
  have hs0 : screening l ≠ 0 := by
    intro hs
    have hdsq : d ^ 2 = 0 := hd.trans hs
    exact hd0 (sq_eq_zero_iff.mp hdsq)
  exact (electricSource_constraint_solution_unique l
    (source / screening l) (l * (source / screening l)) source hs0).2
    ⟨rfl, rfl⟩

/-- Quartic specialization of the source-preserving closure. -/
theorem quartic_electricFrame_constraint_closure
    (q d r source : ℝ)
    (hq : 1 < q) (hr : r ≠ 0)
    (hrd : r ^ 2 = d)
    (hd : d ^ 2 = screening (lambda4 q)) (hd0 : d ≠ 0) :
    let response := (electricFrameInverse (lambda4 q) r).mulVec
      (canonicalElectricResponse d r source)
    electricConstraintResponse (lambda4 q) (response 0) (response 1) = source ∧
      magneticConstraintResponse (lambda4 q) (response 0) (response 1) = 0 ∧
      response 0 = source / ((2 * q - 1) / q ^ 2) := by
  have hq0 : q ≠ 0 := by linarith
  dsimp
  have hresponse := electricFrame_full_source_response
    (lambda4 q) d r source hr hrd hd
  rw [hresponse]
  have hs0 : screening (lambda4 q) ≠ 0 := by
    intro hs
    have : d ^ 2 = 0 := hd.trans hs
    exact hd0 (sq_eq_zero_iff.mp this)
  constructor
  · exact (electricSource_constraint_solution_unique (lambda4 q)
      (source / screening (lambda4 q))
      (lambda4 q * (source / screening (lambda4 q))) source hs0).2
      ⟨rfl, rfl⟩ |>.1
  · constructor
    · exact (electricSource_constraint_solution_unique (lambda4 q)
        (source / screening (lambda4 q))
        (lambda4 q * (source / screening (lambda4 q))) source hs0).2
        ⟨rfl, rfl⟩ |>.2
    · rw [quartic_screening_identity q hq0]
      rfl

#print axioms GravityScreening.electricFrameTransform_det
#print axioms GravityScreening.electricFrameTransform_symplectic
#print axioms GravityScreening.electricFrameTransform_mul_inverse
#print axioms GravityScreening.electricFrameInverse_mul_transform
#print axioms GravityScreening.electricFrameTransform_gram
#print axioms GravityScreening.positive_sourcePreserving_gramFactor_unique
#print axioms GravityScreening.electricFrame_preserves_source_ray
#print axioms GravityScreening.electricFrame_full_source_response
#print axioms GravityScreening.electricFrame_constraint_closure
#print axioms GravityScreening.quartic_electricFrame_constraint_closure

end GravityScreening
