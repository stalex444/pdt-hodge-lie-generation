module
public import GravityScreening.GeometricResponseRigidity

@[expose] public section

/-!
# Calibration on the actual local Hodge mode

The local Hodge matrix is a nonzero element of `sl(15,ℂ)`. Its cubic identity
`H * H * H = -H` makes it a distinguished calibration witness: the two-sided
divide/flip factors satisfy `D * H * E = (rho*q) • H`, even when their
two-sided action on other matrices does not preserve the trace-free space.

The final theorem assumes that the same response `R` appearing in generator
covariance agrees with this two-sided action on this one Hodge mode. That
operator identification is explicit; it is not inferred from generation or
from the numerical values of the supplied scalars.

The complex theorem concerns complex dimension 224. The final real theorem
uses complexification only to evaluate one Hodge mode; its response and
determinant remain over the real 224-dimensional algebra.
-/

namespace GravityScreening.HodgeModeCalibration

noncomputable section

open HodgeResponseCovariance

abbrev CMatrix := Matrix (Fin 15) (Fin 15) ℂ

/-- The actual geometric Hodge matrix, obtained by scalar extension from its
integral metric-and-orientation formula. -/
def hodgeMatrix : CMatrix := (hodgeGenerator ℂ : CMatrix)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The local projection is the identity on the range of the geometric Hodge
operation. This is a finite identity on the specified integral matrices. -/
theorem integral_projector_hodge :
    ResponseClosureGeometry.localProjector * ResponseClosureGeometry.hodgeComplement =
      ResponseClosureGeometry.hodgeComplement := by
  decide +kernel

/-- The cubic identity follows from the actual Hodge square and projector. -/
theorem integral_hodge_cubic :
    ResponseClosureGeometry.hodgeComplement * ResponseClosureGeometry.hodgeComplement *
      ResponseClosureGeometry.hodgeComplement = -ResponseClosureGeometry.hodgeComplement := by
  rw [ResponseClosureGeometry.hodge_square, neg_mul, integral_projector_hodge]

/-- The coefficient mapping the 01 bivector to the 23 bivector is one. -/
theorem integral_hodge_entry : ResponseClosureGeometry.hodgeComplement 9 0 = 1 := by
  decide +kernel

theorem hodgeMatrix_entry : hodgeMatrix 9 0 = 1 := by
  change (ResponseClosureGeometry.hodgeComplement 9 0 : ℂ) = 1
  rw [integral_hodge_entry]
  norm_num

theorem hodgeMatrix_trace_zero : hodgeMatrix.trace = 0 :=
  (hodgeGenerator ℂ).property

theorem hodgeMatrix_ne_zero : hodgeMatrix ≠ 0 := by
  intro h
  have hentry := congrArg (fun M : CMatrix => M 9 0) h
  simp only [hodgeMatrix_entry, Matrix.zero_apply, one_ne_zero] at hentry

/-- The Hodge calibration witness is nonzero in the actual trace-free
response space. Trace-freeness is carried by its subtype. -/
theorem hodgeMode_ne_zero : hodgeGenerator ℂ ≠ 0 := by
  intro h
  apply hodgeMatrix_ne_zero
  exact congrArg (fun X : ResponseAlgebra ℂ => (X : CMatrix)) h

theorem hodgeMatrix_cubic : hodgeMatrix * hodgeMatrix * hodgeMatrix = -hodgeMatrix := by
  change HodgeLieGeneration.castMatrix ℂ ResponseClosureGeometry.hodgeComplement *
      HodgeLieGeneration.castMatrix ℂ ResponseClosureGeometry.hodgeComplement *
      HodgeLieGeneration.castMatrix ℂ ResponseClosureGeometry.hodgeComplement =
    -HodgeLieGeneration.castMatrix ℂ ResponseClosureGeometry.hodgeComplement
  rw [← map_mul, ← map_mul, integral_hodge_cubic, map_neg]

/-- Complex chirality on the local six-dimensional support, with the same
zero extension as the geometric Hodge operator. -/
def chirality : CMatrix := (-Complex.I) • hodgeMatrix

def divide (rho q : ℂ) : CMatrix :=
  ((rho + q) / 2) • (1 : CMatrix) + ((rho - q) / 2) • chirality

def flip (rho q : ℂ) : CMatrix :=
  ((rho + q) / 2) • (1 : CMatrix) - ((rho - q) / 2) • chirality

/-- The actual Hodge mode has divide/flip weight `rho*q`. This identity
does not claim that `X ↦ D*X*E` is a response on the entire trace-free space. -/
theorem divide_hodge_flip (rho q : ℂ) :
    divide rho q * hodgeMatrix * flip rho q = (rho * q) • hodgeMatrix := by
  let a : ℂ := (rho + q) / 2
  let b : ℂ := ((rho - q) / 2) * (-Complex.I)
  have hab : a ^ 2 + b ^ 2 = rho * q := by
    dsimp [a, b]
    rw [mul_pow, neg_sq, Complex.I_sq]
    ring
  simp only [divide, flip, chirality, smul_smul]
  change (a • (1 : CMatrix) + b • hodgeMatrix) * hodgeMatrix *
      (a • (1 : CMatrix) - b • hodgeMatrix) = _
  simp only [add_mul, mul_sub, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul, hodgeMatrix_cubic,
    smul_neg]
  calc
    _ = (a ^ 2 + b ^ 2) • hodgeMatrix := by module
    _ = (rho * q) • hodgeMatrix := by rw [hab]

/-- Explicit agreement on the Hodge mode converts the two-sided formula to
the one-mode calibration of the same trace-free response. -/
theorem calibration_of_same_hodge_response
    (R : ResponseAlgebra ℂ →ₗ[ℂ] ResponseAlgebra ℂ) (rho q : ℂ)
    (hmode : (R (hodgeGenerator ℂ) : CMatrix) =
      divide rho q * hodgeMatrix * flip rho q) :
    R (hodgeGenerator ℂ) = (rho * q) • hodgeGenerator ℂ := by
  apply Subtype.ext
  change (R (hodgeGenerator ℂ) : CMatrix) = (rho * q) • hodgeMatrix
  rw [hmode, divide_hodge_flip]

/-- Generator covariance and agreement of the same response with the
divide/flip action on the nonzero Hodge mode determine its scalar and
determinant on the whole 224-dimensional algebra. -/
theorem geometric_hodge_calibrated_determinant
    (R : ResponseAlgebra ℂ →ₗ[ℂ] ResponseAlgebra ℂ)
    (ha : ∀ p x, R ⁅adjointGenerator ℂ p, x⁆ = ⁅adjointGenerator ℂ p, R x⁆)
    (hh : ∀ x, R ⁅hodgeGenerator ℂ, x⁆ = ⁅hodgeGenerator ℂ, R x⁆)
    (rho q : ℂ)
    (hmode : (R (hodgeGenerator ℂ) : CMatrix) =
      divide rho q * hodgeMatrix * flip rho q) :
    R = (rho * q) • LinearMap.id ∧ LinearMap.det R = (rho * q) ^ 224 := by
  exact GeometricResponseRigidity.geometric_response_calibrated_determinant
    ℂ (by norm_num) R ha hh rho q (hodgeGenerator ℂ) hodgeMode_ne_zero
    (calibration_of_same_hodge_response R rho q hmode)

/-! ## Real response, with a complexified one-mode identification -/

abbrev RMatrix := Matrix (Fin 15) (Fin 15) ℝ

def realHodgeMatrix : RMatrix := (hodgeGenerator ℝ : RMatrix)

/-- Entrywise scalar extension of a real matrix. No extension of the whole
response operator is assumed or needed. -/
def complexifyMatrix (M : RMatrix) : CMatrix := fun i j => (M i j : ℂ)

theorem complexifyMatrix_injective : Function.Injective complexifyMatrix := by
  intro M N h
  ext i j
  exact Complex.ofReal_injective (congrArg (fun A : CMatrix => A i j) h)

theorem complexifyMatrix_smul (r : ℝ) (M : RMatrix) :
    complexifyMatrix (r • M) = (r : ℂ) • complexifyMatrix M := by
  ext i j
  exact Complex.ofReal_mul r (M i j)

/-- The real and complex Hodge matrices are scalar extensions of the same
integral geometric formula. -/
theorem complexify_realHodgeMatrix : complexifyMatrix realHodgeMatrix = hodgeMatrix := by
  ext i j
  change (((ResponseClosureGeometry.hodgeComplement i j : ℝ) : ℂ)) =
    (ResponseClosureGeometry.hodgeComplement i j : ℂ)
  exact Complex.ofReal_intCast _

theorem real_hodgeMode_ne_zero : hodgeGenerator ℝ ≠ 0 := by
  intro h
  have hm : realHodgeMatrix = 0 :=
    congrArg (fun X : ResponseAlgebra ℝ => (X : RMatrix)) h
  apply hodgeMatrix_ne_zero
  rw [← complexify_realHodgeMatrix, hm]
  ext i j
  simp [complexifyMatrix]

/-- Agreement after entrywise complexification calibrates the same real
response on its real Hodge mode. -/
theorem real_calibration_of_same_hodge_response
    (R : ResponseAlgebra ℝ →ₗ[ℝ] ResponseAlgebra ℝ) (rho q : ℝ)
    (hmode : complexifyMatrix (R (hodgeGenerator ℝ) : RMatrix) =
      divide (rho : ℂ) (q : ℂ) * hodgeMatrix * flip (rho : ℂ) (q : ℂ)) :
    R (hodgeGenerator ℝ) = (rho * q) • hodgeGenerator ℝ := by
  apply Subtype.ext
  apply complexifyMatrix_injective
  change complexifyMatrix (R (hodgeGenerator ℝ) : RMatrix) =
    complexifyMatrix ((rho * q) • realHodgeMatrix)
  rw [hmode, divide_hodge_flip, complexifyMatrix_smul, complexify_realHodgeMatrix,
    Complex.ofReal_mul]

/-- The response and determinant here are over `ℝ`, on real dimension 224.
The explicit complexified Hodge-mode identification and the original
sixteen real covariance conditions determine the entire real response. -/
theorem real_geometric_hodge_calibrated_determinant
    (R : ResponseAlgebra ℝ →ₗ[ℝ] ResponseAlgebra ℝ)
    (ha : ∀ p x, R ⁅adjointGenerator ℝ p, x⁆ = ⁅adjointGenerator ℝ p, R x⁆)
    (hh : ∀ x, R ⁅hodgeGenerator ℝ, x⁆ = ⁅hodgeGenerator ℝ, R x⁆)
    (rho q : ℝ)
    (hmode : complexifyMatrix (R (hodgeGenerator ℝ) : RMatrix) =
      divide (rho : ℂ) (q : ℂ) * hodgeMatrix * flip (rho : ℂ) (q : ℂ)) :
    R = (rho * q) • LinearMap.id ∧ LinearMap.det R = (rho * q) ^ 224 := by
  exact GeometricResponseRigidity.geometric_response_calibrated_determinant
    ℝ (by norm_num) R ha hh rho q (hodgeGenerator ℝ) real_hodgeMode_ne_zero
    (real_calibration_of_same_hodge_response R rho q hmode)

#print axioms integral_projector_hodge
#print axioms hodgeMode_ne_zero
#print axioms hodgeMatrix_cubic
#print axioms divide_hodge_flip
#print axioms geometric_hodge_calibrated_determinant
#print axioms complexify_realHodgeMatrix
#print axioms real_calibration_of_same_hodge_response
#print axioms real_geometric_hodge_calibrated_determinant

end

end GravityScreening.HodgeModeCalibration
