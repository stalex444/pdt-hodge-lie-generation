module
public import GravityScreening.TransverseTracelessCount

@[expose] public section

/-!
# An explicit three-dimensional plastic-number digit geometry

Bandt--Meyer's three-dimensional plastic-number Meyer-set proposition uses
four non-coplanar digit vectors whose sum is zero.  This file supplies an
explicit regular-tetrahedral choice and verifies its finite-dimensional
hypotheses.  The existence of the associated Meyer set is a cited published
theorem, not reproved here.
-/

namespace GravityScreening

abbrev PackingPoint3 := Fin 3 → ℝ

def tetraDigitA : PackingPoint3 := ![1, 1, 1]
def tetraDigitB : PackingPoint3 := ![1, -1, -1]
def tetraDigitC : PackingPoint3 := ![-1, 1, -1]
def tetraDigitD : PackingPoint3 := ![-1, -1, 1]

/-- The four tetrahedral digit directions balance exactly at the origin. -/
theorem tetraDigits_sum_zero :
    tetraDigitA + tetraDigitB + tetraDigitC + tetraDigitD = 0 := by
  funext i
  fin_cases i <;>
    norm_num [tetraDigitA, tetraDigitB, tetraDigitC, tetraDigitD]

/-- Difference matrix based at the first tetrahedral digit. -/
def tetraDifferenceMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, -2, -2;
     -2, 0, -2;
     -2, -2, 0]

/-- Its determinant is nonzero, so the four displayed digits are not
coplanar. -/
theorem tetraDifferenceMatrix_det :
    Matrix.det tetraDifferenceMatrix = -16 := by
  simp only [tetraDifferenceMatrix, Matrix.det_fin_three, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
    Matrix.cons_val_one, Matrix.cons_val]
  norm_num

theorem tetraDifferenceMatrix_nonsingular :
    Matrix.det tetraDifferenceMatrix ≠ 0 := by
  rw [tetraDifferenceMatrix_det]
  norm_num

#print axioms GravityScreening.tetraDigits_sum_zero
#print axioms GravityScreening.tetraDifferenceMatrix_det
#print axioms GravityScreening.tetraDifferenceMatrix_nonsingular

end GravityScreening
