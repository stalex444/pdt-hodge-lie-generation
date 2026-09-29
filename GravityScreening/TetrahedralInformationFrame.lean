module
public import GravityScreening.ThreeDPackingWitness

@[expose] public section

/-!
# The tetrahedral digits as an isotropic information frame

The four normalized vertices of a regular tetrahedron are the Bloch vectors
of the qubit tetrahedral SIC measurement.  This file proves the real
finite-frame identity carried by the same four vectors used in the packing
construction.  The quantum-measurement interpretation is a published input;
the checked theorem is the underlying three-dimensional linear algebra.
-/

namespace GravityScreening

def tetraDigitFamily : Fin 4 → PackingPoint3 :=
  ![tetraDigitA, tetraDigitB, tetraDigitC, tetraDigitD]

def packingDot3 (x y : PackingPoint3) : ℝ := ∑ i, x i * y i

/-- The unnormalized tetrahedral directions have squared length three. -/
theorem tetraDigitFamily_normSq (k : Fin 4) :
    packingDot3 (tetraDigitFamily k) (tetraDigitFamily k) = 3 := by
  fin_cases k <;>
    norm_num [packingDot3, tetraDigitFamily, tetraDigitA, tetraDigitB,
      tetraDigitC, tetraDigitD, Fin.sum_univ_succ, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one,
      Matrix.cons_val]

/-- Distinct tetrahedral directions have constant inner product `-1`. -/
theorem tetraDigitFamily_pairing (k l : Fin 4) (hkl : k ≠ l) :
    packingDot3 (tetraDigitFamily k) (tetraDigitFamily l) = -1 := by
  fin_cases k <;> fin_cases l <;>
    simp_all [packingDot3, tetraDigitFamily, tetraDigitA, tetraDigitB,
      tetraDigitC, tetraDigitD, Fin.sum_univ_three]

/-- The four unnormalized tetrahedral directions form a tight frame with
frame bound four in three-dimensional coordinates. -/
theorem tetraFrame_energy (x : PackingPoint3) :
    ∑ k, (packingDot3 (tetraDigitFamily k) x) ^ 2 =
      4 * packingDot3 x x := by
  simp [packingDot3, tetraDigitFamily, tetraDigitA, tetraDigitB,
    tetraDigitC, tetraDigitD, Fin.sum_univ_four, Fin.sum_univ_three]
  ring

/-- After unit normalization, the frame bound is exactly `4/3`: four
balanced outcomes encode three real coordinates isotropically. -/
theorem tetraNormalizedFrame_energy (x : PackingPoint3) :
    (1 / 3 : ℝ) * ∑ k, (packingDot3 (tetraDigitFamily k) x) ^ 2 =
      (4 / 3 : ℝ) * packingDot3 x x := by
  rw [tetraFrame_energy]
  ring

/-- Four affine outcome weights associated with the tetrahedral frame.  In
Bloch coordinates these are the tetrahedral SIC probabilities after the
corresponding normalization of the state vector. -/
noncomputable def tetraOutcomeWeight (x : PackingPoint3) (k : Fin 4) : ℝ :=
  (1 + packingDot3 (tetraDigitFamily k) x) / 4

/-- Reconstruct the three real coordinates carried by four normalized
outcome weights. -/
def tetraRecord (weight : Fin 4 → ℝ) : PackingPoint3 :=
  fun j => ∑ k, weight k * tetraDigitFamily k j

/-- The balanced frame makes the four affine outcome weights sum to one. -/
theorem tetraOutcomeWeight_sum (x : PackingPoint3) :
    ∑ k, tetraOutcomeWeight x k = 1 := by
  simp [tetraOutcomeWeight, packingDot3, tetraDigitFamily, tetraDigitA,
    tetraDigitB, tetraDigitC, tetraDigitD, Fin.sum_univ_four,
    Fin.sum_univ_three]
  ring

/-- The four outcome weights reconstruct all three coordinates.  Thus the
tetrahedral frame is informationally complete at the level of real Bloch
coordinates. -/
theorem tetraOutcomeWeight_reconstruct (x : PackingPoint3) (j : Fin 3) :
    ∑ k, tetraOutcomeWeight x k * tetraDigitFamily k j = x j := by
  fin_cases j <;>
    simp [tetraOutcomeWeight, packingDot3, tetraDigitFamily, tetraDigitA,
      tetraDigitB, tetraDigitC, tetraDigitD, Fin.sum_univ_succ, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one,
      Matrix.cons_val] <;>
    ring

/-- Conversely, every four-weight vector of total mass one is recovered from
its three-coordinate tetrahedral record. -/
theorem tetraRecord_outcomeWeight
    (weight : Fin 4 → ℝ) (hsum : ∑ k, weight k = 1) (j : Fin 4) :
    tetraOutcomeWeight (tetraRecord weight) j = weight j := by
  simp only [Fin.sum_univ_four] at hsum
  fin_cases j <;>
    simp [tetraOutcomeWeight, tetraRecord, packingDot3, tetraDigitFamily,
      tetraDigitA, tetraDigitB, tetraDigitC, tetraDigitD,
      Fin.sum_univ_succ, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one,
      Matrix.cons_val] <;>
    linarith

#print axioms GravityScreening.tetraDigitFamily_normSq
#print axioms GravityScreening.tetraDigitFamily_pairing
#print axioms GravityScreening.tetraFrame_energy
#print axioms GravityScreening.tetraNormalizedFrame_energy
#print axioms GravityScreening.tetraOutcomeWeight_sum
#print axioms GravityScreening.tetraOutcomeWeight_reconstruct
#print axioms GravityScreening.tetraRecord_outcomeWeight

end GravityScreening
