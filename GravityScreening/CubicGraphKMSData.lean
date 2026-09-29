module
public import GravityScreening.QuarticGraphKMSData

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Perron--Frobenius data for the cubic graph KMS scale

The cubic substitution matrix is a primitive zero-one matrix with Perron
value `rho`, where `rho^3=rho+1`.  Its coprime return loops fix the fundamental
canonical gauge frequency at `log rho` and the associated discrete modular
ratio at `1/rho`.
-/

namespace GravityScreening

/-- Incidence matrix of the cubic Selmer substitution. -/
def cubicCompanion : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![0, 0, 1],
    ![1, 0, 1],
    ![0, 1, 0]]

/-- Positive Perron eigenvector in the positive-root regime. -/
noncomputable def cubicPerronVector (rho : ℝ) : Fin 3 → ℝ :=
  ![1, rho ^ 2, rho]

theorem cubicCompanion_nonnegative (i j : Fin 3) :
    0 <= cubicCompanion i j := by
  fin_cases i <;> fin_cases j <;> norm_num [cubicCompanion]

theorem cubicCompanion_zero_or_one (i j : Fin 3) :
    cubicCompanion i j = 0 ∨ cubicCompanion i j = 1 := by
  fin_cases i <;> fin_cases j <;> norm_num [cubicCompanion]

theorem cubicCompanion_not_permutation_witness :
    cubicCompanion 1 0 = 1 ∧ cubicCompanion 1 2 = 1 ∧
      (0 : Fin 3) ≠ 2 := by
  refine ⟨by norm_num [cubicCompanion], ?_, by decide⟩
  change (1 : ℝ) = 1
  rfl

/-- The fifth power is strictly positive entrywise. -/
theorem cubicCompanion_pow_five_positive (i j : Fin 3) :
    0 < (cubicCompanion ^ 5) i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [cubicCompanion, pow_succ, Matrix.mul_apply,
      Fin.sum_univ_succ]

theorem cubicCompanion_isPrimitive : Matrix.IsPrimitive cubicCompanion := by
  refine ⟨cubicCompanion_nonnegative, 5, by norm_num, ?_⟩
  exact cubicCompanion_pow_five_positive

theorem cubicCompanion_isIrreducible : Matrix.IsIrreducible cubicCompanion :=
  cubicCompanion_isPrimitive.isIrreducible

theorem cubicCompanion_cycle_three :
    0 < (cubicCompanion ^ 3) (0 : Fin 3) 0 := by
  norm_num [cubicCompanion, pow_succ, Matrix.mul_apply,
    Fin.sum_univ_succ]

theorem cubicCompanion_cycle_five :
    0 < (cubicCompanion ^ 5) (0 : Fin 3) 0 := by
  exact cubicCompanion_pow_five_positive 0 0

theorem cubicCompanion_cycleLengths_coprime : Nat.Coprime 3 5 := by
  norm_num

/-- The length-three and length-five loop frequencies generate `log rho`. -/
theorem cubicLoopFrequencies_generate_logRho (rho : ℝ) :
    2 * (3 * Real.log rho) - 5 * Real.log rho = Real.log rho := by
  ring

theorem cubicPerronVector_positive
    (rho : ℝ) (hrho : 0 < rho) (i : Fin 3) :
    0 < cubicPerronVector rho i := by
  fin_cases i <;> simp [cubicPerronVector, hrho]

theorem cubicCompanion_perron
    (rho : ℝ) (hrho : rho ^ 3 = rho + 1) :
    cubicCompanion.mulVec (cubicPerronVector rho) =
      fun i => rho * cubicPerronVector rho i := by
  funext i
  fin_cases i <;>
    simp [cubicCompanion, cubicPerronVector, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ]
  all_goals nlinarith [hrho]

noncomputable def cubicConnesParameter (rho : ℝ) : ℝ :=
  Real.exp (-Real.log rho)

theorem cubicConnesParameter_eq_inv (rho : ℝ) (hrho : 0 < rho) :
    cubicConnesParameter rho = 1 / rho := by
  exact quarticGaugeBoltzmannFactor rho hrho

/-- Exact finite graph data needed for the cubic graph-KMS theorem. -/
theorem cubicGraphKMS_finiteData
    (rho : ℝ) (hrho3 : rho ^ 3 = rho + 1) (hrho1 : 1 < rho) :
    Matrix.IsPrimitive cubicCompanion ∧
      (∀ i, 0 < cubicPerronVector rho i) ∧
      cubicCompanion.mulVec (cubicPerronVector rho) =
        (fun i => rho * cubicPerronVector rho i) ∧
      Real.exp (-Real.log rho) = 1 / rho := by
  have hrho : 0 < rho := lt_trans zero_lt_one hrho1
  exact ⟨cubicCompanion_isPrimitive,
    cubicPerronVector_positive rho hrho,
    cubicCompanion_perron rho hrho3,
    quarticGaugeBoltzmannFactor rho hrho⟩

#print axioms GravityScreening.cubicCompanion_isPrimitive
#print axioms GravityScreening.cubicCompanion_cycle_three
#print axioms GravityScreening.cubicCompanion_cycle_five
#print axioms GravityScreening.cubicCompanion_perron
#print axioms GravityScreening.cubicGraphKMS_finiteData

end GravityScreening
