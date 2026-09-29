module
public import GravityScreening.GaussianInformationGeometry
public import GravityScreening.ClockHodgeBridge

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Reverse classification of the doubled Hodge response

This file starts from symmetry data rather than from the displayed response
matrix.  A real four-mode operator that is self-adjoint and commutes with both
the common polarization quarter-turn and realified chirality is forced to lie
in the two-dimensional span of `I` and the chirality involution.  Mean-one
normalization fixes the identity coefficient.  Choosing the minus-chiral core
weight `1/q` then fixes the remaining coefficient to `lambda4 q`.

The last step is orientation-sensitive: choosing the opposite chiral plane
would reverse the sign.  The normalized Fisher scalar from
`GaussianInformationGeometry` is orientation-blind and recovers only the
magnitude.  The full positive-measure cone retains the sign as a mixed
radial--chiral pairing once the outward radial direction is oriented.
-/

namespace GravityScreening

/-- The simultaneous quarter-turn of the physical TT pair and its independent
Hodge partner. -/
def doubledPolarizationQuarterTurn : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0,-1,0,0; 1,0,0,0; 0,0,0,-1; 0,0,1,0]

/-- Self-adjoint operators commuting with both the polarization quarter-turn
and the realified chirality are exactly affine functions of chirality. -/
theorem doubledResponse_eq_explicit_of_symmetries
    (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hJ : M * doubledPolarizationQuarterTurn =
      doubledPolarizationQuarterTurn * M)
    (hC : M * realifiedChirality = realifiedChirality * M)
    (hself : M.transpose = M) :
    M = !![M 0 0, 0, 0, M 0 3;
            0, M 0 0, -M 0 3, 0;
            0, -M 0 3, M 0 0, 0;
            M 0 3, 0, 0, M 0 0] := by
  have hJ00 := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℝ => A 0 0) hJ
  have hJ01 := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℝ => A 0 1) hJ
  have hJ02 := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℝ => A 0 2) hJ
  have hJ03 := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℝ => A 0 3) hJ
  have hJ10 := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℝ => A 1 0) hJ
  have hJ11 := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℝ => A 1 1) hJ
  have hJ12 := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℝ => A 1 2) hJ
  have hJ13 := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℝ => A 1 3) hJ
  have hJ20 := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℝ => A 2 0) hJ
  have hJ21 := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℝ => A 2 1) hJ
  have hJ22 := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℝ => A 2 2) hJ
  have hJ23 := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℝ => A 2 3) hJ
  have hJ30 := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℝ => A 3 0) hJ
  have hJ31 := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℝ => A 3 1) hJ
  have hJ32 := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℝ => A 3 2) hJ
  have hJ33 := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℝ => A 3 3) hJ
  have hC00 := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℝ => A 0 0) hC
  have hC01 := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℝ => A 0 1) hC
  have hC02 := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℝ => A 0 2) hC
  have hC03 := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℝ => A 0 3) hC
  have hC10 := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℝ => A 1 0) hC
  have hC11 := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℝ => A 1 1) hC
  have hC12 := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℝ => A 1 2) hC
  have hC13 := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℝ => A 1 3) hC
  have hC20 := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℝ => A 2 0) hC
  have hC21 := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℝ => A 2 1) hC
  have hC22 := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℝ => A 2 2) hC
  have hC23 := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℝ => A 2 3) hC
  have hC30 := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℝ => A 3 0) hC
  have hC31 := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℝ => A 3 1) hC
  have hC32 := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℝ => A 3 2) hC
  have hC33 := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℝ => A 3 3) hC
  have hS01 := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℝ => A 0 1) hself
  have hS02 := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℝ => A 0 2) hself
  have hS03 := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℝ => A 0 3) hself
  have hS12 := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℝ => A 1 2) hself
  have hS13 := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℝ => A 1 3) hself
  have hS23 := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℝ => A 2 3) hself
  norm_num [doubledPolarizationQuarterTurn, realifiedChirality,
    Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ,
    Matrix.cons_val_two, Matrix.cons_val_three] at hJ00 hJ01 hJ02 hJ03 hJ10 hJ11 hJ12 hJ13 hJ20 hJ21 hJ22 hJ23 hJ30 hJ31 hJ32 hJ33 hC00 hC01 hC02 hC03 hC10 hC11 hC12 hC13 hC20 hC21 hC22 hC23 hC30 hC31 hC32 hC33 hS01 hS02 hS03 hS12 hS13 hS23
  apply Matrix.ext
  simp only [Fin.forall_fin_succ, Fin.forall_fin_zero]
  norm_num [Matrix.cons_val_two, Matrix.cons_val_three]
  norm_num
  repeat' apply And.intro
  all_goals linarith

/-- Coordinate-free form of the same classification: the symmetric joint
commutant is the two-dimensional span of identity and chirality. -/
theorem doubledResponse_eq_affineChirality_of_symmetries
    (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hJ : M * doubledPolarizationQuarterTurn =
      doubledPolarizationQuarterTurn * M)
    (hC : M * realifiedChirality = realifiedChirality * M)
    (hself : M.transpose = M) :
    M = (M 0 0) • (1 : Matrix (Fin 4) (Fin 4) ℝ) +
      (M 0 3) • realifiedChirality := by
  rw [doubledResponse_eq_explicit_of_symmetries M hJ hC hself]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [realifiedChirality, Matrix.one_apply,
      Matrix.cons_val_two, Matrix.cons_val_three]

/-- The displayed doubled response satisfies the two commuting symmetries and
self-adjointness used in the reverse classification. -/
theorem realDoubledResponse_symmetry_characterization (l : ℝ) :
    realDoubledResponse l * doubledPolarizationQuarterTurn =
        doubledPolarizationQuarterTurn * realDoubledResponse l ∧
      realDoubledResponse l * realifiedChirality =
        realifiedChirality * realDoubledResponse l ∧
      (realDoubledResponse l).transpose = realDoubledResponse l := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [realDoubledResponse, doubledPolarizationQuarterTurn,
        Matrix.mul_apply, Fin.sum_univ_succ]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [realDoubledResponse, realifiedChirality,
        Matrix.mul_apply, Fin.sum_univ_succ]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [realDoubledResponse, Matrix.transpose_apply]

/-- Reverse construction of the precision matrix.  Symmetry restricts the
operator to `a I+b C`; normalized mean trace fixes `a=1`; and the selected
minus-chiral core weight `1/q` fixes `b=lambda4 q`. -/
theorem realDoubledResponse_unique_of_symmetry_mean_core
    (M : Matrix (Fin 4) (Fin 4) ℝ) (q : ℝ) (hq : 1 < q)
    (hJ : M * doubledPolarizationQuarterTurn =
      doubledPolarizationQuarterTurn * M)
    (hC : M * realifiedChirality = realifiedChirality * M)
    (hself : M.transpose = M)
    (hmean : Matrix.trace M / 4 = 1)
    (hcore : M.mulVec (realifiedMinus 1 0) =
      fun i => (1 / q) * realifiedMinus 1 0 i) :
    M = realDoubledResponse (lambda4 q) := by
  have hshape := doubledResponse_eq_affineChirality_of_symmetries M hJ hC hself
  have hq0 : q ≠ 0 := by linarith
  have ha : M 0 0 = 1 := by
    rw [hshape] at hmean
    norm_num [Matrix.trace, Fin.sum_univ_succ, realifiedChirality,
      Matrix.cons_val_two, Matrix.cons_val_three] at hmean
    linarith
  have hb : M 0 3 = lambda4 q := by
    have hcore0 := congrFun hcore 0
    rw [hshape] at hcore0
    norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, realifiedMinus,
      realifiedChirality, Matrix.one_apply, Matrix.cons_val_two,
      Matrix.cons_val_three] at hcore0
    rw [ha] at hcore0
    unfold lambda4
    field_simp [hq0] at hcore0 ⊢
    linarith
  rw [hshape, ha, hb]
  apply Matrix.ext
  simp only [Fin.forall_fin_succ, Fin.forall_fin_zero]
  norm_num [realDoubledResponse, realifiedChirality, Matrix.one_apply,
    Matrix.cons_val_two, Matrix.cons_val_three]

/-- Consequently the reverse-classified matrix has the exact quartic
information-geometric fingerprint. -/
theorem symmetry_mean_core_forces_quarticFisher
    (M : Matrix (Fin 4) (Fin 4) ℝ) (q : ℝ) (hq : 1 < q)
    (hJ : M * doubledPolarizationQuarterTurn =
      doubledPolarizationQuarterTurn * M)
    (hC : M * realifiedChirality = realifiedChirality * M)
    (hself : M.transpose = M)
    (hmean : Matrix.trace M / 4 = 1)
    (hcore : M.mulVec (realifiedMinus 1 0) =
      fun i => (1 / q) * realifiedMinus 1 0 i) :
    M = realDoubledResponse (lambda4 q) ∧
      doubledTTGaussianFisher (lambda4 q) =
        2 * q ^ 2 * (2 * q ^ 2 - 2 * q + 1) / (2 * q - 1) ^ 2 := by
  constructor
  · exact realDoubledResponse_unique_of_symmetry_mean_core
      M q hq hJ hC hself hmean hcore
  · exact quarticDoubledTTGaussianFisher q hq

#print axioms GravityScreening.doubledResponse_eq_explicit_of_symmetries
#print axioms GravityScreening.doubledResponse_eq_affineChirality_of_symmetries
#print axioms GravityScreening.realDoubledResponse_symmetry_characterization
#print axioms GravityScreening.realDoubledResponse_unique_of_symmetry_mean_core
#print axioms GravityScreening.symmetry_mean_core_forces_quarticFisher

end GravityScreening
