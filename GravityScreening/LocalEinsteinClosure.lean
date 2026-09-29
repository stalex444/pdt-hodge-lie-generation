module
public import GravityScreening.KMSOpticalBoundarySelection

@[expose] public section

/-!
# Local Jacobson-to-Einstein tensor closure

Jacobson's local-horizon argument first produces a null-contracted tensor
relation.  The remaining algebraic step is that a symmetric bilinear form
which vanishes on every Minkowski-null direction must be proportional to the
metric.  This file proves that step constructively in four dimensions and
then inserts the PDT gravitational coupling.

This is a pointwise tensor theorem in a local orthonormal frame.  It does not
formalize differential geometry, the Bianchi identity, or the proof of the
Clausius premise from quantum fields.
-/

namespace GravityScreening

/-- Minkowski metric in a local orthonormal frame, with signature `(-,+,+,+)`.
-/
noncomputable def localMinkowskiMetric : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-1, 0, 0, 0;
      0, 1, 0, 0;
      0, 0, 1, 0;
      0, 0, 0, 1]

/-- Squared Minkowski norm in the local orthonormal frame. -/
def localMinkowskiSq (v : Fin 4 → ℝ) : ℝ :=
  -(v 0) ^ 2 + (v 1) ^ 2 + (v 2) ^ 2 + (v 3) ^ 2

/-- Quadratic contraction `v^a M_ab v^b`. -/
def localQuadraticContraction
    (M : Matrix (Fin 4) (Fin 4) ℝ) (v : Fin 4 → ℝ) : ℝ :=
  dotProduct v (M.mulVec v)

theorem localMinkowskiMetric_quadratic
    (v : Fin 4 → ℝ) :
    localQuadraticContraction localMinkowskiMetric v =
      localMinkowskiSq v := by
  simp [localQuadraticContraction, localMinkowskiMetric,
    localMinkowskiSq, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

/-- Constructive four-dimensional null-cone rigidity.  Only finitely many
rational null probes are needed in the proof, although the hypothesis is
stated in its coordinate-independent physical form. -/
theorem symmetricForm_vanishes_on_nullCone_forces_metric
    (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hsym : M.transpose = M)
    (hnull : ∀ v : Fin 4 → ℝ,
      localMinkowskiSq v = 0 → localQuadraticContraction M v = 0) :
    ∃ c : ℝ, M = c • localMinkowskiMetric := by
  have hs01 := congrArg
    (fun A : Matrix (Fin 4) (Fin 4) ℝ => A 0 1) hsym
  have hs02 := congrArg
    (fun A : Matrix (Fin 4) (Fin 4) ℝ => A 0 2) hsym
  have hs03 := congrArg
    (fun A : Matrix (Fin 4) (Fin 4) ℝ => A 0 3) hsym
  have hs12 := congrArg
    (fun A : Matrix (Fin 4) (Fin 4) ℝ => A 1 2) hsym
  have hs13 := congrArg
    (fun A : Matrix (Fin 4) (Fin 4) ℝ => A 1 3) hsym
  have hs23 := congrArg
    (fun A : Matrix (Fin 4) (Fin 4) ℝ => A 2 3) hsym
  simp [Matrix.transpose_apply] at hs01 hs02 hs03 hs12 hs13 hs23

  have h01p := hnull ![(1 : ℝ), 1, 0, 0]
    (by norm_num [localMinkowskiSq, Matrix.cons_val_two,
      Matrix.cons_val_three])
  have h01m := hnull ![(1 : ℝ), -1, 0, 0]
    (by norm_num [localMinkowskiSq, Matrix.cons_val_two,
      Matrix.cons_val_three])
  have h02p := hnull ![(1 : ℝ), 0, 1, 0]
    (by norm_num [localMinkowskiSq, Matrix.cons_val_two,
      Matrix.cons_val_three])
  have h02m := hnull ![(1 : ℝ), 0, -1, 0]
    (by norm_num [localMinkowskiSq, Matrix.cons_val_two,
      Matrix.cons_val_three])
  have h03p := hnull ![(1 : ℝ), 0, 0, 1]
    (by norm_num [localMinkowskiSq, Matrix.cons_val_two,
      Matrix.cons_val_three])
  have h03m := hnull ![(1 : ℝ), 0, 0, -1]
    (by norm_num [localMinkowskiSq, Matrix.cons_val_two,
      Matrix.cons_val_three])
  have h12p := hnull ![(5 : ℝ), 3, 4, 0]
    (by norm_num [localMinkowskiSq, Matrix.cons_val_two,
      Matrix.cons_val_three])
  have h12m := hnull ![(5 : ℝ), 3, -4, 0]
    (by norm_num [localMinkowskiSq, Matrix.cons_val_two,
      Matrix.cons_val_three])
  have h13p := hnull ![(5 : ℝ), 3, 0, 4]
    (by norm_num [localMinkowskiSq, Matrix.cons_val_two,
      Matrix.cons_val_three])
  have h13m := hnull ![(5 : ℝ), 3, 0, -4]
    (by norm_num [localMinkowskiSq, Matrix.cons_val_two,
      Matrix.cons_val_three])
  have h23p := hnull ![(5 : ℝ), 0, 3, 4]
    (by norm_num [localMinkowskiSq, Matrix.cons_val_two,
      Matrix.cons_val_three])
  have h23m := hnull ![(5 : ℝ), 0, 3, -4]
    (by norm_num [localMinkowskiSq, Matrix.cons_val_two,
      Matrix.cons_val_three])
  simp [localQuadraticContraction, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] at h01p h01m h02p h02m h03p h03m h12p h12m h13p h13m h23p h23m

  have h01 : M 0 1 = 0 := by linarith
  have h02 : M 0 2 = 0 := by linarith
  have h03 : M 0 3 = 0 := by linarith
  have h11 : M 1 1 = -M 0 0 := by linarith
  have h22 : M 2 2 = -M 0 0 := by linarith
  have h33 : M 3 3 = -M 0 0 := by linarith
  have h12 : M 1 2 = 0 := by linarith
  have h13 : M 1 3 = 0 := by linarith
  have h23 : M 2 3 = 0 := by linarith
  refine ⟨-M 0 0, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [localMinkowskiMetric] <;> linarith

/-- Local metric trace of a rank-two tensor. -/
def localMinkowskiTrace (M : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  -M 0 0 + M 1 1 + M 2 2 + M 3 3

/-- The algebraic last step in Jacobson's argument.  If the Ricci-minus-source
tensor has zero contraction with every null direction, the local Einstein
equation follows with one scalar cosmological term. -/
theorem nullClausius_forces_localEinsteinShape
    (ricci stress : Matrix (Fin 4) (Fin 4) ℝ) (kappa : ℝ)
    (hricci : ricci.transpose = ricci)
    (hstress : stress.transpose = stress)
    (hnull : ∀ v : Fin 4 → ℝ,
      localMinkowskiSq v = 0 →
        localQuadraticContraction (ricci - kappa • stress) v = 0) :
    ∃ cosmological : ℝ,
      ricci - (localMinkowskiTrace ricci / 2) • localMinkowskiMetric +
          cosmological • localMinkowskiMetric =
        kappa • stress := by
  have hsym : (ricci - kappa • stress).transpose =
      ricci - kappa • stress := by
    rw [Matrix.transpose_sub, Matrix.transpose_smul, hricci, hstress]
  obtain ⟨c, hc⟩ :=
    symmetricForm_vanishes_on_nullCone_forces_metric
      (ricci - kappa • stress) hsym hnull
  refine ⟨localMinkowskiTrace ricci / 2 - c, ?_⟩
  ext i j
  have hij := congrArg
    (fun A : Matrix (Fin 4) (Fin 4) ℝ => A i j) hc
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul] at hij ⊢
  linarith [hij]

/-- PDT specialization of the local Jacobson closure.  In electron-mass
natural units the dimensionless null Clausius relation uses
`8*pi*alphaG`, with `alphaG` supplied by the complete rho Q determinant.
Restoring units requires the separate physical identification
`alphaG = G_N*m_e^2/(hbar*c)`. -/
theorem pdtNullClausius_forces_localEinsteinShape
    (ricci stress : Matrix (Fin 4) (Fin 4) ℝ)
    (rho q : ℝ)
    (hrho3 : rho ^ 3 = rho + 1) (hrho1 : 1 < rho)
    (hq4 : q ^ 4 = q + 1) (hq1 : 1 < q)
    (hricci : ricci.transpose = ricci)
    (hstress : stress.transpose = stress)
    (hnull : ∀ v : Fin 4 → ℝ,
      localMinkowskiSq v = 0 →
        localQuadraticContraction
          (ricci - (8 * Real.pi * gravitationalCoupling rho q) • stress)
          v = 0) :
    Irrational (Real.log rho / Real.log q) ∧
      (∃ cosmological : ℝ,
        ricci - (localMinkowskiTrace ricci / 2) • localMinkowskiMetric +
            cosmological • localMinkowskiMetric =
          (8 * Real.pi * gravitationalCoupling rho q) • stress) ∧
      1 / gravitationalCoupling rho q =
        (Matrix.det
            (scalarResponseMatrix gravitationalExponent (rho * q)) *
          Matrix.det (perronCompressedConstitutiveBlock q)) /
          Real.pi ^ 4 := by
  have hind := (rhoQ_modularCompletion_capstone
    rho q 0 hrho3 hrho1 hq4 hq1).1
  refine ⟨hind, ?_, ?_⟩
  · exact nullClausius_forces_localEinsteinShape
      ricci stress (8 * Real.pi * gravitationalCoupling rho q)
      hricci hstress hnull
  · have hrho0 : rho ≠ 0 := by linarith
    exact canonicalPerron_fullGravity_determinant
      rho q hrho0 hq4 hq1

#print axioms GravityScreening.localMinkowskiMetric_quadratic
#print axioms GravityScreening.symmetricForm_vanishes_on_nullCone_forces_metric
#print axioms GravityScreening.nullClausius_forces_localEinsteinShape
#print axioms GravityScreening.pdtNullClausius_forces_localEinsteinShape

end GravityScreening
