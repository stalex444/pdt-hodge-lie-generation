module
public import GravityScreening.LQGHorizonThermodynamics

@[expose] public section

/-!
# The quartic Perron carrier is dynamical, not a static area observable

The full quartic inverse-step residual is directed and non-self-adjoint.  A
faithful representation preserving the real adjoint therefore cannot identify
it with a self-adjoint horizon observable.  Its left/right Perron compression,
however, is the scalar `lambda4`, which enters the symmetric two-channel
constitutive block with determinant `screening lambda4`.

This file proves that division of roles.  Calling a particular representation
an LQG horizon representation remains a physical identification.
-/

namespace GravityScreening

/-- The quartic residual is not self-adjoint in the standard real matrix
adjoint. -/
theorem quarticResidual_not_selfAdjoint :
    quarticResidual.transpose ≠ quarticResidual := by
  intro h
  have hij := congrArg (fun M => M 0 1) h
  norm_num [quarticResidual, Matrix.transpose_apply] at hij

/-- The full directed residual cannot equal any self-adjoint four-state
observable. -/
theorem quarticResidual_ne_selfAdjointMatrix
    (A : Matrix (Fin 4) (Fin 4) ℝ)
    (hA : A.transpose = A) :
    quarticResidual ≠ A := by
  intro h
  apply quarticResidual_not_selfAdjoint
  rw [h, hA]

/-- Representation-level obstruction.  Any injective map that preserves the
real adjoint carries the quartic residual to a non-self-adjoint operator.  This
models the minimum algebraic properties of a faithful star representation. -/
theorem quarticResidual_image_not_selfAdjoint
    {n : ℕ}
    (f : Matrix (Fin 4) (Fin 4) ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hinjective : Function.Injective f)
    (hadjoint : ∀ A, f A.transpose = (f A).transpose) :
    (f quarticResidual).transpose ≠ f quarticResidual := by
  intro hself
  apply quarticResidual_not_selfAdjoint
  apply hinjective
  rw [hadjoint]
  exact hself

/-- The symmetric observable response obtained after left/right Perron
compression. -/
noncomputable def perronCompressedConstitutiveBlock
    (q : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  constitutiveBlock (quarticBiResidualCoefficient q)

/-- Unlike the full directed residual, the compressed response block is
self-adjoint. -/
theorem perronCompressedConstitutiveBlock_selfAdjoint
    (q : ℝ) :
    (perronCompressedConstitutiveBlock q).transpose =
      perronCompressedConstitutiveBlock q := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [perronCompressedConstitutiveBlock, constitutiveBlock,
      Matrix.transpose_apply]

/-- On the quartic root, the compressed observable determinant is exactly the
PDT screening coefficient. -/
theorem perronCompressedConstitutiveBlock_det
    (q : ℝ) (hq : q ^ 4 = q + 1) (hq1 : 1 < q) :
    Matrix.det (perronCompressedConstitutiveBlock q) =
      screening (lambda4 q) := by
  unfold perronCompressedConstitutiveBlock
  rw [constitutiveBlock_det,
    quarticBiResidualCoefficient_eq_lambda4 q hq hq1]

/-- Complete carrier classification.  The directed four-state operator is
neither self-adjoint nor normal, and no nondegenerate diagonal change of
information metric makes it self-adjoint.  Nevertheless its canonical
left/right Perron compression is the scalar `lambda4`, and that scalar defines
the symmetric two-channel response whose determinant is `S_Q`. -/
theorem quarticPerron_carrier_classification
    (q : ℝ) (hq : q ^ 4 = q + 1) (hq1 : 1 < q) :
    quarticResidual.transpose ≠ quarticResidual ∧
      quarticResidual.transpose * quarticResidual ≠
        quarticResidual * quarticResidual.transpose ∧
      (∀ w₀ w₁ w₂ w₃ : ℝ, w₀ ≠ 0 →
        diagonalWeight4 w₀ w₁ w₂ w₃ * quarticResidual ≠
          quarticResidual.transpose * diagonalWeight4 w₀ w₁ w₂ w₃) ∧
      quarticBiResidualCoefficient q = lambda4 q ∧
      (perronCompressedConstitutiveBlock q).transpose =
        perronCompressedConstitutiveBlock q ∧
      Matrix.det (perronCompressedConstitutiveBlock q) =
        (2 * q - 1) / q ^ 2 := by
  have hq0 : q ≠ 0 := by linarith
  refine ⟨quarticResidual_not_selfAdjoint,
    quarticResidual_not_normal, ?_,
    quarticBiResidualCoefficient_eq_lambda4 q hq hq1,
    perronCompressedConstitutiveBlock_selfAdjoint q, ?_⟩
  · intro w₀ w₁ w₂ w₃ hw₀
    exact quarticResidual_no_diagonal_symmetrizer w₀ w₁ w₂ w₃ hw₀
  · rw [perronCompressedConstitutiveBlock_det q hq hq1,
      quartic_screening_identity q hq0]

/-- The directed residual has an exact discrete history law on its positive
Perron line: after `n` transfer steps the surviving amplitude is
`lambda4 q ^ n`.  This is the role appropriate to a transfer operator rather
than a static observable. -/
theorem quarticResidual_perron_iterate
    (q : ℝ) (hq : q ^ 4 = q + 1) (hq0 : q ≠ 0) (n : ℕ) :
    (quarticResidual ^ n).mulVec (quarticPerronVector q) =
      fun i => lambda4 q ^ n * quarticPerronVector q i := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih]
      change quarticResidual.mulVec
          ((lambda4 q ^ n) • quarticPerronVector q) = _
      rw [Matrix.mulVec_smul,
        quarticResidual_perron q hq hq0]
      funext i
      simp [pow_succ']
      ring

/-- The scale-free left/right Perron reading of an `n`-step history is exactly
the same power `lambda4 q ^ n`. -/
theorem quarticBiResidualIterateCoefficient_eq_pow
    (q : ℝ) (hq : q ^ 4 = q + 1) (hq1 : 1 < q) (n : ℕ) :
    dotProduct (quarticLeftPerronVector q)
        ((quarticResidual ^ n).mulVec (quarticPerronVector q)) /
      dotProduct (quarticLeftPerronVector q) (quarticPerronVector q) =
        lambda4 q ^ n := by
  have hq0 : q ≠ 0 := by linarith
  have hden :
      dotProduct (quarticLeftPerronVector q) (quarticPerronVector q) ≠ 0 := by
    rw [quarticPerron_pairing q hq]
    nlinarith
  rw [quarticResidual_perron_iterate q hq hq0 n]
  have hdot :
      dotProduct (quarticLeftPerronVector q)
          (fun i => lambda4 q ^ n * quarticPerronVector q i) =
        lambda4 q ^ n *
          dotProduct (quarticLeftPerronVector q) (quarticPerronVector q) := by
    simp [dotProduct, Fin.sum_univ_succ]
    ring
  rw [hdot]
  field_simp [hden]

/-- The quartic polynomial also has a real root strictly between `-1` and
zero.  This is the real conjugate branch that prevents the complete quartic
transfer dynamics from being a global contraction. -/
theorem exists_quartic_negative_root :
    ∃ r : ℝ, -1 < r ∧ r < 0 ∧ r ^ 4 = r + 1 := by
  let f : ℝ → ℝ := fun x => x ^ 4 - x - 1
  have hf : Continuous f := by
    fun_prop
  have hzero : (0 : ℝ) ∈ Set.Icc (f 0) (f (-1)) := by
    norm_num [f]
  have himage :=
    intermediate_value_Icc' (show (-1 : ℝ) ≤ 0 by norm_num)
      hf.continuousOn hzero
  rcases himage with ⟨r, hrange, hfr⟩
  have hrneg : r < 0 := by
    rcases lt_or_eq_of_le hrange.2 with hr | hr
    · exact hr
    · subst r
      norm_num [f] at hfr
  have hrminus : -1 < r := by
    rcases lt_or_eq_of_le hrange.1 with hr | hr
    · exact hr
    · subst r
      norm_num [f] at hfr
  refine ⟨r, hrminus, hrneg, ?_⟩
  dsimp [f] at hfr
  nlinarith

/-- Every quartic root in `(-1,0)` gives an expanding residual eigenvalue:
`lambda4 r` is strictly larger than two. -/
theorem negativeQuarticResidualWeight_gt_two
    (r : ℝ) (hrminus : -1 < r) (hrneg : r < 0) :
    2 < lambda4 r := by
  have hrecip : 1 / r < -1 := by
    apply (div_lt_iff_of_neg hrneg).2
    nlinarith
  unfold lambda4
  nlinarith

/-- The full directed quartic residual contains an expanding real conjugate
eigenline.  Hence decay on the positive Perron line is a selected compression,
not global convergence of the four-state transfer operator. -/
theorem exists_expanding_quarticResidual_eigenline :
    ∃ r : ℝ,
      -1 < r ∧ r < 0 ∧
      (quarticResidual.mulVec (quarticPerronVector r) =
        fun i => lambda4 r * quarticPerronVector r i) ∧
      2 < lambda4 r := by
  obtain ⟨r, hrminus, hrneg, hrquartic⟩ := exists_quartic_negative_root
  have hr0 : r ≠ 0 := ne_of_lt hrneg
  exact ⟨r, hrminus, hrneg,
    quarticResidual_perron r hrquartic hr0,
    negativeQuarticResidualWeight_gt_two r hrminus hrneg⟩

/-- On the positive quartic Perron branch, the inverse-step residue is a
strict contraction. -/
theorem positiveQuarticResidualWeight_mem_unitInterval
    (q : ℝ) (hq1 : 1 < q) :
    0 < lambda4 q ∧ lambda4 q < 1 := by
  have hqpos : 0 < q := lt_trans zero_lt_one hq1
  have hrecippos : 0 < 1 / q := div_pos zero_lt_one hqpos
  have hreciplt : 1 / q < 1 := (div_lt_one hqpos).2 hq1
  unfold lambda4
  constructor <;> nlinarith

/-- Consequently the selected positive Perron history amplitude tends to
zero under repeated residual steps. -/
theorem positiveQuarticResidualWeight_tendsto_zero
    (q : ℝ) (hq1 : 1 < q) :
    Filter.Tendsto (fun n : ℕ => lambda4 q ^ n)
      Filter.atTop (nhds 0) := by
  obtain ⟨hlpos, hllt⟩ :=
    positiveQuarticResidualWeight_mem_unitInterval q hq1
  exact tendsto_pow_atTop_nhds_zero_of_lt_one hlpos.le hllt

/-- Quartic settle/escape dichotomy.  The positive Perron residue decays to
zero, but the same directed transfer operator has a negative-real conjugate
eigenline with multiplier larger than two at every step. -/
theorem quarticResidual_settle_escape_dichotomy
    (q : ℝ) (hq : q ^ 4 = q + 1) (hq1 : 1 < q) :
    Filter.Tendsto (fun n : ℕ => lambda4 q ^ n)
        Filter.atTop (nhds 0) ∧
      (∀ n : ℕ,
        (quarticResidual ^ n).mulVec (quarticPerronVector q) =
          fun i => lambda4 q ^ n * quarticPerronVector q i) ∧
      ∃ r : ℝ,
        -1 < r ∧ r < 0 ∧ 2 < lambda4 r ∧
        ∀ n : ℕ,
          (quarticResidual ^ n).mulVec (quarticPerronVector r) =
            fun i => lambda4 r ^ n * quarticPerronVector r i := by
  have hq0 : q ≠ 0 := by linarith
  refine ⟨positiveQuarticResidualWeight_tendsto_zero q hq1,
    fun n => quarticResidual_perron_iterate q hq hq0 n, ?_⟩
  obtain ⟨r, hrminus, hrneg, hrquartic⟩ := exists_quartic_negative_root
  have hr0 : r ≠ 0 := ne_of_lt hrneg
  exact ⟨r, hrminus, hrneg,
    negativeQuarticResidualWeight_gt_two r hrminus hrneg,
    fun n => quarticResidual_perron_iterate r hrquartic hr0 n⟩

/-- Dynamics-to-observable capstone.  The full quartic operator cannot become
a static self-adjoint observable under a faithful adjoint-preserving map, while
its canonical biorthogonal compression gives the self-adjoint response with
determinant `S_Q`. -/
theorem quarticPerron_dynamics_observable_capstone
    (q : ℝ) (hq : q ^ 4 = q + 1) (hq1 : 1 < q) :
    quarticResidual.transpose ≠ quarticResidual ∧
      quarticBiResidualCoefficient q = lambda4 q ∧
      (perronCompressedConstitutiveBlock q).transpose =
        perronCompressedConstitutiveBlock q ∧
      Matrix.det (perronCompressedConstitutiveBlock q) =
        (2 * q - 1) / q ^ 2 := by
  have hq0 : q ≠ 0 := by linarith
  refine ⟨quarticResidual_not_selfAdjoint,
    quarticBiResidualCoefficient_eq_lambda4 q hq hq1,
    perronCompressedConstitutiveBlock_selfAdjoint q, ?_⟩
  rw [perronCompressedConstitutiveBlock_det q hq hq1,
    quartic_screening_identity q hq0]

#print axioms GravityScreening.quarticResidual_not_selfAdjoint
#print axioms GravityScreening.quarticResidual_ne_selfAdjointMatrix
#print axioms GravityScreening.quarticResidual_image_not_selfAdjoint
#print axioms GravityScreening.perronCompressedConstitutiveBlock_selfAdjoint
#print axioms GravityScreening.perronCompressedConstitutiveBlock_det
#print axioms GravityScreening.quarticPerron_carrier_classification
#print axioms GravityScreening.quarticResidual_perron_iterate
#print axioms GravityScreening.quarticBiResidualIterateCoefficient_eq_pow
#print axioms GravityScreening.exists_quartic_negative_root
#print axioms GravityScreening.negativeQuarticResidualWeight_gt_two
#print axioms GravityScreening.exists_expanding_quarticResidual_eigenline
#print axioms GravityScreening.positiveQuarticResidualWeight_mem_unitInterval
#print axioms GravityScreening.positiveQuarticResidualWeight_tendsto_zero
#print axioms GravityScreening.quarticResidual_settle_escape_dichotomy
#print axioms GravityScreening.quarticPerron_dynamics_observable_capstone

end GravityScreening
