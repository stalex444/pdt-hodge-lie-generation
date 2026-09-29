module
public import GravityScreening.UnifiedCouplingGrammar
public import Mathlib.Algebra.Lie.Classical

@[expose] public section

/-!
# The fifteen generators of the four-dimensional conformal algebra

Mathlib defines the indefinite orthogonal Lie algebra `so'(p,q)` as the
matrices skew-adjoint for a diagonal form of signature `(p,q)`, but does not
currently supply its finite-dimensional rank.  This file proves directly that
`so'(4,2)` has real dimension `15`.

The proof has three exact steps.  Multiplication by the signature matrix gives
a linear equivalence from the indefinite algebra to ordinary skew-symmetric
six-by-six matrices.  Reindexing `Fin 4 ⊕ Fin 2` by `Fin 6` changes no data.
Finally, a skew-symmetric matrix is linearly equivalent to its entries strictly
above the diagonal, of which there are fifteen.

This is a theorem about the Lie algebra itself.  The physical statement that
this conformal generator count supplies the electromagnetic exponent is made
explicit in the final equality; no numerical observation enters its proof.
-/

namespace GravityScreening

open Module

/-- Strictly upper-triangular index pairs in an `n` by `n` matrix. -/
abbrev UpperPair (n : ℕ) := {ij : Fin n × Fin n // ij.1 < ij.2}

/-- Restrict a skew-symmetric matrix to its strictly upper-triangular entries. -/
noncomputable def definiteSoToUpper (n : ℕ) :
    LieAlgebra.Orthogonal.so (Fin n) ℝ →ₗ[ℝ] (UpperPair n → ℝ) where
  toFun A ij := (A : Matrix (Fin n) (Fin n) ℝ) ij.1.1 ij.1.2
  map_add' A B := by
    funext ij
    rfl
  map_smul' c A := by
    funext ij
    rfl

/-- Reconstruct a skew-symmetric matrix from its upper-triangular entries. -/
noncomputable def upperSkewMatrix {n : ℕ} (x : UpperPair n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ := fun i j =>
  if h : i < j then x ⟨(i, j), h⟩
  else if h' : j < i then -x ⟨(j, i), h'⟩
  else 0

/-- The reconstruction map lands in the definite orthogonal Lie algebra. -/
noncomputable def upperToDefiniteSo (n : ℕ) :
    (UpperPair n → ℝ) →ₗ[ℝ] LieAlgebra.Orthogonal.so (Fin n) ℝ where
  toFun x := ⟨upperSkewMatrix x, by
    rw [LieAlgebra.Orthogonal.mem_so (Fin n) ℝ]
    ext i j
    simp only [Matrix.transpose_apply]
    rcases lt_trichotomy i j with hij | hij | hij
    · simp [upperSkewMatrix, hij, not_lt_of_ge (le_of_lt hij)]
    · subst j
      simp [upperSkewMatrix]
    · simp [upperSkewMatrix, hij, not_lt_of_ge (le_of_lt hij)]
    ⟩
  map_add' x y := by
    apply Subtype.ext
    ext i j
    rcases lt_trichotomy i j with hij | hij | hij
    · simp [upperSkewMatrix, hij]
    · subst j
      simp [upperSkewMatrix]
    · simp [upperSkewMatrix, hij, not_lt_of_ge (le_of_lt hij)]
      ring
  map_smul' c x := by
    apply Subtype.ext
    ext i j
    rcases lt_trichotomy i j with hij | hij | hij
    · simp [upperSkewMatrix, hij]
    · subst j
      simp [upperSkewMatrix]
    · simp [upperSkewMatrix, hij, not_lt_of_ge (le_of_lt hij)]

/-- A skew-symmetric matrix is completely and uniquely determined by its
strictly upper-triangular entries. -/
noncomputable def definiteSoUpperEquiv (n : ℕ) :
    LieAlgebra.Orthogonal.so (Fin n) ℝ ≃ₗ[ℝ] (UpperPair n → ℝ) where
  toLinearMap := definiteSoToUpper n
  invFun := upperToDefiniteSo n
  left_inv A := by
    apply Subtype.ext
    ext i j
    have hskew : Matrix.transpose (A : Matrix (Fin n) (Fin n) ℝ) =
        -(A : Matrix (Fin n) (Fin n) ℝ) :=
      (LieAlgebra.Orthogonal.mem_so (Fin n) ℝ
        (A : Matrix (Fin n) (Fin n) ℝ)).mp A.property
    change
      upperSkewMatrix (fun ij =>
        (A : Matrix (Fin n) (Fin n) ℝ) ij.val.1 ij.val.2) i j =
        (A : Matrix (Fin n) (Fin n) ℝ) i j
    rcases lt_trichotomy i j with hij | hij | hij
    · simp [upperSkewMatrix, hij]
    · subst j
      have hii := congr_fun (congr_fun hskew i) i
      change (A : Matrix (Fin n) (Fin n) ℝ) i i =
        -(A : Matrix (Fin n) (Fin n) ℝ) i i at hii
      have hz : (A : Matrix (Fin n) (Fin n) ℝ) i i = 0 := by linarith
      simp [upperSkewMatrix, hz]
    · have hentry := congr_fun (congr_fun hskew j) i
      change (A : Matrix (Fin n) (Fin n) ℝ) i j =
        -(A : Matrix (Fin n) (Fin n) ℝ) j i at hentry
      simp [upperSkewMatrix, hij]
      exact fun _ => hentry.symm
  right_inv x := by
    funext ij
    change upperSkewMatrix x ij.1.1 ij.1.2 = x ij
    simp [upperSkewMatrix, ij.property]

/-- The definite six-dimensional orthogonal Lie algebra has rank fifteen. -/
theorem finrank_definiteSoSix :
    finrank ℝ (LieAlgebra.Orthogonal.so (Fin 6) ℝ) = 15 := by
  rw [LinearEquiv.finrank_eq (definiteSoUpperEquiv 6)]
  rw [Module.finrank_fintype_fun_eq_card]
  decide

/-- The six coordinates split into four spacetime-sign coordinates and two of
the opposite sign. -/
abbrev ConformalIndex := Fin 4 ⊕ Fin 2

/-- Mathlib's matrix model of the real Lie algebra `so(4,2)`. -/
abbrev conformalLieAlgebra :=
  LieAlgebra.Orthogonal.so' (Fin 4) (Fin 2) ℝ

/-- The signature `(4,2)` metric. -/
noncomputable abbrev conformalMetric42 :
    Matrix ConformalIndex ConformalIndex ℝ :=
  LieAlgebra.Orthogonal.indefiniteDiagonal (Fin 4) (Fin 2) ℝ

private theorem conformalMetric42_sq :
    conformalMetric42 * conformalMetric42 = 1 := by
  change Matrix.diagonal (Sum.elim (fun _ : Fin 4 => (1 : ℝ))
      (fun _ : Fin 2 => -1)) *
      Matrix.diagonal (Sum.elim (fun _ : Fin 4 => (1 : ℝ))
        (fun _ : Fin 2 => -1)) = 1
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · by_cases h : i = j <;> simp [h, Matrix.one_apply]
  · simp
  · simp
  · by_cases h : i = j <;> simp [h, Matrix.one_apply]

private theorem conformalMetric42_transpose :
    Matrix.transpose conformalMetric42 = conformalMetric42 :=
  Matrix.diagonal_transpose _

/-- Left multiplication by the signature matrix sends an `so(4,2)` matrix to
an ordinary skew-symmetric matrix. -/
noncomputable def conformalToDefiniteSo :
    conformalLieAlgebra →ₗ[ℝ]
      LieAlgebra.Orthogonal.so ConformalIndex ℝ where
  toFun A := ⟨conformalMetric42 *
      (A : Matrix ConformalIndex ConformalIndex ℝ), by
    rw [LieAlgebra.Orthogonal.mem_so ConformalIndex ℝ]
    have hA := A.property
    change (A : Matrix ConformalIndex ConformalIndex ℝ) ∈
      skewAdjointMatricesLieSubalgebra conformalMetric42 at hA
    rw [mem_skewAdjointMatricesLieSubalgebra,
      mem_skewAdjointMatricesSubmodule] at hA
    change Matrix.transpose (A : Matrix ConformalIndex ConformalIndex ℝ) *
        conformalMetric42 =
      conformalMetric42 *
        (-(A : Matrix ConformalIndex ConformalIndex ℝ)) at hA
    calc
      Matrix.transpose (conformalMetric42 *
          (A : Matrix ConformalIndex ConformalIndex ℝ)) =
          Matrix.transpose (A : Matrix ConformalIndex ConformalIndex ℝ) *
            Matrix.transpose conformalMetric42 := Matrix.transpose_mul _ _
      _ = Matrix.transpose (A : Matrix ConformalIndex ConformalIndex ℝ) *
          conformalMetric42 := by rw [conformalMetric42_transpose]
      _ = conformalMetric42 *
          (-(A : Matrix ConformalIndex ConformalIndex ℝ)) := hA
      _ = -(conformalMetric42 *
          (A : Matrix ConformalIndex ConformalIndex ℝ)) := by rw [mul_neg]
    ⟩
  map_add' A B := by
    apply Subtype.ext
    simp [mul_add]
  map_smul' c A := by
    apply Subtype.ext
    simp

/-- The inverse again multiplies by the signature matrix, whose square is the
identity. -/
noncomputable def definiteSoToConformal :
    LieAlgebra.Orthogonal.so ConformalIndex ℝ →ₗ[ℝ]
      conformalLieAlgebra where
  toFun B := ⟨conformalMetric42 *
      (B : Matrix ConformalIndex ConformalIndex ℝ), by
    change conformalMetric42 *
        (B : Matrix ConformalIndex ConformalIndex ℝ) ∈
      skewAdjointMatricesLieSubalgebra conformalMetric42
    rw [mem_skewAdjointMatricesLieSubalgebra,
      mem_skewAdjointMatricesSubmodule]
    change Matrix.transpose (conformalMetric42 *
        (B : Matrix ConformalIndex ConformalIndex ℝ)) * conformalMetric42 =
      conformalMetric42 * (-(conformalMetric42 *
        (B : Matrix ConformalIndex ConformalIndex ℝ)))
    have hB : Matrix.transpose (B : Matrix ConformalIndex ConformalIndex ℝ) =
        -(B : Matrix ConformalIndex ConformalIndex ℝ) :=
      (LieAlgebra.Orthogonal.mem_so ConformalIndex ℝ
        (B : Matrix ConformalIndex ConformalIndex ℝ)).mp B.property
    calc
      Matrix.transpose (conformalMetric42 *
          (B : Matrix ConformalIndex ConformalIndex ℝ)) * conformalMetric42 =
          (Matrix.transpose (B : Matrix ConformalIndex ConformalIndex ℝ) *
            Matrix.transpose conformalMetric42) * conformalMetric42 := by
              rw [Matrix.transpose_mul]
      _ = Matrix.transpose (B : Matrix ConformalIndex ConformalIndex ℝ) *
          (conformalMetric42 * conformalMetric42) := by
            rw [conformalMetric42_transpose, Matrix.mul_assoc]
      _ = Matrix.transpose (B : Matrix ConformalIndex ConformalIndex ℝ) := by
            rw [conformalMetric42_sq, mul_one]
      _ = -(B : Matrix ConformalIndex ConformalIndex ℝ) := hB
      _ = conformalMetric42 * (-(conformalMetric42 *
          (B : Matrix ConformalIndex ConformalIndex ℝ))) := by
            symm
            rw [mul_neg, ← Matrix.mul_assoc, conformalMetric42_sq, one_mul]
    ⟩
  map_add' A B := by
    apply Subtype.ext
    simp [mul_add]
  map_smul' c A := by
    apply Subtype.ext
    simp

/-- The indefinite and definite six-coordinate orthogonal Lie algebras have
the same underlying real vector-space dimension. -/
noncomputable def conformalDefiniteSoEquiv :
    conformalLieAlgebra ≃ₗ[ℝ]
      LieAlgebra.Orthogonal.so ConformalIndex ℝ where
  toLinearMap := conformalToDefiniteSo
  invFun := definiteSoToConformal
  left_inv A := by
    apply Subtype.ext
    change conformalMetric42 * (conformalMetric42 *
      (A : Matrix ConformalIndex ConformalIndex ℝ)) = A
    rw [← Matrix.mul_assoc, conformalMetric42_sq, one_mul]
  right_inv B := by
    apply Subtype.ext
    change conformalMetric42 * (conformalMetric42 *
      (B : Matrix ConformalIndex ConformalIndex ℝ)) = B
    rw [← Matrix.mul_assoc, conformalMetric42_sq, one_mul]

/-- Reindex the `4+2` coordinates by six coordinates. -/
noncomputable def conformalIndexFinSixEquiv :
    LieAlgebra.Orthogonal.so ConformalIndex ℝ ≃ₗ[ℝ]
      LieAlgebra.Orthogonal.so (Fin 6) ℝ where
  toFun A := ⟨Matrix.reindex finSumFinEquiv finSumFinEquiv
      (A : Matrix ConformalIndex ConformalIndex ℝ), by
    rw [LieAlgebra.Orthogonal.mem_so (Fin 6) ℝ]
    have hA : Matrix.transpose (A : Matrix ConformalIndex ConformalIndex ℝ) =
        -(A : Matrix ConformalIndex ConformalIndex ℝ) :=
      (LieAlgebra.Orthogonal.mem_so ConformalIndex ℝ
        (A : Matrix ConformalIndex ConformalIndex ℝ)).mp A.property
    rw [Matrix.transpose_reindex, hA]
    rfl
    ⟩
  invFun B := ⟨Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm
      (B : Matrix (Fin 6) (Fin 6) ℝ), by
    rw [LieAlgebra.Orthogonal.mem_so ConformalIndex ℝ]
    have hB : Matrix.transpose (B : Matrix (Fin 6) (Fin 6) ℝ) =
        -(B : Matrix (Fin 6) (Fin 6) ℝ) :=
      (LieAlgebra.Orthogonal.mem_so (Fin 6) ℝ
        (B : Matrix (Fin 6) (Fin 6) ℝ)).mp B.property
    rw [Matrix.transpose_reindex, hB]
    rfl
    ⟩
  map_add' A B := by
    apply Subtype.ext
    rfl
  map_smul' c A := by
    apply Subtype.ext
    rfl
  left_inv A := by
    apply Subtype.ext
    ext i j
    simp [Matrix.reindex_apply]
  right_inv B := by
    apply Subtype.ext
    ext i j
    simp [Matrix.reindex_apply]

/-- **Conformal generator count.** The real Lie algebra `so(4,2)` has exactly
fifteen independent generators. -/
theorem finrank_conformalLieAlgebra :
    finrank ℝ conformalLieAlgebra = 15 := by
  rw [LinearEquiv.finrank_eq conformalDefiniteSoEquiv]
  rw [LinearEquiv.finrank_eq conformalIndexFinSixEquiv]
  exact finrank_definiteSoSix

/-- The PDT electromagnetic exponent equals the kernel-computed dimension of
the four-dimensional conformal Lie algebra. -/
theorem electromagneticExponent_eq_finrank_conformalLieAlgebra :
    electromagneticExponent = finrank ℝ conformalLieAlgebra := by
  rw [finrank_conformalLieAlgebra]
  rfl

#print axioms GravityScreening.definiteSoUpperEquiv
#print axioms GravityScreening.conformalDefiniteSoEquiv
#print axioms GravityScreening.finrank_conformalLieAlgebra
#print axioms GravityScreening.electromagneticExponent_eq_finrank_conformalLieAlgebra

end GravityScreening
