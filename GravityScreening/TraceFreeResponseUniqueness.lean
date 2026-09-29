module
public import GravityScreening.SignedLieGeneration
public import Mathlib.LinearAlgebra.Determinant

@[expose] public section

/-! Scalar response rigidity on the actual special linear Lie algebra.
The proof uses a rank-one double commutator and elementary matrix units;
no simplicity instance or physical scalar calibration is assumed. -/

namespace GravityScreening.TraceFreeResponseUniqueness

open Matrix
open LieAlgebra.SpecialLinear

attribute [local instance] LieRing.ofAssociativeRing

variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

lemma double_single_commutator (i j : n) (hij : i ≠ j) (X : Matrix n n K) :
    ⁅Matrix.single i j (1 : K), ⁅Matrix.single i j (1 : K), X⁆⁆ =
      (-2 * X j i) • Matrix.single i j (1 : K) := by
  let E : Matrix n n K := Matrix.single i j 1
  have he : E * E = 0 := by simp [E, hij.symm]
  have hex : E * X * E = Matrix.single i j (X j i) := by simp [E]
  change E * (E * X - X * E) - (E * X - X * E) * E = _
  calc
    _ = E * E * X - (E * X * E + E * X * E) + X * (E * E) := by
      noncomm_ring
    _ = -(Matrix.single i j (X j i) + Matrix.single i j (X j i)) := by
      rw [he, hex]
      simp
    _ = _ := by
      ext a b
      by_cases hi : i = a <;> by_cases hj : j = b <;>
        simp [Matrix.single, hi, hj]
      ring

lemma all_single_mem_of_ideal_seed (htwo : (2 : K) ≠ 0)
    (L : LieSubalgebra K (Matrix n n K))
    (hstable : ∀ (i j : n), i ≠ j → ∀ (X : Matrix n n K), X ∈ L →
      ⁅Matrix.single i j (1 : K), X⁆ ∈ L)
    (a b : n) (hab : a ≠ b) (hseed : Matrix.single a b (1 : K) ∈ L) :
    ∀ i j, i ≠ j → Matrix.single i j (1 : K) ∈ L := by
  have hdiag : Matrix.single b b (1 : K) - Matrix.single a a (1 : K) ∈ L := by
    simpa [Ring.lie_def, Matrix.single_mul_single_same] using
      hstable b a hab.symm _ hseed
  have hback : Matrix.single b a (1 : K) ∈ L := by
    have h := hstable b a hab.symm _ hdiag
    have heq : ⁅Matrix.single b a (1 : K),
        Matrix.single b b (1 : K) - Matrix.single a a (1 : K)⁆ =
        (-2 : K) • Matrix.single b a (1 : K) := by
      simp [Ring.lie_def, mul_sub, sub_mul, Matrix.single_mul_single_same,
        Matrix.single_mul_single_of_ne, hab, Matrix.smul_single]
      ext x y
      simp only [Matrix.single, Matrix.of_apply, Matrix.sub_apply, Matrix.neg_apply]
      split_ifs <;> ring
    rw [heq] at h
    simpa [smul_smul, htwo] using L.smul_mem (-2 : K)⁻¹ h
  have hrow : ∀ j, a ≠ j → Matrix.single a j (1 : K) ∈ L := by
    intro j haj
    by_cases hbj : b = j
    · subst j; exact hseed
    have h := hstable b j hbj _ hseed
    have heq : ⁅Matrix.single b j (1 : K), Matrix.single a b (1 : K)⁆ =
        -Matrix.single a j (1 : K) := by
      simp [Ring.lie_def, Matrix.single_mul_single_same,
        Matrix.single_mul_single_of_ne, haj.symm]
    rw [heq] at h
    exact (L.neg_mem_iff).mp h
  have hcol : ∀ i, i ≠ a → Matrix.single i a (1 : K) ∈ L := by
    intro i hia
    by_cases hib : i = b
    · subst i; exact hback
    simpa [Ring.lie_def, Matrix.single_mul_single_same,
      Matrix.single_mul_single_of_ne, hia, hia.symm] using
      hstable i b hib _ hback
  intro i j hij
  by_cases hia : i = a
  · subst i; exact hrow j hij
  by_cases hja : j = a
  · subst j; exact hcol i hij
  simpa [Ring.lie_def, Matrix.single_mul_single_same,
    Matrix.single_mul_single_of_ne, hij, hij.symm] using
    hstable i a hia _ (hrow j (Ne.symm hja))

lemma double_single_commutator_sl (i j : n) (hij : i ≠ j) (X : sl n K) :
    ⁅single i j hij (1 : K), ⁅single i j hij (1 : K), X⁆⁆ =
      (-2 * X.val j i) • single i j hij (1 : K) := by
  apply Subtype.ext
  exact double_single_commutator i j hij X.val

def scalarEigensubalgebra (R : sl n K →ₗ[K] sl n K)
    (hcov : ∀ (X Y : sl n K), R ⁅X, Y⁆ = ⁅X, R Y⁆) (c : K) :
    LieSubalgebra K (sl n K) :=
  { LinearMap.ker (R - c • LinearMap.id) with
    lie_mem' := by
      intro X Y _ hY
      change R ⁅X, Y⁆ - c • ⁅X, Y⁆ = 0
      have hy : R Y = c • Y := sub_eq_zero.mp hY
      rw [hcov, hy, lie_smul, sub_self] }

@[simp] lemma mem_scalarEigensubalgebra (R : sl n K →ₗ[K] sl n K)
    (hcov : ∀ (X Y : sl n K), R ⁅X, Y⁆ = ⁅X, R Y⁆) (c : K) (X : sl n K) :
    X ∈ scalarEigensubalgebra R hcov c ↔ R X = c • X := by
  change R X - c • X = 0 ↔ _
  exact sub_eq_zero

/-- Every adjoint-covariant linear response on a special linear matrix algebra
with at least two indices is scalar, provided two is invertible. -/
theorem eq_smul_id_of_adjoint_covariant (htwo : (2 : K) ≠ 0)
    (a b : n) (hab : a ≠ b) (R : sl n K →ₗ[K] sl n K)
    (hcov : ∀ (X Y : sl n K), R ⁅X, Y⁆ = ⁅X, R Y⁆) :
    ∃ c : K, R = c • LinearMap.id := by
  let U := single a b hab (1 : K)
  let V := single b a hab.symm (1 : K)
  let c := (R V).val b a
  have hU : R U = c • U := by
    have hv : ⁅U, ⁅U, V⁆⁆ = (-2 : K) • U := by
      simpa [U, V, Matrix.single] using double_single_commutator_sl a b hab V
    have h := congrArg R hv
    rw [hcov, hcov, map_smul] at h
    rw [show ⁅U, ⁅U, R V⁆⁆ = (-2 * c) • U from
      double_single_commutator_sl a b hab (R V)] at h
    have hh := congrArg (fun Z : sl n K => (-2 : K)⁻¹ • Z) h
    simpa [smul_smul, htwo, mul_assoc] using hh.symm
  let S := scalarEigensubalgebra R hcov c
  let L := S.map (sl n K).incl
  have hstable : ∀ (i j : n), i ≠ j → ∀ (X : Matrix n n K), X ∈ L →
      ⁅Matrix.single i j (1 : K), X⁆ ∈ L := by
    intro i j hij X hX
    obtain ⟨Y, hY, rfl⟩ := (LieSubalgebra.mem_map _ _ _).mp hX
    apply (LieSubalgebra.mem_map _ _ _).mpr
    refine ⟨⁅single i j hij (1 : K), Y⁆, ?_, rfl⟩
    apply (mem_scalarEigensubalgebra R hcov c _).mpr
    have hy : R Y = c • Y := (mem_scalarEigensubalgebra R hcov c Y).mp hY
    rw [hcov, hy, lie_smul]
  have hseed : Matrix.single a b (1 : K) ∈ L := by
    apply (LieSubalgebra.mem_map _ _ _).mpr
    exact ⟨U, (mem_scalarEigensubalgebra R hcov c U).mpr hU, rfl⟩
  have hall := all_single_mem_of_ideal_seed htwo L hstable a b hab hseed
  refine ⟨c, ?_⟩
  apply LinearMap.ext
  intro X
  have hx : X.val ∈ L :=
    SignedLieGeneration.tracefree_mem_of_singles L hall a X.val X.property
  obtain ⟨Y, hY, hYX⟩ := (LieSubalgebra.mem_map _ _ _).mp hx
  have heq : Y = X := Subtype.ext hYX
  subst Y
  exact (mem_scalarEigensubalgebra R hcov c X).mp hY

/-- Every scalar response satisfies the covariance assumption. -/
theorem smul_id_adjoint_covariant (c : K) (X Y : sl n K) :
    (c • (LinearMap.id : sl n K →ₗ[K] sl n K)) ⁅X, Y⁆ =
      ⁅X, (c • (LinearMap.id : sl n K →ₗ[K] sl n K)) Y⁆ := by
  simp [lie_smul]

/-- One nonzero response calibration fixes the scalar left by adjoint covariance. -/
theorem eq_calibrated_smul_id (htwo : (2 : K) ≠ 0)
    (a b : n) (hab : a ≠ b) (R : sl n K →ₗ[K] sl n K)
    (hcov : ∀ (X Y : sl n K), R ⁅X, Y⁆ = ⁅X, R Y⁆)
    (c : K) (X : sl n K) (hX : X ≠ 0) (hcal : R X = c • X) :
    R = c • LinearMap.id := by
  obtain ⟨d, hd⟩ := eq_smul_id_of_adjoint_covariant htwo a b hab R hcov
  have hdc : d = c := by
    apply smul_left_injective K hX
    simpa [hd] using hcal
  simpa [hdc] using hd

/-- The concrete fifteen-dimensional carrier has a 224-dimensional trace-free
response algebra, and every adjoint-covariant response has determinant c^224. -/
theorem sl15_scalar_response_determinant (htwo : (2 : K) ≠ 0)
    (R : sl (Fin 15) K →ₗ[K] sl (Fin 15) K)
    (hcov : ∀ (X Y : sl (Fin 15) K), R ⁅X, Y⁆ = ⁅X, R Y⁆) :
    ∃ c : K, R = c • LinearMap.id ∧ LinearMap.det R = c ^ 224 := by
  obtain ⟨c, hc⟩ := eq_smul_id_of_adjoint_covariant htwo
    (0 : Fin 15) 1 (by decide) R hcov
  refine ⟨c, hc, ?_⟩
  have hdim : Module.finrank K (sl (Fin 15) K) = 224 := by
    have h := SignedLieGeneration.finrank_sl_add_one (K := K) (0 : Fin 15)
    norm_num at h
    omega
  simp [hc, LinearMap.det_smul, hdim]

/-- Calibrating any one nonzero trace-free direction to rho*q fixes the
whole response and its determinant. The calibration remains an explicit input. -/
theorem sl15_calibrated_response_determinant (htwo : (2 : K) ≠ 0)
    (R : sl (Fin 15) K →ₗ[K] sl (Fin 15) K)
    (hcov : ∀ (X Y : sl (Fin 15) K), R ⁅X, Y⁆ = ⁅X, R Y⁆)
    (rho q : K) (X : sl (Fin 15) K) (hX : X ≠ 0)
    (hcal : R X = (rho * q) • X) :
    R = (rho * q) • LinearMap.id ∧ LinearMap.det R = (rho * q) ^ 224 := by
  obtain ⟨c, hc, hdet⟩ := sl15_scalar_response_determinant htwo R hcov
  have hcr : c = rho * q := by
    apply smul_left_injective K hX
    simpa [hc] using hcal
  simpa [hcr] using And.intro hc hdet

#print axioms eq_smul_id_of_adjoint_covariant
#print axioms eq_calibrated_smul_id
#print axioms sl15_scalar_response_determinant
#print axioms sl15_calibrated_response_determinant

end GravityScreening.TraceFreeResponseUniqueness
