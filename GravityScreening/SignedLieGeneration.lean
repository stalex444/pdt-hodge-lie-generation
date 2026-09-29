module
public import Mathlib.Algebra.Lie.Classical
public import Mathlib.Tactic

@[expose] public section

/-! A reusable matrix-unit proof of Lie generation from all signed skew
directions and one signed symmetric off-diagonal direction. -/

namespace GravityScreening.SignedLieGeneration

open Matrix

attribute [local instance] LieRing.ofAssociativeRing

variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

def skew (q : n → K) (i j : n) : Matrix n n K :=
  single i j (q j) - single j i (q i)

def sym (q : n → K) (i j : n) : Matrix n n K :=
  single i j (q j) + single j i (q i)

omit [Fintype n] in
lemma sym_swap (q : n → K) (i j : n) : sym q j i = sym q i j := by
  simp [sym, add_comm]

lemma sym_skew_chain (q : n → K) (a b c : n)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ⁅sym q a b, skew q b c⁆ = q b • sym q a c := by
  simp [sym, skew, Ring.lie_def, add_mul, mul_add, sub_mul, mul_sub,
    Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne,
    hab, hac, hbc, hab.symm, hac.symm, hbc.symm, smul_add,
    Matrix.smul_single, mul_comm]

lemma sym_skew_fork (q : n → K) (a b c : n)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ⁅sym q a b, skew q a c⁆ = q a • sym q b c := by
  simp [sym, skew, Ring.lie_def, add_mul, mul_add, sub_mul, mul_sub,
    Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne,
    hab, hac, hbc, hab.symm, hac.symm, hbc.symm, smul_add,
    Matrix.smul_single]

omit [Fintype n] in
lemma sym_add_skew (q : n → K) (i j : n) :
    sym q i j + skew q i j = (2 * q j) • single i j 1 := by
  simp only [sym, skew, add_add_sub_cancel, Matrix.smul_single, smul_eq_mul, mul_one]
  rw [← Matrix.single_add]
  congr 1
  ring

theorem all_sym_mem (q : n → K) (hq : ∀ i, q i ≠ 0)
    (L : LieSubalgebra K (Matrix n n K)) (a b : n) (hab : a ≠ b)
    (hskew : ∀ i j, skew q i j ∈ L) (hseed : sym q a b ∈ L) :
    ∀ i j, i ≠ j → sym q i j ∈ L := by
  have hrow : ∀ j, a ≠ j → sym q a j ∈ L := by
    intro j haj
    by_cases hbj : b = j
    · simpa [← hbj] using hseed
    · have h := L.lie_mem hseed (hskew b j)
      rw [sym_skew_chain q a b j hab haj hbj] at h
      have hh := L.smul_mem (q b)⁻¹ h
      simpa [smul_smul, hq b] using hh
  intro i j hij
  by_cases hai : a = i
  · subst i
    exact hrow j hij
  by_cases haj : a = j
  · subst j
    rw [sym_swap]
    exact hrow i hai
  have h := L.lie_mem (hrow i hai) (hskew a j)
  rw [sym_skew_fork q a i j hai haj hij] at h
  have hh := L.smul_mem (q a)⁻¹ h
  simpa [smul_smul, hq a] using hh

theorem all_single_mem (htwo : (2 : K) ≠ 0) (q : n → K)
    (hq : ∀ i, q i ≠ 0) (L : LieSubalgebra K (Matrix n n K))
    (a b : n) (hab : a ≠ b) (hskew : ∀ i j, skew q i j ∈ L)
    (hseed : sym q a b ∈ L) :
    ∀ i j, i ≠ j → single i j (1 : K) ∈ L := by
  intro i j hij
  have h := L.add_mem (all_sym_mem q hq L a b hab hskew hseed i j hij) (hskew i j)
  rw [sym_add_skew] at h
  have hh := L.smul_mem (2 * q j)⁻¹ h
  simpa only [smul_smul, inv_mul_cancel₀ (mul_ne_zero htwo (hq j)), one_smul] using hh

lemma diagonal_difference_mem (L : LieSubalgebra K (Matrix n n K))
    (hsingle : ∀ i j, i ≠ j → single i j (1 : K) ∈ L) (i j : n) :
    single i i (1 : K) - single j j 1 ∈ L := by
  by_cases hij : i = j
  · subst j
    simp
  · have h := L.lie_mem (hsingle i j hij) (hsingle j i (Ne.symm hij))
    simpa [Ring.lie_def, Matrix.single_mul_single_same] using h

theorem tracefree_mem_of_singles (L : LieSubalgebra K (Matrix n n K))
    (hsingle : ∀ i j, i ≠ j → single i j (1 : K) ∈ L)
    (p : n) (M : Matrix n n K) (hM : M.trace = 0) : M ∈ L := by
  let T (i j : n) := single i j (M i j) -
    if i = j then single p p (M i j) else 0
  have hT : ∀ i j, T i j ∈ L := by
    intro i j
    by_cases hij : i = j
    · subst j
      have h := L.smul_mem (M i i) (diagonal_difference_mem L hsingle i p)
      simpa [T, smul_sub, Matrix.smul_single] using h
    · have h := L.smul_mem (M i j) (hsingle i j hij)
      simpa [T, hij, Matrix.smul_single] using h
  have hsum : (∑ i, ∑ j, T i j) ∈ L :=
    L.toSubmodule.sum_mem fun i _ => L.toSubmodule.sum_mem fun j _ => hT i j
  have hd : (∑ i, single p p (M i i)) = single p p M.trace := by
    change (∑ i, (Matrix.singleLinearMap K p p) (M i i)) =
      (Matrix.singleLinearMap K p p) (∑ i, M i i)
    exact (map_sum _ _ _).symm
  have heq : (∑ i, ∑ j, T i j) = M := by
    simp only [T, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ,
      if_true]
    rw [hd, hM, Matrix.single_zero, sub_zero]
    exact (Matrix.matrix_eq_sum_single M).symm
  rwa [heq] at hsum

/-- All signed skew directions and one symmetric off-diagonal direction generate
all trace-free matrices, over every field in which two is nonzero. -/
theorem tracefree_le (htwo : (2 : K) ≠ 0) (q : n → K)
    (hq : ∀ i, q i ≠ 0) (L : LieSubalgebra K (Matrix n n K))
    (a b : n) (hab : a ≠ b) (hskew : ∀ i j, skew q i j ∈ L)
    (hseed : sym q a b ∈ L) : LieAlgebra.SpecialLinear.sl n K ≤ L := by
  intro M hM
  exact tracefree_mem_of_singles L (all_single_mem htwo q hq L a b hab hskew hseed)
    a M hM

/-- Trace has rank one over any field, including fields whose characteristic
 divides the matrix size. -/
lemma finrank_sl_add_one (p : n) :
    Module.finrank K (LieAlgebra.SpecialLinear.sl n K) + 1 =
      Fintype.card n * Fintype.card n := by
  let tr := Matrix.traceLinearMap n K K
  have htr : Function.Surjective tr := by
    intro c
    refine ⟨Matrix.single p p c, ?_⟩
    exact Matrix.trace_single_eq_same p c
  have h := LinearMap.finrank_range_add_finrank_ker tr
  rw [LinearMap.range_eq_top.mpr htr, finrank_top, Module.finrank_self,
    Module.finrank_matrix, Module.finrank_self, mul_one] at h
  change Module.finrank K (LinearMap.ker tr) + 1 = _
  omega

#print axioms tracefree_le
#print axioms finrank_sl_add_one

end GravityScreening.SignedLieGeneration
