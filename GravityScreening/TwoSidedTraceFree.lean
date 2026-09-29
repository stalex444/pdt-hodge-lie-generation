module
public import Mathlib.LinearAlgebra.Matrix.Trace

@[expose] public section

/-!
# The exact trace-free preservation condition for a two-sided response

For square matrices over a commutative ring on a nonempty finite index set,
the map `T ↦ D * T * E` preserves trace zero if and only if `E * D` is scalar.
The proof tests ordinary matrix units and diagonal differences. It does not
assume invertibility, irreducibility, a physical response law, or a coupling.
-/

namespace GravityScreening.TwoSidedTraceFree

open Matrix

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] [CommRing R]

/-- The annihilator of trace-zero matrices under the trace pairing is the
scalar line. This works over any commutative ring, without dividing by the
cardinality of the index set. -/
theorem trace_zero_annihilator_iff_scalar (A : Matrix ι ι R) :
    (∀ T : Matrix ι ι R, T.trace = 0 → (T * A).trace = 0) ↔
      ∃ r : R, A = r • (1 : Matrix ι ι R) := by
  constructor
  · intro h
    classical
    let k : ι := Classical.choice inferInstance
    have offdiag (i j : ι) (hij : i ≠ j) : A i j = 0 := by
      have ht : (Matrix.single j i (1 : R)).trace = 0 :=
        Matrix.trace_single_eq_of_ne j i 1 (Ne.symm hij)
      simpa only [Matrix.trace_single_mul, one_smul] using h _ ht
    have diag (i : ι) : A i i = A k k := by
      have ht : (Matrix.single i i (1 : R) - Matrix.single k k 1).trace = 0 := by
        simp only [Matrix.trace_sub, Matrix.trace_single_eq_same, sub_self]
      have hh := h _ ht
      simp only [sub_mul, Matrix.trace_sub, Matrix.trace_single_mul, one_smul] at hh
      exact sub_eq_zero.mp hh
    refine ⟨A k k, ?_⟩
    ext i j
    by_cases hij : i = j
    · subst j
      simpa using diag i
    · simp [hij, offdiag i j hij]
  · rintro ⟨r, rfl⟩ T hT
    simp [Matrix.trace_smul, hT]

/-- A two-sided linear response preserves the trace-free matrix space exactly
when the reversed product of its two factors is scalar. -/
theorem two_sided_preserves_trace_zero_iff (D E : Matrix ι ι R) :
    (∀ T : Matrix ι ι R, T.trace = 0 → (D * T * E).trace = 0) ↔
      ∃ r : R, E * D = r • (1 : Matrix ι ι R) := by
  rw [← trace_zero_annihilator_iff_scalar (E * D)]
  have cyclic (T : Matrix ι ι R) :
      (D * T * E).trace = (T * (E * D)).trace := by
    rw [Matrix.trace_mul_cycle D T E, Matrix.trace_mul_comm (E * D) T]
  simp only [cyclic]

omit [Nonempty ι] in
/-- A diagonal difference gives a concrete obstruction whenever the two
factors' reversed product has unequal diagonal entries. -/
theorem trace_two_sided_diagonal_difference (D E : Matrix ι ι R) (i j : ι) :
    (D * (Matrix.single i i (1 : R) - Matrix.single j j 1) * E).trace =
      (E * D) i i - (E * D) j j := by
  rw [Matrix.trace_mul_cycle, Matrix.trace_mul_comm]
  simp only [sub_mul, Matrix.trace_sub, Matrix.trace_single_mul, one_smul]

omit [Nonempty ι] in
/-- The preceding witness is trace free, so differing diagonal weights rule
out a response on the trace-free space. -/
theorem not_preserves_of_diagonal_ne (D E : Matrix ι ι R) (i j : ι)
    (hne : (E * D) i i ≠ (E * D) j j) :
    ¬ (∀ T : Matrix ι ι R, T.trace = 0 → (D * T * E).trace = 0) := by
  intro h
  have ht : (Matrix.single i i (1 : R) - Matrix.single j j 1).trace = 0 := by
    simp only [Matrix.trace_sub, Matrix.trace_single_eq_same, sub_self]
  have hh := h _ ht
  rw [trace_two_sided_diagonal_difference] at hh
  exact hne (sub_eq_zero.mp hh)

#print axioms trace_zero_annihilator_iff_scalar
#print axioms two_sided_preserves_trace_zero_iff
#print axioms trace_two_sided_diagonal_difference
#print axioms not_preserves_of_diagonal_ne

end GravityScreening.TwoSidedTraceFree
