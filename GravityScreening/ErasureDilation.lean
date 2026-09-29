module
public import GravityScreening.ErasureInformation

@[expose] public section

/-!
# A finite horizon-cell Stinespring dilation

This file realizes the fixed quantum erasure channel by an explicit
norm-preserving map.  The exterior output type has the original data states
plus an erasure flag.  The hidden output type has a vacuum flag plus a copy of
the original data states.  The physical identification of these two systems
with the two sides of a causal horizon is not made by this file.
-/

namespace GravityScreening

open scoped BigOperators

/-- Squared norm of a finite complex amplitude vector. -/
noncomputable def finiteNormSq {n : ℕ} (psi : Fin n → ℂ) : ℝ :=
  ∑ i, Complex.normSq (psi i)

/-- Squared norm of a finite bipartite amplitude vector. -/
noncomputable def bipartiteNormSq {B E : Type*}
    [Fintype B] [Fintype E] (Psi : B × E → ℂ) : ℝ :=
  ∑ b, ∑ e, Complex.normSq (Psi (b, e))

/-- The Stinespring vector for a fixed-erasure channel.

`some i` in the exterior system is retained data and `none` is the erasure
flag.  `none` in the hidden system is its vacuum and `some i` carries the
input state when the exterior branch is erased. -/
noncomputable def erasureDilation {n : ℕ} (s : ℝ) (psi : Fin n → ℂ) :
    Option (Fin n) × Option (Fin n) → ℂ
  | (some i, none) => (Real.sqrt s : ℂ) * psi i
  | (none, some i) => (Real.sqrt (1 - s) : ℂ) * psi i
  | _ => 0

/-- The dilation preserves total squared norm for `0 ≤ s ≤ 1`. -/
theorem erasureDilation_normSq {n : ℕ} (s : ℝ) (psi : Fin n → ℂ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    bipartiteNormSq (erasureDilation s psi) = finiteNormSq psi := by
  unfold bipartiteNormSq
  simp_rw [Fintype.sum_option]
  simp only [erasureDilation, Complex.normSq_zero, Finset.sum_const_zero,
    zero_add, add_zero]
  simp_rw [Complex.normSq_mul, Complex.normSq_ofReal]
  rw [show Real.sqrt s * Real.sqrt s = s by nlinarith [Real.sq_sqrt hs0]]
  have hcomp : 0 ≤ 1 - s := sub_nonneg.mpr hs1
  rw [show Real.sqrt (1 - s) * Real.sqrt (1 - s) = 1 - s by
    nlinarith [Real.sq_sqrt hcomp]]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  simp [finiteNormSq]
  ring

/-- Exterior reduced density matrix obtained by summing over the hidden
system. -/
noncomputable def exteriorReduced {n : ℕ}
    (Psi : Option (Fin n) × Option (Fin n) → ℂ) :
    Option (Fin n) → Option (Fin n) → ℂ :=
  fun b b' => ∑ e, Psi (b, e) * star (Psi (b', e))

/-- The retained exterior block is exactly `s |psi><psi|`. -/
theorem erasureDilation_exterior_data {n : ℕ}
    (s : ℝ) (psi : Fin n → ℂ) (i j : Fin n) (hs0 : 0 ≤ s) :
    exteriorReduced (erasureDilation s psi) (some i) (some j) =
      (s : ℂ) * (psi i * star (psi j)) := by
  unfold exteriorReduced
  rw [Fintype.sum_option]
  simp [erasureDilation]
  have hsqrt : ((Real.sqrt s : ℂ) ^ 2) = (s : ℂ) := by
    exact_mod_cast Real.sq_sqrt hs0
  calc
    (Real.sqrt s : ℂ) * psi i *
          ((Real.sqrt s : ℂ) * star (psi j)) =
        (Real.sqrt s : ℂ) ^ 2 * (psi i * star (psi j)) := by ring
    _ = (s : ℂ) * (psi i * star (psi j)) := by rw [hsqrt]

/-- The erasure flag carries the complementary probability times the input
norm. -/
theorem erasureDilation_exterior_flag {n : ℕ}
    (s : ℝ) (psi : Fin n → ℂ) (hs1 : s ≤ 1) :
    exteriorReduced (erasureDilation s psi) none none =
      ((1 - s : ℝ) : ℂ) * (finiteNormSq psi : ℂ) := by
  unfold exteriorReduced
  rw [Fintype.sum_option]
  simp only [erasureDilation, star_zero, mul_zero, zero_add]
  have hcomp : 0 ≤ 1 - s := sub_nonneg.mpr hs1
  have hsqrt : ((Real.sqrt (1 - s) : ℂ) ^ 2) = ((1 - s : ℝ) : ℂ) := by
    exact_mod_cast Real.sq_sqrt hcomp
  calc
    (∑ x, (Real.sqrt (1 - s) : ℂ) * psi x *
        star ((Real.sqrt (1 - s) : ℂ) * psi x)) =
        ∑ x, ((1 - s : ℝ) : ℂ) * (Complex.normSq (psi x) : ℂ) := by
      apply Finset.sum_congr rfl
      intro x hx
      have hstar : star ((Real.sqrt (1 - s) : ℂ)) =
          (Real.sqrt (1 - s) : ℂ) := by
        change (starRingEnd ℂ) ((Real.sqrt (1 - s) : ℝ) : ℂ) = _
        exact Complex.conj_ofReal _
      rw [star_mul, hstar, Complex.star_def]
      calc
        (Real.sqrt (1 - s) : ℂ) * psi x *
              ((starRingEnd ℂ) (psi x) * (Real.sqrt (1 - s) : ℂ)) =
            (Real.sqrt (1 - s) : ℂ) ^ 2 *
              (psi x * (starRingEnd ℂ) (psi x)) := by ring
        _ = ((1 - s : ℝ) : ℂ) * (Complex.normSq (psi x) : ℂ) := by
          rw [Complex.mul_conj, hsqrt]
    _ = ((1 - s : ℝ) : ℂ) * (finiteNormSq psi : ℂ) := by
      rw [← Finset.mul_sum]
      simp [finiteNormSq]

/-- Retained data and the erasure flag have zero exterior coherence. -/
theorem erasureDilation_exterior_cross {n : ℕ}
    (s : ℝ) (psi : Fin n → ℂ) (i : Fin n) :
    exteriorReduced (erasureDilation s psi) (some i) none = 0 := by
  unfold exteriorReduced
  rw [Fintype.sum_option]
  simp [erasureDilation]

/-- The adjoint exterior cross block also vanishes. -/
theorem erasureDilation_exterior_cross' {n : ℕ}
    (s : ℝ) (psi : Fin n → ℂ) (i : Fin n) :
    exteriorReduced (erasureDilation s psi) none (some i) = 0 := by
  unfold exteriorReduced
  rw [Fintype.sum_option]
  simp [erasureDilation]

/-- Hidden reduced density matrix obtained by summing over the exterior
system. -/
noncomputable def hiddenReduced {n : ℕ}
    (Psi : Option (Fin n) × Option (Fin n) → ℂ) :
    Option (Fin n) → Option (Fin n) → ℂ :=
  fun e e' => ∑ b, Psi (b, e) * star (Psi (b, e'))

/-- The data block of the hidden system contains the original state with the
complementary weight `1-s`. -/
theorem erasureDilation_hidden_data {n : ℕ}
    (s : ℝ) (psi : Fin n → ℂ) (i j : Fin n) (hs1 : s ≤ 1) :
    hiddenReduced (erasureDilation s psi) (some i) (some j) =
      ((1 - s : ℝ) : ℂ) * (psi i * star (psi j)) := by
  unfold hiddenReduced
  rw [Fintype.sum_option]
  simp [erasureDilation]
  have hcomp : 0 ≤ 1 - s := sub_nonneg.mpr hs1
  have hsqrt : ((Real.sqrt (1 - s) : ℂ) ^ 2) = ((1 - s : ℝ) : ℂ) := by
    exact_mod_cast Real.sq_sqrt hcomp
  calc
    (Real.sqrt (1 - s) : ℂ) * psi i *
          ((Real.sqrt (1 - s) : ℂ) * star (psi j)) =
        (Real.sqrt (1 - s) : ℂ) ^ 2 *
          (psi i * star (psi j)) := by ring
    _ = ((1 - s : ℝ) : ℂ) * (psi i * star (psi j)) := by
      rw [hsqrt]
    _ = (1 - (s : ℂ)) *
          (psi i * (starRingEnd ℂ) (psi j)) := by
      rw [Complex.star_def]
      push_cast
      rfl

/-- The hidden vacuum flag has the retained exterior weight `s`. -/
theorem erasureDilation_hidden_vacuum {n : ℕ}
    (s : ℝ) (psi : Fin n → ℂ) (hs0 : 0 ≤ s) :
    hiddenReduced (erasureDilation s psi) none none =
      (s : ℂ) * (finiteNormSq psi : ℂ) := by
  unfold hiddenReduced
  rw [Fintype.sum_option]
  simp only [erasureDilation, mul_zero, star_zero, zero_add]
  have hsqrt : ((Real.sqrt s : ℂ) ^ 2) = (s : ℂ) := by
    exact_mod_cast Real.sq_sqrt hs0
  calc
    (∑ x, (Real.sqrt s : ℂ) * psi x *
        star ((Real.sqrt s : ℂ) * psi x)) =
        ∑ x, (s : ℂ) * (Complex.normSq (psi x) : ℂ) := by
      apply Finset.sum_congr rfl
      intro x hx
      have hstar : star ((Real.sqrt s : ℂ)) = (Real.sqrt s : ℂ) := by
        change (starRingEnd ℂ) ((Real.sqrt s : ℝ) : ℂ) = _
        exact Complex.conj_ofReal _
      rw [star_mul, hstar, Complex.star_def]
      calc
        (Real.sqrt s : ℂ) * psi x *
              ((starRingEnd ℂ) (psi x) * (Real.sqrt s : ℂ)) =
            (Real.sqrt s : ℂ) ^ 2 *
              (psi x * (starRingEnd ℂ) (psi x)) := by ring
        _ = (s : ℂ) * (Complex.normSq (psi x) : ℂ) := by
          rw [Complex.mul_conj, hsqrt]
    _ = (s : ℂ) * (finiteNormSq psi : ℂ) := by
      rw [← Finset.mul_sum]
      simp [finiteNormSq]

/-- The exterior vacuum branch and hidden data branch have zero coherence. -/
theorem erasureDilation_hidden_cross {n : ℕ}
    (s : ℝ) (psi : Fin n → ℂ) (i : Fin n) :
    hiddenReduced (erasureDilation s psi) none (some i) = 0 := by
  unfold hiddenReduced
  rw [Fintype.sum_option]
  simp [erasureDilation]

/-- The adjoint hidden cross block also vanishes. -/
theorem erasureDilation_hidden_cross' {n : ℕ}
    (s : ℝ) (psi : Fin n → ℂ) (i : Fin n) :
    hiddenReduced (erasureDilation s psi) (some i) none = 0 := by
  unfold hiddenReduced
  rw [Fintype.sum_option]
  simp [erasureDilation]

/-! ## Quartic specialization -/

/-- For every `q>1`, the quartic screening coefficient is a valid retention
weight in `(0,1]`. -/
theorem quarticScreening_bounds (q : ℝ) (hq : 1 < q) :
    0 ≤ screening (lambda4 q) ∧ screening (lambda4 q) ≤ 1 := by
  have hq0 : 0 < q := by linarith
  have hinv0 : 0 < 1 / q := one_div_pos.mpr hq0
  have hinv1 : 1 / q < 1 := by
    rw [div_lt_one hq0]
    exact hq
  have hl0 : 0 < lambda4 q := by
    unfold lambda4
    linarith
  have hl1 : lambda4 q < 1 := by
    unfold lambda4
    linarith
  constructor
  · exact le_of_lt (screening_pos ⟨by linarith, hl1⟩)
  · unfold screening
    nlinarith [sq_nonneg (lambda4 q)]

/-- The explicit Stinespring map at the quartic gravity-screening weight. -/
noncomputable def quarticErasureDilation {n : ℕ}
    (q : ℝ) (psi : Fin n → ℂ) :
    Option (Fin n) × Option (Fin n) → ℂ :=
  erasureDilation (screening (lambda4 q)) psi

/-- The quartic horizon-cell dilation preserves global norm. -/
theorem quarticErasureDilation_normSq {n : ℕ}
    (q : ℝ) (psi : Fin n → ℂ) (hq : 1 < q) :
    bipartiteNormSq (quarticErasureDilation q psi) = finiteNormSq psi := by
  unfold quarticErasureDilation
  exact erasureDilation_normSq _ _
    (quarticScreening_bounds q hq).1 (quarticScreening_bounds q hq).2

/-- The exterior data block is retained with the exact gravity-screening
coefficient `(2q-1)/q^2`. -/
theorem quarticErasureDilation_exterior_data {n : ℕ}
    (q : ℝ) (psi : Fin n → ℂ) (i j : Fin n) (hq : 1 < q) :
    exteriorReduced (quarticErasureDilation q psi) (some i) (some j) =
      (((2 * q - 1) / q ^ 2 : ℝ) : ℂ) *
        (psi i * star (psi j)) := by
  have hq0 : q ≠ 0 := by linarith
  unfold quarticErasureDilation
  rw [erasureDilation_exterior_data _ _ _ _
    (quarticScreening_bounds q hq).1]
  rw [quartic_screening_identity q hq0]

/-- The quartic exterior erasure flag has exact weight `lambda4^2`. -/
theorem quarticErasureDilation_exterior_flag {n : ℕ}
    (q : ℝ) (psi : Fin n → ℂ) (hq : 1 < q) :
    exteriorReduced (quarticErasureDilation q psi) none none =
      ((lambda4 q ^ 2 : ℝ) : ℂ) * (finiteNormSq psi : ℂ) := by
  unfold quarticErasureDilation
  rw [erasureDilation_exterior_flag _ _
    (quarticScreening_bounds q hq).2]
  simp [screening]

/-- The hidden data block carries the same input state with the exact defect
weight `lambda4^2`. -/
theorem quarticErasureDilation_hidden_data {n : ℕ}
    (q : ℝ) (psi : Fin n → ℂ) (i j : Fin n) (hq : 1 < q) :
    hiddenReduced (quarticErasureDilation q psi) (some i) (some j) =
      ((lambda4 q ^ 2 : ℝ) : ℂ) * (psi i * star (psi j)) := by
  unfold quarticErasureDilation
  rw [erasureDilation_hidden_data _ _ _ _
    (quarticScreening_bounds q hq).2]
  simp [screening]

/-- The quartic hidden vacuum has the exact surviving gravity weight. -/
theorem quarticErasureDilation_hidden_vacuum {n : ℕ}
    (q : ℝ) (psi : Fin n → ℂ) (hq : 1 < q) :
    hiddenReduced (quarticErasureDilation q psi) none none =
      (((2 * q - 1) / q ^ 2 : ℝ) : ℂ) *
        (finiteNormSq psi : ℂ) := by
  have hq0 : q ≠ 0 := by linarith
  unfold quarticErasureDilation
  rw [erasureDilation_hidden_vacuum _ _
    (quarticScreening_bounds q hq).1]
  rw [quartic_screening_identity q hq0]

#print axioms GravityScreening.erasureDilation_normSq
#print axioms GravityScreening.erasureDilation_exterior_data
#print axioms GravityScreening.erasureDilation_exterior_flag
#print axioms GravityScreening.erasureDilation_exterior_cross
#print axioms GravityScreening.erasureDilation_exterior_cross'
#print axioms GravityScreening.erasureDilation_hidden_data
#print axioms GravityScreening.erasureDilation_hidden_vacuum
#print axioms GravityScreening.erasureDilation_hidden_cross
#print axioms GravityScreening.erasureDilation_hidden_cross'
#print axioms GravityScreening.quarticScreening_bounds
#print axioms GravityScreening.quarticErasureDilation_normSq
#print axioms GravityScreening.quarticErasureDilation_exterior_data
#print axioms GravityScreening.quarticErasureDilation_exterior_flag
#print axioms GravityScreening.quarticErasureDilation_hidden_data
#print axioms GravityScreening.quarticErasureDilation_hidden_vacuum

end GravityScreening
