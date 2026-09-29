module
public import GravityScreening.JacobsonPlacement

@[expose] public section

/-!
# Conserved global flux in the finite erasure dilation

The exterior data branch carries weight `s` and the hidden data branch carries
weight `1-s`.  If the same diagonal observable is assigned to the data
wherever it resides, its total expectation is unchanged by the dilation.  This
is the finite algebraic distinction between screened exterior accessibility
and an unscaled globally conserved flux.
-/

namespace GravityScreening

open scoped BigOperators

/-- Expectation of a real diagonal observable in a finite pure state. -/
noncomputable def finiteDiagonalExpectation {n : ℕ}
    (k : Fin n → ℝ) (psi : Fin n → ℂ) : ℝ :=
  ∑ i, k i * Complex.normSq (psi i)

/-- Contribution from data retained in the exterior branch. -/
noncomputable def exteriorDataExpectation {n : ℕ}
    (k : Fin n → ℝ)
    (Psi : Option (Fin n) × Option (Fin n) → ℂ) : ℝ :=
  ∑ i, k i * Complex.normSq (Psi (some i, none))

/-- Contribution from data transferred to the hidden branch. -/
noncomputable def hiddenDataExpectation {n : ℕ}
    (k : Fin n → ℝ)
    (Psi : Option (Fin n) × Option (Fin n) → ℂ) : ℝ :=
  ∑ i, k i * Complex.normSq (Psi (none, some i))

/-- The exterior expectation is multiplied by the retained weight. -/
theorem erasureDilation_exterior_expectation {n : ℕ}
    (s : ℝ) (k : Fin n → ℝ) (psi : Fin n → ℂ) (hs0 : 0 ≤ s) :
    exteriorDataExpectation k (erasureDilation s psi) =
      s * finiteDiagonalExpectation k psi := by
  unfold exteriorDataExpectation finiteDiagonalExpectation
  simp_rw [erasureDilation, Complex.normSq_mul, Complex.normSq_ofReal]
  rw [show Real.sqrt s * Real.sqrt s = s by
    nlinarith [Real.sq_sqrt hs0]]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The hidden expectation is multiplied by the complementary weight. -/
theorem erasureDilation_hidden_expectation {n : ℕ}
    (s : ℝ) (k : Fin n → ℝ) (psi : Fin n → ℂ) (hs1 : s ≤ 1) :
    hiddenDataExpectation k (erasureDilation s psi) =
      (1 - s) * finiteDiagonalExpectation k psi := by
  unfold hiddenDataExpectation finiteDiagonalExpectation
  simp_rw [erasureDilation, Complex.normSq_mul, Complex.normSq_ofReal]
  have hcomp : 0 ≤ 1 - s := sub_nonneg.mpr hs1
  rw [show Real.sqrt (1 - s) * Real.sqrt (1 - s) = 1 - s by
    nlinarith [Real.sq_sqrt hcomp]]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Exterior plus hidden expectation equals the original expectation. -/
theorem erasureDilation_total_expectation {n : ℕ}
    (s : ℝ) (k : Fin n → ℝ) (psi : Fin n → ℂ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    exteriorDataExpectation k (erasureDilation s psi) +
        hiddenDataExpectation k (erasureDilation s psi) =
      finiteDiagonalExpectation k psi := by
  rw [erasureDilation_exterior_expectation s k psi hs0,
    erasureDilation_hidden_expectation s k psi hs1]
  ring

/-- Quartic specialization: the globally counted diagonal flux is unchanged
even though the exterior contribution is screened. -/
theorem quarticErasureDilation_total_expectation {n : ℕ}
    (q : ℝ) (k : Fin n → ℝ) (psi : Fin n → ℂ) (hq : 1 < q) :
    exteriorDataExpectation k (quarticErasureDilation q psi) +
        hiddenDataExpectation k (quarticErasureDilation q psi) =
      finiteDiagonalExpectation k psi := by
  unfold quarticErasureDilation
  exact erasureDilation_total_expectation _ _ _
    (quarticScreening_bounds q hq).1 (quarticScreening_bounds q hq).2

#print axioms GravityScreening.erasureDilation_exterior_expectation
#print axioms GravityScreening.erasureDilation_hidden_expectation
#print axioms GravityScreening.erasureDilation_total_expectation
#print axioms GravityScreening.quarticErasureDilation_total_expectation

end GravityScreening
