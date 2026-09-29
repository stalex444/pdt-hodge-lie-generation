module
public import GravityScreening.ConservedFlux

@[expose] public section

/-!
# Two-dimensional information area of the erasure channel

The fixed-erasure channel scales the diagonal Fisher bilinear form by its
retained weight `s`.  On a two-dimensional parameter surface this scales the
associated information-area element by exactly `s`, because the determinant
scales by `s^2` and the area element is its positive square root.
-/

namespace GravityScreening

open scoped BigOperators

/-- Bilinear diagonal Fisher metric at `p`. -/
noncomputable def diagonalFisherPair {n : ℕ}
    (p x y : Fin n → ℝ) : ℝ :=
  ∑ i, x i * y i / p i

/-- Fisher pairing after applying a fixed erasure channel. -/
noncomputable def erasureFisherPair {n : ℕ}
    (s : ℝ) (p x y : Fin n → ℝ) : ℝ :=
  ∑ i, (s * x i) * (s * y i) / (s * p i)

/-- The entire Fisher bilinear form, including cross terms, contracts by `s`. -/
theorem erasureFisherPair_eq {n : ℕ}
    (s : ℝ) (p x y : Fin n → ℝ)
    (hs : s ≠ 0) (hp : ∀ i, p i ≠ 0) :
    erasureFisherPair s p x y = s * diagonalFisherPair p x y := by
  unfold erasureFisherPair diagonalFisherPair
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  field_simp [hs, hp i]

/-- Determinant of a two-dimensional information metric. -/
def informationMetricDet2 (g00 g01 g10 g11 : ℝ) : ℝ :=
  g00 * g11 - g01 * g10

/-- Positive information-area element of a two-dimensional metric. -/
noncomputable def informationArea2 (g00 g01 g10 g11 : ℝ) : ℝ :=
  Real.sqrt (informationMetricDet2 g00 g01 g10 g11)

/-- Uniform metric scaling by `s` multiplies the two-dimensional determinant
by `s^2`. -/
theorem informationMetricDet2_scale
    (s g00 g01 g10 g11 : ℝ) :
    informationMetricDet2 (s * g00) (s * g01) (s * g10) (s * g11) =
      s ^ 2 * informationMetricDet2 g00 g01 g10 g11 := by
  unfold informationMetricDet2
  ring

/-- For nonnegative `s`, uniform metric scaling multiplies the positive
two-dimensional square-root determinant by `s`. -/
theorem informationArea2_scale
    (s g00 g01 g10 g11 : ℝ)
    (hs0 : 0 ≤ s) :
    informationArea2 (s * g00) (s * g01) (s * g10) (s * g11) =
      s * informationArea2 g00 g01 g10 g11 := by
  unfold informationArea2
  rw [informationMetricDet2_scale]
  rw [Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq hs0]

/-- The two-dimensional Fisher area of two tangent directions contracts by
the erasure retention weight. -/
theorem erasureFisherArea2_eq {n : ℕ}
    (s : ℝ) (p x y : Fin n → ℝ)
    (hs0 : 0 ≤ s) (hs : s ≠ 0) (hp : ∀ i, p i ≠ 0) :
    informationArea2
        (erasureFisherPair s p x x) (erasureFisherPair s p x y)
        (erasureFisherPair s p y x) (erasureFisherPair s p y y) =
      s * informationArea2
        (diagonalFisherPair p x x) (diagonalFisherPair p x y)
        (diagonalFisherPair p y x) (diagonalFisherPair p y y) := by
  rw [erasureFisherPair_eq s p x x hs hp,
    erasureFisherPair_eq s p x y hs hp,
    erasureFisherPair_eq s p y x hs hp,
    erasureFisherPair_eq s p y y hs hp]
  exact informationArea2_scale s _ _ _ _ hs0

/-- At the quartic retention weight, the information-area response is exactly
the PDT gravity-screening factor `(2q-1)/q^2`. -/
theorem quarticErasureFisherArea2_eq {n : ℕ}
    (q : ℝ) (p x y : Fin n → ℝ)
    (hq : 1 < q) (hS : screening (lambda4 q) ≠ 0)
    (hp : ∀ i, p i ≠ 0) :
    informationArea2
        (erasureFisherPair (screening (lambda4 q)) p x x)
        (erasureFisherPair (screening (lambda4 q)) p x y)
        (erasureFisherPair (screening (lambda4 q)) p y x)
        (erasureFisherPair (screening (lambda4 q)) p y y) =
      ((2 * q - 1) / q ^ 2) * informationArea2
        (diagonalFisherPair p x x) (diagonalFisherPair p x y)
        (diagonalFisherPair p y x) (diagonalFisherPair p y y) := by
  rw [erasureFisherArea2_eq (screening (lambda4 q)) p x y
    (quarticScreening_bounds q hq).1 hS hp]
  rw [quartic_screening_identity q (by linarith)]

#print axioms GravityScreening.erasureFisherPair_eq
#print axioms GravityScreening.informationMetricDet2_scale
#print axioms GravityScreening.informationArea2_scale
#print axioms GravityScreening.erasureFisherArea2_eq
#print axioms GravityScreening.quarticErasureFisherArea2_eq

end GravityScreening
