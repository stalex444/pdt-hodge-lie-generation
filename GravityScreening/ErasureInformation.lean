module
public import GravityScreening.ModularAmplitude

@[expose] public section

/-!
# Information geometry of the quartic erasure channel

This file checks the finite diagonal form of two exact consequences of a
state-independent erasure channel: relative entropy and Fisher information are
both multiplied by the retained weight.  The identification of this channel
with a physical causal horizon is a PDT physical postulate, not a theorem of
this file.
-/

namespace GravityScreening

/-- One-coordinate contribution to diagonal relative entropy. -/
noncomputable def relativeEntropyContribution (x y : ℝ) : ℝ :=
  x * Real.log (x / y)

/-- Relative entropy of two finite diagonal weights. -/
noncomputable def diagonalRelativeEntropy {n : ℕ}
    (p r : Fin n → ℝ) : ℝ :=
  ∑ i, relativeEntropyContribution (p i) (r i)

/-- Relative entropy after both inputs pass through the same erasure channel.
The first term is the common erasure flag and the sum is the retained block. -/
noncomputable def erasureRelativeEntropy {n : ℕ}
    (s : ℝ) (p r : Fin n → ℝ) : ℝ :=
  relativeEntropyContribution (1 - s) (1 - s) +
    ∑ i, relativeEntropyContribution (s * p i) (s * r i)

/-- A common erasure flag contributes no relative entropy. -/
theorem relativeEntropyContribution_self (x : ℝ) :
    relativeEntropyContribution x x = 0 := by
  by_cases hx : x = 0
  · simp [relativeEntropyContribution, hx]
  · simp [relativeEntropyContribution, hx]

/-- A state-independent erasure channel contracts diagonal relative entropy
by exactly its retained weight `s`. -/
theorem erasureRelativeEntropy_eq {n : ℕ}
    (s : ℝ) (p r : Fin n → ℝ)
    (hs : s ≠ 0) (hr : ∀ i, r i ≠ 0) :
    erasureRelativeEntropy s p r =
      s * diagonalRelativeEntropy p r := by
  unfold erasureRelativeEntropy diagonalRelativeEntropy
  rw [relativeEntropyContribution_self]
  simp only [zero_add, relativeEntropyContribution]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hratio : (s * p i) / (s * r i) = p i / r i := by
    field_simp [hs, hr i]
  rw [hratio]
  ring

/-- The diagonal Fisher information of a tangent vector `delta` at `p`. -/
noncomputable def diagonalFisher {n : ℕ}
    (p delta : Fin n → ℝ) : ℝ :=
  ∑ i, delta i ^ 2 / p i

/-- Fisher information of the retained block of an erasure channel.  The
erasure flag has zero tangent because its weight is state independent. -/
noncomputable def erasureFisher {n : ℕ}
    (s : ℝ) (p delta : Fin n → ℝ) : ℝ :=
  ∑ i, (s * delta i) ^ 2 / (s * p i)

/-- A state-independent erasure channel contracts the diagonal Fisher metric
by exactly its retained weight. -/
theorem erasureFisher_eq {n : ℕ}
    (s : ℝ) (p delta : Fin n → ℝ)
    (hs : s ≠ 0) (hp : ∀ i, p i ≠ 0) :
    erasureFisher s p delta = s * diagonalFisher p delta := by
  unfold erasureFisher diagonalFisher
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  field_simp [hs, hp i]

/-- Repeating a fixed retention step `s` for `ticks` steps gives the
multiplicative retained weight `s^ticks`. -/
theorem iteratedRetention_succ (s : ℝ) (ticks : ℕ) :
    s ^ (ticks + 1) = s * s ^ ticks := by
  rw [pow_succ]
  ring

/-- For a nontrivial erasure step `0 < s < 1`, every additional tick strictly
reduces any positive retained distinguishability. -/
theorem iteratedRetention_strict_decrease
    (s x : ℝ) (ticks : ℕ) (hs0 : 0 < s) (hs1 : s < 1) (hx : 0 < x) :
    s ^ (ticks + 1) * x < s ^ ticks * x := by
  rw [pow_succ]
  have hpx : 0 < s ^ ticks * x := mul_pos (pow_pos hs0 ticks) hx
  nlinarith

/-- At the quartic modular defect, relative entropy contracts by the same
factor `(2q-1)/q^2` that occurs in the PDT entropy-area density. -/
theorem quarticErasureRelativeEntropy_eq {n : ℕ}
    (q : ℝ) (p r : Fin n → ℝ)
    (hq0 : q ≠ 0) (hS : screening (lambda4 q) ≠ 0)
    (hr : ∀ i, r i ≠ 0) :
    erasureRelativeEntropy (screening (lambda4 q)) p r =
      ((2 * q - 1) / q ^ 2) * diagonalRelativeEntropy p r := by
  rw [erasureRelativeEntropy_eq _ p r hS hr]
  rw [quartic_screening_identity q hq0]

/-- The corresponding quartic erasure channel contracts the diagonal Fisher
metric by the same exact factor. -/
theorem quarticErasureFisher_eq {n : ℕ}
    (q : ℝ) (p delta : Fin n → ℝ)
    (hq0 : q ≠ 0) (hS : screening (lambda4 q) ≠ 0)
    (hp : ∀ i, p i ≠ 0) :
    erasureFisher (screening (lambda4 q)) p delta =
      ((2 * q - 1) / q ^ 2) * diagonalFisher p delta := by
  rw [erasureFisher_eq _ p delta hS hp]
  rw [quartic_screening_identity q hq0]

/-! ## The exact `pQ`/screening/modular chain

The root-weighted Hodge transform and the quartic-residue response are
distinct operators.  The theorem below packages their exact consequences
together with the modular defect and erasure contraction without identifying
those operators with one another.
-/

/-- The Perron inverse-step and modular eigenvalue both fix `lambda4 q`; the
Hodge-pair response and information-erasure channel then expose the same exact
scalar `(2q-1)/q^2`. -/
theorem quarticTransformChain
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {n : ℕ} (Delta : Module.End ℂ V) (xi : V)
    (q : ℝ) (p r : Fin n → ℝ)
    (hEigen : Delta xi = ((1 / q : ℝ) : ℂ) • xi)
    (hq4 : q ^ 4 = q + 1) (hq1 : 1 < q)
    (hS : screening (lambda4 q) ≠ 0)
    (hr : ∀ i, r i ≠ 0) :
    quarticBiResidualCoefficient q = lambda4 q ∧
      (1 - Delta) xi = (lambda4 q : ℂ) • xi ∧
      Matrix.det (chiralAreaResponse (lambda4 q)) =
        (((2 * q - 1) / q ^ 2 : ℝ) : ℂ) ∧
      erasureRelativeEntropy (screening (lambda4 q)) p r =
        ((2 * q - 1) / q ^ 2) * diagonalRelativeEntropy p r := by
  have hq0 : q ≠ 0 := by linarith
  exact ⟨quarticBiResidualCoefficient_eq_lambda4 q hq4 hq1,
    modularEigenvector_defect Delta xi q hEigen,
    quartic_chiralAreaResponse_det q hq0,
    quarticErasureRelativeEntropy_eq q p r hq0 hS hr⟩

/-! ## The six-bivector rate candidate

In four dimensions `dim(Λ²) = 6`.  The candidate comparison
`screening(lambda4 q)^6 ≈ 1/q` is not exact.  The theorem below reduces its
exact residual to the cubic coordinate shown; numerical size and density
controls are deliberately kept in the reproducible audit script.
-/

/-- Exact algebraic residual of the proposed six-bivector product. -/
theorem quarticSixBivector_residual
    (q : ℝ) (hq4 : q ^ 4 = q + 1) (hq0 : q ≠ 0) :
    screening (lambda4 q) ^ 6 * q - 1 =
      (-97 + 142 * q + 33 * q ^ 2 - 69 * q ^ 3) / q ^ 12 := by
  rw [quartic_screening_identity q hq0]
  have hroot : q ^ 4 - q - 1 = 0 := by linarith
  field_simp [hq0]
  linear_combination
    (-97 + 238 * q - 193 * q ^ 2 + 64 * q ^ 3 - q ^ 4 - q ^ 5 - q ^ 8) * hroot

#print axioms GravityScreening.relativeEntropyContribution_self
#print axioms GravityScreening.erasureRelativeEntropy_eq
#print axioms GravityScreening.erasureFisher_eq
#print axioms GravityScreening.iteratedRetention_succ
#print axioms GravityScreening.iteratedRetention_strict_decrease
#print axioms GravityScreening.quarticErasureRelativeEntropy_eq
#print axioms GravityScreening.quarticErasureFisher_eq
#print axioms GravityScreening.quarticTransformChain
#print axioms GravityScreening.quarticSixBivector_residual

end GravityScreening
