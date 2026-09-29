module
public import GravityScreening.QuarticGraphKMSData

@[expose] public section

/-!
# Real-time phase and imaginary-time contraction of the quartic modular flow

The degree-one modular line fixed by the quartic graph has frequency `log q`.
Its analytic exponential is unitary on the real modular-time axis.  Evaluation
at one negative-imaginary unit gives the KMS contraction `1/q`; subtracting
that contraction from the identity gives the quartic residue `lambda4 q`.

This is the exact analytic relation between the clock-like phase and the
screening precursor.  It does not identify the graph modular group with a
particular physical horizon modular group.
-/

namespace GravityScreening

/-- Analytic degree-one modular multiplier with frequency `log q`. -/
noncomputable def quarticModularAnalyticFlow (q : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (-Complex.I * (Real.log q : ℂ) * z)

/-- The analytic modular multipliers form a representation of addition. -/
theorem quarticModularAnalyticFlow_add (q : ℝ) (z w : ℂ) :
    quarticModularAnalyticFlow q (z + w) =
      quarticModularAnalyticFlow q z * quarticModularAnalyticFlow q w := by
  unfold quarticModularAnalyticFlow
  rw [← Complex.exp_add]
  congr 1
  ring

/-- The real modular-time axis has unit norm. -/
theorem quarticModularAnalyticFlow_real_norm (q t : ℝ) :
    ‖quarticModularAnalyticFlow q (t : ℂ)‖ = 1 := by
  unfold quarticModularAnalyticFlow
  have harg :
      -Complex.I * (Real.log q : ℂ) * (t : ℂ) =
        ((-(Real.log q * t) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg]
  exact Complex.norm_exp_ofReal_mul_I _

/-- One real modular tick is a unit-modulus phase at angle `-log q`. -/
theorem quarticModularAnalyticFlow_real_tick (q : ℝ) :
    quarticModularAnalyticFlow q 1 =
      Complex.exp (((-Real.log q : ℝ) : ℂ) * Complex.I) := by
  unfold quarticModularAnalyticFlow
  congr 1
  push_cast
  ring

/-- One negative-imaginary modular step is the inverse Perron contraction. -/
theorem quarticModularAnalyticFlow_imaginaryStep
    (q : ℝ) (hq : 0 < q) :
    quarticModularAnalyticFlow q (-Complex.I) = (1 / q : ℝ) := by
  unfold quarticModularAnalyticFlow
  have harg :
      -Complex.I * (Real.log q : ℂ) * (-Complex.I) =
        ((-Real.log q : ℝ) : ℂ) := by
    calc
      -Complex.I * (Real.log q : ℂ) * (-Complex.I) =
          (Complex.I * Complex.I) * (Real.log q : ℂ) := by ring
      _ = (-1 : ℂ) * (Real.log q : ℂ) := by rw [Complex.I_mul_I]
      _ = ((-Real.log q : ℝ) : ℂ) := by push_cast; ring
  rw [harg, ← Complex.ofReal_exp]
  exact_mod_cast quarticGaugeBoltzmannFactor q hq

/-- The imaginary modular-step defect is exactly the quartic residue. -/
theorem quarticModularAnalyticFlow_imaginaryDefect
    (q : ℝ) (hq : 0 < q) :
    1 - quarticModularAnalyticFlow q (-Complex.I) =
      (lambda4 q : ℂ) := by
  rw [quarticModularAnalyticFlow_imaginaryStep q hq]
  unfold lambda4
  push_cast
  rfl

/-- Time/gravity analytic capstone: the same graph-fixed analytic multiplier
is a norm-one phase on real modular time and has quartic residue `lambda4` at
the KMS imaginary step. -/
theorem quarticModular_timeAndDefect_capstone
    (q t : ℝ) (hq : 0 < q) :
    ‖quarticModularAnalyticFlow q (t : ℂ)‖ = 1 ∧
      quarticModularAnalyticFlow q (-Complex.I) = (1 / q : ℝ) ∧
      1 - quarticModularAnalyticFlow q (-Complex.I) =
        (lambda4 q : ℂ) := by
  exact ⟨quarticModularAnalyticFlow_real_norm q t,
    quarticModularAnalyticFlow_imaginaryStep q hq,
    quarticModularAnalyticFlow_imaginaryDefect q hq⟩

#print axioms GravityScreening.quarticModularAnalyticFlow_add
#print axioms GravityScreening.quarticModularAnalyticFlow_real_norm
#print axioms GravityScreening.quarticModularAnalyticFlow_imaginaryStep
#print axioms GravityScreening.quarticModularAnalyticFlow_imaginaryDefect
#print axioms GravityScreening.quarticModular_timeAndDefect_capstone

end GravityScreening
