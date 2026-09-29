module
public import GravityScreening.HorizonShearNormalization

@[expose] public section

/-!
# Coherent shear matching across the quartic information channel

For a canonically normalized graviton shear amplitude `a`, the physical metric
shear is proportional to `(kappa / 2) * a`, with
`kappa^2 = 32 * pi * G`.  A passive information splitter with retained weight
`s` sends the accessible canonical amplitude to `sqrt s * a`.

This file proves that matching the microscopic and effective descriptions to
the same nonzero physical metric shear is equivalent to the inverse screening
of Newton's coupling.  The result isolates the physical input: the quartic
channel must act on the canonically normalized horizon shear amplitude.
-/

namespace GravityScreening

/-- Accessible canonical amplitude after a passive splitter of retained
weight `s`. -/
noncomputable def attenuatedCanonicalAmplitude (s a : ℝ) : ℝ :=
  Real.sqrt s * a

/-- Physical metric-shear amplitude associated with a canonically normalized
amplitude and gravitational normalization `kappa`. -/
noncomputable def physicalMetricShearAmplitude (kappa a : ℝ) : ℝ :=
  (kappa / 2) * a

/-- For positive retention and nonnegative gravitational normalizations,
matching the attenuated canonical mode to the same physical metric shear is
equivalent to scaling Newton's coupling by the inverse retained weight. -/
theorem coherentShear_samePhysicalMetric_iff_newtonResponse
    (s kappa0 kappaQ G0 GQ a : ℝ)
    (hs : 0 < s) (hkappa0 : 0 ≤ kappa0) (hkappaQ : 0 ≤ kappaQ)
    (hkappa0_sq : kappa0 ^ 2 = 32 * Real.pi * G0)
    (hkappaQ_sq : kappaQ ^ 2 = 32 * Real.pi * GQ)
    (ha : a ≠ 0) :
    physicalMetricShearAmplitude kappaQ
          (attenuatedCanonicalAmplitude s a) =
        physicalMetricShearAmplitude kappa0 a ↔
      GQ = G0 / s := by
  have hs0 : 0 ≤ s := le_of_lt hs
  have hs_ne : s ≠ 0 := ne_of_gt hs
  have hsqrt0 : 0 ≤ Real.sqrt s := Real.sqrt_nonneg s
  have hsqrt_sq : (Real.sqrt s) ^ 2 = s := Real.sq_sqrt hs0
  constructor
  · intro hmetric
    have hscaled : (kappaQ * Real.sqrt s) * a = kappa0 * a := by
      calc
        (kappaQ * Real.sqrt s) * a =
            2 * physicalMetricShearAmplitude kappaQ
              (attenuatedCanonicalAmplitude s a) := by
                simp [physicalMetricShearAmplitude,
                  attenuatedCanonicalAmplitude]
                ring
        _ = 2 * physicalMetricShearAmplitude kappa0 a := by rw [hmetric]
        _ = kappa0 * a := by
          simp [physicalMetricShearAmplitude]
          ring
    have hkappa_match : kappaQ * Real.sqrt s = kappa0 := by
      exact mul_right_cancel₀ ha hscaled
    have hsq : (kappaQ * Real.sqrt s) ^ 2 = kappa0 ^ 2 := by
      rw [hkappa_match]
    have hGs : GQ * s = G0 := by
      have hpi : 32 * Real.pi ≠ 0 :=
        mul_ne_zero (by norm_num) Real.pi_ne_zero
      apply mul_left_cancel₀ hpi
      calc
        (32 * Real.pi) * (GQ * s) = (kappaQ ^ 2) * s := by
          rw [hkappaQ_sq]
          ring
        _ = (kappaQ * Real.sqrt s) ^ 2 := by
          rw [mul_pow, hsqrt_sq]
        _ = kappa0 ^ 2 := hsq
        _ = (32 * Real.pi) * G0 := hkappa0_sq
    exact (eq_div_iff hs_ne).2 hGs
  · intro hG
    have hGs : GQ * s = G0 := (eq_div_iff hs_ne).1 hG
    have hsq : (kappaQ * Real.sqrt s) ^ 2 = kappa0 ^ 2 := by
      calc
        (kappaQ * Real.sqrt s) ^ 2 = (kappaQ ^ 2) * s := by
          rw [mul_pow, hsqrt_sq]
        _ = (32 * Real.pi) * (GQ * s) := by
          rw [hkappaQ_sq]
          ring
        _ = (32 * Real.pi) * G0 := by rw [hGs]
        _ = kappa0 ^ 2 := hkappa0_sq.symm
    have hkappa_match : kappaQ * Real.sqrt s = kappa0 := by
      have hleft : 0 ≤ kappaQ * Real.sqrt s :=
        mul_nonneg hkappaQ hsqrt0
      nlinarith
    unfold physicalMetricShearAmplitude attenuatedCanonicalAmplitude
    rw [← hkappa_match]
    ring

/-- Quartic specialization: matching the `sqrt(S_Q)`-attenuated canonical
shear to the same physical metric shear is exactly equivalent to the PDT
screened Newton response. -/
theorem quarticCoherentShear_samePhysicalMetric_iff_newtonResponse
    (q kappa0 kappaQ G0 GQ a : ℝ)
    (hq : 1 < q) (hkappa0 : 0 ≤ kappa0) (hkappaQ : 0 ≤ kappaQ)
    (hkappa0_sq : kappa0 ^ 2 = 32 * Real.pi * G0)
    (hkappaQ_sq : kappaQ ^ 2 = 32 * Real.pi * GQ)
    (ha : a ≠ 0) :
    physicalMetricShearAmplitude kappaQ
          (attenuatedCanonicalAmplitude (screening (lambda4 q)) a) =
        physicalMetricShearAmplitude kappa0 a ↔
      GQ = G0 / ((2 * q - 1) / q ^ 2) := by
  have hq0 : q ≠ 0 := ne_of_gt (lt_trans (by norm_num) hq)
  have hS : 0 < screening (lambda4 q) := by
    rw [quartic_screening_identity q hq0]
    have hnum : 0 < 2 * q - 1 := by linarith
    have hden : 0 < q ^ 2 := sq_pos_of_ne_zero hq0
    exact div_pos hnum hden
  rw [← quartic_screening_identity q hq0]
  exact coherentShear_samePhysicalMetric_iff_newtonResponse
    (screening (lambda4 q)) kappa0 kappaQ G0 GQ a
    hS hkappa0 hkappaQ hkappa0_sq hkappaQ_sq ha

#print axioms GravityScreening.coherentShear_samePhysicalMetric_iff_newtonResponse
#print axioms GravityScreening.quarticCoherentShear_samePhysicalMetric_iff_newtonResponse

end GravityScreening
