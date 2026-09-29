module
public import GravityScreening.ErasureTTBridge

@[expose] public section

/-!
# A norm-preserving two-state code for the TT graviton

The Frobenius norm of the physical TT tensor is twice the Euclidean norm of
its plus/cross coordinate vector.  Multiplication by `sqrt(2)` therefore gives
the canonical norm-preserving embedding into the two-state complex data space
used by the erasure dilation.  This file proves its norm, rotation, and
exterior-channel intertwining properties.

Calling this mathematical code the physical horizon code remains a physics
identification.
-/

namespace GravityScreening

/-- Canonically normalized two-state encoding of the real TT polarization
vector.  The factor `sqrt(2)` is fixed by the tensor Frobenius norm. -/
noncomputable def ttHorizonCodeEncoding
    (x : TTCoordinates) : Fin 2 → ℂ :=
  fun i => (Real.sqrt 2 : ℂ) * (x i : ℂ)

/-- Quarter-turn on the complex two-state code. -/
noncomputable def ttCodeQuarterTurn (psi : Fin 2 → ℂ) : Fin 2 → ℂ :=
  ![-psi 1, psi 0]

/-- The code norm is exactly the complete two-polarization TT tensor norm. -/
theorem ttHorizonCodeEncoding_normSq (x : TTCoordinates) :
    finiteNormSq (ttHorizonCodeEncoding x) =
      ttShearNormSq (x 0) (x 1) := by
  have hsqrt : Real.sqrt 2 * Real.sqrt 2 = 2 :=
    Real.mul_self_sqrt (by norm_num)
  simp [finiteNormSq, ttHorizonCodeEncoding, ttShearNormSq_eq,
    Fin.sum_univ_succ, Complex.normSq_mul, Complex.normSq_ofReal,
    hsqrt]
  ring

/-- The normalized code is injective. -/
theorem ttHorizonCodeEncoding_injective :
    Function.Injective ttHorizonCodeEncoding := by
  intro x y hxy
  funext i
  have hi := congrFun hxy i
  have hire := congrArg Complex.re hi
  simp [ttHorizonCodeEncoding] at hire
  exact hire

/-- Encoding intertwines the physical plus/cross quarter-turn with the code
quarter-turn. -/
theorem ttHorizonCodeEncoding_quarterTurn (x : TTCoordinates) :
    ttHorizonCodeEncoding (ttPolarizationQuarterTurn.mulVec x) =
      ttCodeQuarterTurn (ttHorizonCodeEncoding x) := by
  funext i
  fin_cases i <;>
    simp [ttHorizonCodeEncoding, ttCodeQuarterTurn,
      ttPolarizationQuarterTurn, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]

/-- The exterior data port of the erasure dilation carries the normalized TT
code exactly into the normalized code of the attenuated TT tensor. -/
theorem erasureDilation_ttHorizonCode_exterior
    (s : ℝ) (x : TTCoordinates) (i : Fin 2) :
    erasureDilation s (ttHorizonCodeEncoding x) (some i, none) =
      ttHorizonCodeEncoding (ttExteriorCoordinates s x) i := by
  simp [erasureDilation, ttHorizonCodeEncoding, ttExteriorCoordinates]
  ring

/-- Decode the retained exterior code amplitude back to canonically
normalized real TT coordinates. -/
noncomputable def ttHorizonCodeExteriorDecode
    (s : ℝ) (x : TTCoordinates) : TTCoordinates :=
  fun i =>
    (erasureDilation s (ttHorizonCodeEncoding x) (some i, none)).re /
      Real.sqrt 2

/-- Encoding, applying the exterior erasure port, and decoding is exactly the
TT response `sqrt(s) I₂`. -/
theorem ttHorizonCodeExteriorDecode_eq_ttExteriorCoordinates
    (s : ℝ) (x : TTCoordinates) :
    ttHorizonCodeExteriorDecode s x = ttExteriorCoordinates s x := by
  have htwo : Real.sqrt 2 ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  funext i
  simp [ttHorizonCodeExteriorDecode, erasureDilation,
    ttHorizonCodeEncoding, ttExteriorCoordinates]
  field_simp [htwo]

/-- The retained code norm is the quartic weight times the complete TT tensor
norm. -/
theorem erasureDilation_ttHorizonCode_exterior_normSq
    (s : ℝ) (x : TTCoordinates) (hs : 0 ≤ s) :
    (∑ i, Complex.normSq
        (erasureDilation s (ttHorizonCodeEncoding x) (some i, none))) =
      s * ttShearNormSq (x 0) (x 1) := by
  simp_rw [erasureDilation_ttHorizonCode_exterior]
  change
    finiteNormSq
        (ttHorizonCodeEncoding (ttExteriorCoordinates s x)) =
      s * ttShearNormSq (x 0) (x 1)
  rw [ttHorizonCodeEncoding_normSq]
  have hsqrt : (Real.sqrt s) ^ 2 = s := Real.sq_sqrt hs
  simp [ttExteriorCoordinates, ttShearNormSq_eq]
  nlinarith

/-- Quartic specialization of the norm-preserving code response. -/
theorem quarticErasureDilation_ttHorizonCode_exterior_normSq
    (q : ℝ) (x : TTCoordinates) (hq : 1 < q) :
    (∑ i, Complex.normSq
        (quarticErasureDilation q (ttHorizonCodeEncoding x)
          (some i, none))) =
      ((2 * q - 1) / q ^ 2) * ttShearNormSq (x 0) (x 1) := by
  have hq0 : q ≠ 0 := ne_of_gt (lt_trans (by norm_num) hq)
  unfold quarticErasureDilation
  rw [erasureDilation_ttHorizonCode_exterior_normSq
    (screening (lambda4 q)) x (quarticScreening_bounds q hq).1]
  rw [quartic_screening_identity q hq0]

/-- Capstone using the norm-preserving horizon-code encoding itself: the
decoded quartic exterior state describes the same nonzero physical TT metric
exactly when Newton's coupling has the inverse-screening response. -/
theorem quarticTTHorizonCode_samePhysicalMetric_iff_newtonResponse
    (q kappa0 kappaQ G0 GQ : ℝ) (x : TTCoordinates)
    (hq : 1 < q) (hkappa0 : 0 ≤ kappa0) (hkappaQ : 0 ≤ kappaQ)
    (hkappa0_sq : kappa0 ^ 2 = 32 * Real.pi * G0)
    (hkappaQ_sq : kappaQ ^ 2 = 32 * Real.pi * GQ)
    (hmode : x 0 ≠ 0 ∨ x 1 ≠ 0) :
    physicalTTTensor kappaQ
          (ttHorizonCodeExteriorDecode (screening (lambda4 q)) x) =
        physicalTTTensor kappa0 x ↔
      GQ = G0 / ((2 * q - 1) / q ^ 2) := by
  rw [ttHorizonCodeExteriorDecode_eq_ttExteriorCoordinates]
  exact quarticTTExterior_samePhysicalMetric_iff_newtonResponse
    q kappa0 kappaQ G0 GQ x hq hkappa0 hkappaQ
      hkappa0_sq hkappaQ_sq hmode

/-- The encoding is norm-preserving directly on the TT tensor subspace, not
only on a chosen pair of coordinates. -/
noncomputable def ttSubspaceHorizonCodeEncoding
    (h : ttSubspace) : Fin 2 → ℂ :=
  ttHorizonCodeEncoding (ttToCoordinates h)

theorem ttSubspaceHorizonCodeEncoding_normSq (h : ttSubspace) :
    finiteNormSq (ttSubspaceHorizonCodeEncoding h) =
      tensorPairing h.1 h.1 := by
  rw [show ttSubspaceHorizonCodeEncoding h =
      ttHorizonCodeEncoding (ttToCoordinates h) by rfl]
  rw [ttHorizonCodeEncoding_normSq]
  change
    ttShearNormSq (h.1 0 0) (h.1 0 1) = tensorPairing h.1 h.1
  have hcomplete := ttTensor_complete h.1 h.2
  rw [hcomplete, ttTensor_pairing]
  rfl

#print axioms GravityScreening.ttHorizonCodeEncoding_normSq
#print axioms GravityScreening.ttHorizonCodeEncoding_injective
#print axioms GravityScreening.ttHorizonCodeEncoding_quarterTurn
#print axioms GravityScreening.erasureDilation_ttHorizonCode_exterior
#print axioms GravityScreening.ttHorizonCodeExteriorDecode_eq_ttExteriorCoordinates
#print axioms GravityScreening.erasureDilation_ttHorizonCode_exterior_normSq
#print axioms GravityScreening.quarticErasureDilation_ttHorizonCode_exterior_normSq
#print axioms GravityScreening.quarticTTHorizonCode_samePhysicalMetric_iff_newtonResponse
#print axioms GravityScreening.ttSubspaceHorizonCodeEncoding_normSq

end GravityScreening
