module
public import GravityScreening.CoherentShearMatching
public import GravityScreening.ElectricSourceFrame

@[expose] public section

/-!
# The quartic splitter on the physical TT polarization space

The fixed-momentum transverse-traceless graviton space has the two coordinates
`plus` and `cross`.  The polarization-blind candidate for a passive horizon
splitter acts with the same retained amplitude on both.  This file writes that
candidate as the explicit block `sqrt(s) I₂`, proves that it preserves the TT
tensor subspace and contracts its quadratic shear norm by `s`, and lifts the
scalar same-physical-metric matching theorem to the full two-polarization
tensor.  Identifying this block with the physical Q interaction is a separate
physics premise, not part of these theorems.
-/

namespace GravityScreening

/-- Exterior action of a passive splitter on the two physical graviton
polarizations. -/
noncomputable def ttExteriorBlock (s : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (Real.sqrt s) • (1 : Matrix (Fin 2) (Fin 2) ℝ)

/-- Coordinate form of the exterior TT attenuation. -/
noncomputable def ttExteriorCoordinates
    (s : ℝ) (x : TTCoordinates) : TTCoordinates :=
  fun i => Real.sqrt s * x i

/-- The displayed matrix is exactly `sqrt(s) I₂` on plus/cross coordinates. -/
theorem ttExteriorBlock_mulVec
    (s : ℝ) (x : TTCoordinates) :
    (ttExteriorBlock s).mulVec x = ttExteriorCoordinates s x := by
  rw [show ttExteriorBlock s =
      (Real.sqrt s) • (1 : Matrix (Fin 2) (Fin 2) ℝ) by rfl]
  rw [Matrix.smul_mulVec, Matrix.one_mulVec]
  rfl

/-- Applying the exterior attenuation to plus and cross coordinates is the
same as scaling the complete TT tensor. -/
theorem ttTensor_exteriorCoordinates
    (s plus cross : ℝ) :
    ttTensor
        (ttExteriorCoordinates s ![plus, cross] 0)
        (ttExteriorCoordinates s ![plus, cross] 1) =
      (Real.sqrt s) • ttTensor plus cross := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ttExteriorCoordinates, ttTensor]

/-- The passive exterior block cannot generate a longitudinal, trace, or
antisymmetric polarization: it remains in the physical TT subspace. -/
theorem ttExteriorBlock_preserves_TT
    (s plus cross : ℝ) :
    IsTTAlongZ
      (ttTensor
        (ttExteriorCoordinates s ![plus, cross] 0)
        (ttExteriorCoordinates s ![plus, cross] 1)) := by
  exact ttTensor_isTT _ _

/-- Every positive retention weight contracts the complete two-polarization
TT shear norm by that weight. -/
theorem ttExteriorBlock_normSq
    (s plus cross : ℝ) (hs : 0 ≤ s) :
    ttShearNormSq
        (ttExteriorCoordinates s ![plus, cross] 0)
        (ttExteriorCoordinates s ![plus, cross] 1) =
      s * ttShearNormSq plus cross := by
  simp [ttExteriorCoordinates, ttShearNormSq_smul, Real.sq_sqrt hs]

/-- Quartic specialization: both physical graviton polarizations carry the
same exact exterior information factor `(2q-1)/q^2`. -/
theorem quarticTTExteriorBlock_normSq
    (q plus cross : ℝ) (hq : 1 < q) :
    ttShearNormSq
        (ttExteriorCoordinates (screening (lambda4 q)) ![plus, cross] 0)
        (ttExteriorCoordinates (screening (lambda4 q)) ![plus, cross] 1) =
      ((2 * q - 1) / q ^ 2) * ttShearNormSq plus cross := by
  have hq0 : q ≠ 0 := ne_of_gt (lt_trans (by norm_num) hq)
  have hS : 0 ≤ screening (lambda4 q) :=
    (quarticScreening_bounds q hq).1
  rw [ttExteriorBlock_normSq _ plus cross hS]
  rw [quartic_screening_identity q hq0]

/-- Physical metric TT tensor obtained from canonical plus/cross coordinates.
-/
noncomputable def physicalTTTensor
    (kappa : ℝ) (x : TTCoordinates) : Matrix SpatialIndex SpatialIndex ℝ :=
  ttTensor
    (physicalMetricShearAmplitude kappa (x 0))
    (physicalMetricShearAmplitude kappa (x 1))

/-- Matching the attenuated two-polarization field to the same nonzero
physical metric tensor is equivalent to the inverse-retention Newton
response. -/
theorem ttExterior_samePhysicalMetric_iff_newtonResponse
    (s kappa0 kappaQ G0 GQ : ℝ) (x : TTCoordinates)
    (hs : 0 < s) (hkappa0 : 0 ≤ kappa0) (hkappaQ : 0 ≤ kappaQ)
    (hkappa0_sq : kappa0 ^ 2 = 32 * Real.pi * G0)
    (hkappaQ_sq : kappaQ ^ 2 = 32 * Real.pi * GQ)
    (hmode : x 0 ≠ 0 ∨ x 1 ≠ 0) :
    physicalTTTensor kappaQ (ttExteriorCoordinates s x) =
        physicalTTTensor kappa0 x ↔
      GQ = G0 / s := by
  constructor
  · intro htensor
    rcases hmode with hplus | hcross
    · have hentry := congrArg
          (fun h : Matrix SpatialIndex SpatialIndex ℝ => h 0 0) htensor
      have hscalar :
          physicalMetricShearAmplitude kappaQ
              (attenuatedCanonicalAmplitude s (x 0)) =
            physicalMetricShearAmplitude kappa0 (x 0) := by
        simpa [physicalTTTensor, ttExteriorCoordinates,
          attenuatedCanonicalAmplitude, ttTensor] using hentry
      exact (coherentShear_samePhysicalMetric_iff_newtonResponse
        s kappa0 kappaQ G0 GQ (x 0) hs hkappa0 hkappaQ
        hkappa0_sq hkappaQ_sq hplus).1 hscalar
    · have hentry := congrArg
          (fun h : Matrix SpatialIndex SpatialIndex ℝ => h 0 1) htensor
      have hscalar :
          physicalMetricShearAmplitude kappaQ
              (attenuatedCanonicalAmplitude s (x 1)) =
            physicalMetricShearAmplitude kappa0 (x 1) := by
        simpa [physicalTTTensor, ttExteriorCoordinates,
          attenuatedCanonicalAmplitude, ttTensor] using hentry
      exact (coherentShear_samePhysicalMetric_iff_newtonResponse
        s kappa0 kappaQ G0 GQ (x 1) hs hkappa0 hkappaQ
        hkappa0_sq hkappaQ_sq hcross).1 hscalar
  · intro hG
    have hunit :=
      (coherentShear_samePhysicalMetric_iff_newtonResponse
        s kappa0 kappaQ G0 GQ 1 hs hkappa0 hkappaQ
        hkappa0_sq hkappaQ_sq one_ne_zero).2 hG
    have hcoefficient :
        (kappaQ / 2) * Real.sqrt s = kappa0 / 2 := by
      simpa [physicalMetricShearAmplitude, attenuatedCanonicalAmplitude]
        using hunit
    have hcoordinate (z : ℝ) :
        physicalMetricShearAmplitude kappaQ (Real.sqrt s * z) =
          physicalMetricShearAmplitude kappa0 z := by
      unfold physicalMetricShearAmplitude
      calc
        (kappaQ / 2) * (Real.sqrt s * z) =
            ((kappaQ / 2) * Real.sqrt s) * z := by ring
        _ = (kappa0 / 2) * z := by rw [hcoefficient]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [physicalTTTensor, ttExteriorCoordinates, ttTensor,
        hcoordinate]

/-- Quartic tensor capstone: `sqrt(S_Q) I₂` preserves the same physical TT
geometry exactly when Newton's coupling has the PDT screened response. -/
theorem quarticTTExterior_samePhysicalMetric_iff_newtonResponse
    (q kappa0 kappaQ G0 GQ : ℝ) (x : TTCoordinates)
    (hq : 1 < q) (hkappa0 : 0 ≤ kappa0) (hkappaQ : 0 ≤ kappaQ)
    (hkappa0_sq : kappa0 ^ 2 = 32 * Real.pi * G0)
    (hkappaQ_sq : kappaQ ^ 2 = 32 * Real.pi * GQ)
    (hmode : x 0 ≠ 0 ∨ x 1 ≠ 0) :
    physicalTTTensor kappaQ
          (ttExteriorCoordinates (screening (lambda4 q)) x) =
        physicalTTTensor kappa0 x ↔
      GQ = G0 / ((2 * q - 1) / q ^ 2) := by
  have hq0 : q ≠ 0 := ne_of_gt (lt_trans (by norm_num) hq)
  have hS : 0 < screening (lambda4 q) := by
    rw [quartic_screening_identity q hq0]
    exact div_pos (by linarith) (sq_pos_of_ne_zero hq0)
  rw [← quartic_screening_identity q hq0]
  exact ttExterior_samePhysicalMetric_iff_newtonResponse
    (screening (lambda4 q)) kappa0 kappaQ G0 GQ x
    hS hkappa0 hkappaQ hkappa0_sq hkappaQ_sq hmode

#print axioms GravityScreening.ttExteriorBlock_mulVec
#print axioms GravityScreening.ttTensor_exteriorCoordinates
#print axioms GravityScreening.ttExteriorBlock_preserves_TT
#print axioms GravityScreening.ttExteriorBlock_normSq
#print axioms GravityScreening.quarticTTExteriorBlock_normSq
#print axioms GravityScreening.ttExterior_samePhysicalMetric_iff_newtonResponse
#print axioms GravityScreening.quarticTTExterior_samePhysicalMetric_iff_newtonResponse

end GravityScreening
