module
public import GravityScreening.TTPrepotentialAction
public import GravityScreening.ElectricSourceFrame
public import GravityScreening.LorentzPauliFierzSymbol
public import GravityScreening.TTHorizonCode

@[expose] public section

/-!
# Constrained and sourced closure of the quartic TT response

This file fixes the two positive triangular-frame scales directly from the
quartic exterior weight.  There is consequently no frame normalization left
to choose.  It then joins four previously separate statements:

* the retained TT prepotential action has coefficient `screening (lambda4 q)`;
* the same coefficient controls all four lapse/shift constraints;
* an ordinary electric stress-energy source remains on the electric source
  ray, although the internal solution has a constitutive partner;
* the physical TT metric is unchanged exactly at the inverse Newton response.

The propagation of the wave coefficient through the complete Pauli--Fierz
operator uses the Lorentz-signature Ward identity and formal self-adjointness.
These operator properties are retained explicitly in the uniqueness statement.
-/

namespace GravityScreening

/-- The positive action-amplitude scale fixed by the quartic retained weight. -/
noncomputable def quarticActionAmplitude (q : ℝ) : ℝ :=
  Real.sqrt (screening (lambda4 q))

/-- The positive lower-triangular frame scale fixed by the action amplitude. -/
noncomputable def quarticSourceFrameAmplitude (q : ℝ) : ℝ :=
  Real.sqrt (quarticActionAmplitude q)

/-- The quartic retained weight is strictly positive throughout `q>1`. -/
theorem quarticScreening_pos (q : ℝ) (hq : 1 < q) :
    0 < screening (lambda4 q) := by
  have hqpos : 0 < q := by linarith
  have hinvpos : 0 < 1 / q := one_div_pos.mpr hqpos
  have hinvlt : 1 / q < 1 := by
    rw [div_lt_one hqpos]
    exact hq
  have hlpos : 0 < lambda4 q := by
    unfold lambda4
    linarith
  have hllt : lambda4 q < 1 := by
    unfold lambda4
    linarith
  exact screening_pos ⟨by linarith, hllt⟩

/-- Squaring the canonical action amplitude returns the exterior weight. -/
theorem quarticActionAmplitude_sq (q : ℝ) (hq : 1 < q) :
    quarticActionAmplitude q ^ 2 = screening (lambda4 q) := by
  exact Real.sq_sqrt (le_of_lt (quarticScreening_pos q hq))

/-- Squaring the canonical source-frame amplitude returns the action
amplitude. -/
theorem quarticSourceFrameAmplitude_sq (q : ℝ) :
    quarticSourceFrameAmplitude q ^ 2 = quarticActionAmplitude q := by
  apply Real.sq_sqrt
  exact Real.sqrt_nonneg _

theorem quarticActionAmplitude_pos (q : ℝ) (hq : 1 < q) :
    0 < quarticActionAmplitude q := by
  exact Real.sqrt_pos.2 (quarticScreening_pos q hq)

theorem quarticSourceFrameAmplitude_pos (q : ℝ) (hq : 1 < q) :
    0 < quarticSourceFrameAmplitude q := by
  exact Real.sqrt_pos.2 (quarticActionAmplitude_pos q hq)

/-- The quartic source frame is now parameter-free: its positive scale is the
fourth root of the retained action weight. -/
noncomputable def quarticElectricSourceFrame (q : ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  electricFrameTransform (lambda4 q) (quarticSourceFrameAmplitude q)

/-- The parameter-free quartic source frame is symplectic. -/
theorem quarticElectricSourceFrame_symplectic (q : ℝ) (hq : 1 < q) :
    (quarticElectricSourceFrame q).transpose * symplecticBlock *
        quarticElectricSourceFrame q = symplecticBlock := by
  exact electricFrameTransform_symplectic
    (lambda4 q) (quarticSourceFrameAmplitude q)
      (ne_of_gt (quarticSourceFrameAmplitude_pos q hq))

/-- The Gram matrix of the parameter-free frame is exactly the normalized
quartic constitutive block. -/
theorem quarticElectricSourceFrame_gram (q : ℝ) (hq : 1 < q) :
    (quarticElectricSourceFrame q).transpose *
        quarticElectricSourceFrame q =
      unimodularConstitutive (lambda4 q) (quarticActionAmplitude q) := by
  exact electricFrameTransform_gram
    (lambda4 q) (quarticActionAmplitude q)
      (quarticSourceFrameAmplitude q)
      (ne_of_gt (quarticSourceFrameAmplitude_pos q hq))
      (quarticSourceFrameAmplitude_sq q)
      (quarticActionAmplitude_sq q hq)
      (ne_of_gt (quarticActionAmplitude_pos q hq))

/-- Pullback through the canonical quartic frame preserves the ordinary
electric source ray exactly.  It changes the magnitude but creates no
magnetic source component. -/
theorem quarticElectricSourceFrame_preserves_source_ray
    (q source : ℝ) :
    (electricFrameInverse (lambda4 q)
        (quarticSourceFrameAmplitude q)).transpose.mulVec
        (electricSourceVector source) =
      electricSourceVector
        (source / quarticSourceFrameAmplitude q) := by
  exact electricFrame_preserves_source_ray
    (lambda4 q) (quarticSourceFrameAmplitude q) source

/-- The unique response obtained by solving in the canonical frame and then
mapping back to the physical electric/magnetic coordinates. -/
noncomputable def quarticConstraintResponse
    (q source : ℝ) : Fin 2 → ℝ :=
  (electricFrameInverse (lambda4 q)
      (quarticSourceFrameAmplitude q)).mulVec
    (canonicalElectricResponse (quarticActionAmplitude q)
      (quarticSourceFrameAmplitude q) source)

/-- The canonical frame gives the exact inverse-screened electric response
and its induced constitutive partner. -/
theorem quarticConstraintResponse_eq
    (q source : ℝ) (hq : 1 < q) :
    quarticConstraintResponse q source =
      ![source / screening (lambda4 q),
        lambda4 q * (source / screening (lambda4 q))] := by
  unfold quarticConstraintResponse
  exact electricFrame_full_source_response
    (lambda4 q) (quarticActionAmplitude q)
      (quarticSourceFrameAmplitude q) source
      (ne_of_gt (quarticSourceFrameAmplitude_pos q hq))
      (quarticSourceFrameAmplitude_sq q)
      (quarticActionAmplitude_sq q hq)

/-- The canonical response satisfies an electric source equation and an
exactly zero magnetic source equation.  Its raw second coordinate is an
induced partner, not an independently supplied source. -/
theorem quarticConstraintResponse_closure
    (q source : ℝ) (hq : 1 < q) :
    electricConstraintResponse (lambda4 q)
        (quarticConstraintResponse q source 0)
        (quarticConstraintResponse q source 1) = source ∧
      magneticConstraintResponse (lambda4 q)
        (quarticConstraintResponse q source 0)
        (quarticConstraintResponse q source 1) = 0 ∧
      quarticConstraintResponse q source 0 =
        source / ((2 * q - 1) / q ^ 2) := by
  simpa [quarticConstraintResponse] using
    quartic_electricFrame_constraint_closure
      q (quarticActionAmplitude q) (quarticSourceFrameAmplitude q) source hq
      (ne_of_gt (quarticSourceFrameAmplitude_pos q hq))
      (quarticSourceFrameAmplitude_sq q)
      (quarticActionAmplitude_sq q hq)
      (ne_of_gt (quarticActionAmplitude_pos q hq))

/-- Apply the same canonical response pointwise to the Hamiltonian constraint
and the three momentum constraints. -/
noncomputable def quarticFullConstraintResponse
    (q : ℝ) (source : PauliFierzConstraintLabel → ℝ) :
    PauliFierzConstraintLabel → Fin 2 → ℝ :=
  fun i => quarticConstraintResponse q (source i)

/-- All four lapse/shift constraints close with the ordinary source fixed,
zero magnetic source equations, and the same inverse quartic response. -/
theorem quarticFullConstraintResponse_closure
    (q : ℝ) (source : PauliFierzConstraintLabel → ℝ) (hq : 1 < q) :
    ∀ i,
      electricConstraintResponse (lambda4 q)
          (quarticFullConstraintResponse q source i 0)
          (quarticFullConstraintResponse q source i 1) = source i ∧
        magneticConstraintResponse (lambda4 q)
          (quarticFullConstraintResponse q source i 0)
          (quarticFullConstraintResponse q source i 1) = 0 ∧
        quarticFullConstraintResponse q source i 0 =
          source i / ((2 * q - 1) / q ^ 2) := by
  intro i
  exact quarticConstraintResponse_closure q (source i) hq

/-- The four-constraint solution is unique whenever `q>1`.  This rules out an
additional independent response hidden in the lapse/shift sector. -/
theorem quarticFullConstraint_solution_unique
    (q : ℝ)
    (electric magnetic source : PauliFierzConstraintLabel → ℝ)
    (hq : 1 < q) :
    (∀ i,
      electricConstraintResponse (lambda4 q)
          (electric i) (magnetic i) = source i ∧
        magneticConstraintResponse (lambda4 q)
          (electric i) (magnetic i) = 0) ↔
      (∀ i,
        electric i = source i / ((2 * q - 1) / q ^ 2) ∧
          magnetic i = lambda4 q *
            (source i / ((2 * q - 1) / q ^ 2))) := by
  have hq0 : q ≠ 0 := by linarith
  have hs0 : screening (lambda4 q) ≠ 0 :=
    ne_of_gt (quarticScreening_pos q hq)
  constructor <;> intro h i
  · have hi := (electricSource_constraint_solution_unique
      (lambda4 q) (electric i) (magnetic i) (source i) hs0).1 (h i)
    rwa [quartic_screening_identity q hq0] at hi
  · have hi := h i
    rw [← quartic_screening_identity q hq0] at hi
    exact (electricSource_constraint_solution_unique
      (lambda4 q) (electric i) (magnetic i) (source i) hs0).2 hi

/-- The actual Lorentz-signature Ward identity and formal self-adjointness
force every admissible five-term, local, two-derivative massless spin-two
symbol with quartic wave coefficient to have the full quartic Pauli--Fierz
coefficient pattern. -/
theorem quarticLorentzPauliFierzNormalization_unique
    (q : ℝ) (hq : 1 < q) :
    ∀ b c d e : ℝ,
      HasLorentzSpinTwoWardIdentity
          (screening (lambda4 q)) b c d e →
        IsLorentzSpinTwoSymbolSelfAdjoint
          (screening (lambda4 q)) b c d e →
        b = -2 * ((2 * q - 1) / q ^ 2) ∧
          c = (2 * q - 1) / q ^ 2 ∧
          d = (2 * q - 1) / q ^ 2 ∧
          e = -((2 * q - 1) / q ^ 2) := by
  intro b c d e hward hself
  have hq0 : q ≠ 0 := by linarith
  have hfull := quartic_lorentzSymbolProperties_force_fullNormalization
    q (screening (lambda4 q)) b c d e hq0 rfl hward hself
  exact ⟨hfull.2.1, hfull.2.2.1, hfull.2.2.2.1, hfull.2.2.2.2⟩

/-- Linearized constrained-source capstone.  The quartic dilation preserves
the full visible-hidden TT action, scales the exterior TT action by the exact
quartic coefficient, fixes the complete Pauli--Fierz coefficient pattern
through the standard Ward/self-adjointness relations, closes all four sourced
constraints, leaves two graviton configuration degrees of freedom, and gives
the inverse Newton response as the exact condition for an unchanged physical
TT metric. -/
theorem quarticConstrainedSourcedTT_capstone
    (q k kappa0 kappaQ G0 GQ : ℝ)
    (H Hdot : TTPrepotentialMode)
    (source : PauliFierzConstraintLabel → ℝ) (x : TTCoordinates)
    (hq : 1 < q)
    (hkappa0 : 0 ≤ kappa0) (hkappaQ : 0 ≤ kappaQ)
    (hkappa0_sq : kappa0 ^ 2 = 32 * Real.pi * G0)
    (hkappaQ_sq : kappaQ ^ 2 = 32 * Real.pi * GQ)
    (hmode : x 0 ≠ 0 ∨ x 1 ≠ 0) :
    ((dilatedTTPrepotentialLagrangian k
          (dilateTTPrepotentialMode (screening (lambda4 q)) H)
          (dilateTTPrepotentialMode (screening (lambda4 q)) Hdot) =
        ttPrepotentialLagrangian k H Hdot) ∧
      (exteriorTTPrepotentialLagrangian k
          (dilateTTPrepotentialMode (screening (lambda4 q)) H)
          (dilateTTPrepotentialMode (screening (lambda4 q)) Hdot) =
        ((2 * q - 1) / q ^ 2) *
          ttPrepotentialLagrangian k H Hdot)) ∧
    (∀ b c d e : ℝ,
      HasLorentzSpinTwoWardIdentity
          (screening (lambda4 q)) b c d e →
        IsLorentzSpinTwoSymbolSelfAdjoint
          (screening (lambda4 q)) b c d e →
        b = -2 * ((2 * q - 1) / q ^ 2) ∧
          c = (2 * q - 1) / q ^ 2 ∧
          d = (2 * q - 1) / q ^ 2 ∧
          e = -((2 * q - 1) / q ^ 2)) ∧
    (∀ i,
      electricConstraintResponse (lambda4 q)
          (quarticFullConstraintResponse q source i 0)
          (quarticFullConstraintResponse q source i 1) = source i ∧
        magneticConstraintResponse (lambda4 q)
          (quarticFullConstraintResponse q source i 0)
          (quarticFullConstraintResponse q source i 1) = 0 ∧
        quarticFullConstraintResponse q source i 0 =
          source i / ((2 * q - 1) / q ^ 2)) ∧
    (Module.finrank ℝ TTCanonicalPhaseSpace / 2 = 2) ∧
    (physicalTTTensor kappaQ
          (ttHorizonCodeExteriorDecode (screening (lambda4 q)) x) =
        physicalTTTensor kappa0 x ↔
      GQ = G0 / ((2 * q - 1) / q ^ 2)) := by
  constructor
  · exact quarticDilatedTTPrepotential_global_and_exterior q k H Hdot hq
  constructor
  · exact quarticLorentzPauliFierzNormalization_unique q hq
  constructor
  · exact quarticFullConstraintResponse_closure q source hq
  constructor
  · exact ttCanonical_configuration_degree_count
  · exact quarticTTHorizonCode_samePhysicalMetric_iff_newtonResponse
      q kappa0 kappaQ G0 GQ x hq hkappa0 hkappaQ
        hkappa0_sq hkappaQ_sq hmode

#print axioms GravityScreening.quarticScreening_pos
#print axioms GravityScreening.quarticActionAmplitude_sq
#print axioms GravityScreening.quarticSourceFrameAmplitude_sq
#print axioms GravityScreening.quarticElectricSourceFrame_symplectic
#print axioms GravityScreening.quarticElectricSourceFrame_gram
#print axioms GravityScreening.quarticElectricSourceFrame_preserves_source_ray
#print axioms GravityScreening.quarticConstraintResponse_eq
#print axioms GravityScreening.quarticConstraintResponse_closure
#print axioms GravityScreening.quarticFullConstraintResponse_closure
#print axioms GravityScreening.quarticFullConstraint_solution_unique
#print axioms GravityScreening.quarticLorentzPauliFierzNormalization_unique
#print axioms GravityScreening.quarticConstrainedSourcedTT_capstone

end GravityScreening
