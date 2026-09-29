module
public import GravityScreening.LQGFluxAreaBridge
public import GravityScreening.JacobsonPlacement
public import GravityScreening.RhoQBoostNormalization
public import GravityScreening.UnifiedCouplingGrammar

@[expose] public section

/-!
# Barbero--Immirzi-independent horizon thermodynamics

Bianchi's quantum-Rindler-horizon calculation uses three local quantities for
one puncture/facet:

* area: `8 * pi * G * hbar * gamma * j`;
* boost energy: `hbar * gamma * j * acceleration`;
* Unruh temperature: `hbar * acceleration / (2 * pi)`.

The common boost/area factor cancels in the Clausius ratio.  The first theorem
below records that cancellation exactly.  It is then joined to the conditional
quartic surface-area response proved in `LQGFluxAreaBridge`.

These are algebraic consequences of the displayed LQG relations.  They do not
assert that the PDT graph sector has already been embedded into the physical
horizon holonomy--flux algebra.
-/

namespace GravityScreening

/-- One LQG facet area in the large-spin convention used in the local
quantum-Rindler-horizon calculation. -/
noncomputable def lqgFacetArea
    (G hbar gamma j : ℝ) : ℝ :=
  8 * Real.pi * G * hbar * gamma * j

/-- Expectation value of one facet's local boost energy. -/
def lqgFacetBoostEnergy
    (hbar gamma j acceleration : ℝ) : ℝ :=
  hbar * gamma * j * acceleration

/-- Local Unruh temperature for a stationary near-horizon observer. -/
noncomputable def localUnruhTemperature
    (hbar acceleration : ℝ) : ℝ :=
  hbar * acceleration / (2 * Real.pi)

/-- Bekenstein--Hawking entropy assigned to a physical horizon area. -/
noncomputable def horizonEntropyFromArea
    (G hbar area : ℝ) : ℝ :=
  area / (4 * G * hbar)

/-- The local Clausius ratio equals the area entropy.  The factors
`gamma * j` appear in both boost energy and physical area and therefore do
not require a selected numerical Barbero--Immirzi value. -/
theorem lqgFacet_clausius_eq_areaEntropy
    (G hbar gamma j acceleration : ℝ)
    (hG : G ≠ 0) (hhbar : hbar ≠ 0) (ha : acceleration ≠ 0) :
    lqgFacetBoostEnergy hbar gamma j acceleration /
        localUnruhTemperature hbar acceleration =
      horizonEntropyFromArea G hbar
        (lqgFacetArea G hbar gamma j) := by
  unfold lqgFacetBoostEnergy localUnruhTemperature
    horizonEntropyFromArea lqgFacetArea
  field_simp [Real.pi_ne_zero]
  ring

/-- At fixed physical area, the facet Clausius entropy is independent of both
the chosen real Immirzi label and the observer acceleration. -/
theorem lqgFacet_fixedArea_entropy_independent
    (G hbar gamma₁ j₁ acceleration₁ gamma₂ j₂ acceleration₂ : ℝ)
    (hG : G ≠ 0) (hhbar : hbar ≠ 0)
    (ha₁ : acceleration₁ ≠ 0) (ha₂ : acceleration₂ ≠ 0)
    (harea :
      lqgFacetArea G hbar gamma₁ j₁ =
        lqgFacetArea G hbar gamma₂ j₂) :
    lqgFacetBoostEnergy hbar gamma₁ j₁ acceleration₁ /
        localUnruhTemperature hbar acceleration₁ =
      lqgFacetBoostEnergy hbar gamma₂ j₂ acceleration₂ /
        localUnruhTemperature hbar acceleration₂ := by
  rw [lqgFacet_clausius_eq_areaEntropy
        G hbar gamma₁ j₁ acceleration₁ hG hhbar ha₁,
      lqgFacet_clausius_eq_areaEntropy
        G hbar gamma₂ j₂ acceleration₂ hG hhbar ha₂,
      harea]

/-! ## BI-free matching of the joint modular boost weight -/

/-- Dimensionless boost weight of a maximally oriented LQG facet in the
linear-simplicity convention. -/
def lqgFacetBoostWeight (gamma j : ℝ) : ℝ :=
  gamma * j

/-- The boost weight can be read from physical facet area.  Once area is the
observable, the separate Immirzi label does not occur. -/
theorem lqgFacetBoostWeight_eq_areaRatio
    (G hbar gamma j : ℝ) (hG : G ≠ 0) (hhbar : hbar ≠ 0) :
    lqgFacetBoostWeight gamma j =
      lqgFacetArea G hbar gamma j /
        (8 * Real.pi * G * hbar) := by
  unfold lqgFacetBoostWeight lqgFacetArea
  field_simp [hG, hhbar, Real.pi_ne_zero]

/-- Physical area required if the LQG facet boost weight is to equal the joint
PDT `rho*q` boost weight in the Bisognano--Wichmann normalization.  This is a
matching target, not an assertion that the LQG area spectrum contains it. -/
noncomputable def matchedRhoQHorizonArea
    (G hbar rho q : ℝ) : ℝ :=
  4 * G * hbar * Real.log (rho * q)

/-- The matched area has exactly the joint PDT boost weight when divided by
the universal local horizon conversion factor. -/
theorem matchedRhoQHorizonArea_ratio
    (G hbar rho q : ℝ) (hG : G ≠ 0) (hhbar : hbar ≠ 0) :
    matchedRhoQHorizonArea G hbar rho q /
        (8 * Real.pi * G * hbar) =
      rhoQBoostWeight rho q := by
  unfold matchedRhoQHorizonArea rhoQBoostWeight
  field_simp [hG, hhbar, Real.pi_ne_zero]
  ring

/-- Exact matching criterion.  A maximally oriented facet carries the joint
PDT boost frequency exactly when its physical area equals the BI-free matched
area above. -/
theorem lqgFacet_matches_rhoQBoost_iff_area
    (G hbar rho q gamma j : ℝ)
    (hG : G ≠ 0) (hhbar : hbar ≠ 0) :
    lqgFacetBoostWeight gamma j = rhoQBoostWeight rho q ↔
      lqgFacetArea G hbar gamma j =
        matchedRhoQHorizonArea G hbar rho q := by
  rw [lqgFacetBoostWeight_eq_areaRatio G hbar gamma j hG hhbar,
    ← matchedRhoQHorizonArea_ratio G hbar rho q hG hhbar]
  have hden : 8 * Real.pi * G * hbar ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hG) hhbar
  exact div_left_inj' hden

/-- A realization on one fixed nonzero magnetic step would determine the
Immirzi label.  Therefore a BI-independent construction must be phrased in
physical-area variables or in a collective horizon sector. -/
theorem singleFacet_rhoQBoostMatch_fixes_immirzi
    (rho q gamma j : ℝ) (hj : j ≠ 0)
    (hmatch : lqgFacetBoostWeight gamma j = rhoQBoostWeight rho q) :
    gamma = rhoQBoostWeight rho q / j := by
  unfold lqgFacetBoostWeight at hmatch
  exact (eq_div_iff hj).2 hmatch

/-- Entropy built from physical area inherits any scalar area response. -/
theorem horizonEntropyFromArea_scale
    (G hbar area s : ℝ) :
    horizonEntropyFromArea G hbar (s * area) =
      s * horizonEntropyFromArea G hbar area := by
  unfold horizonEntropyFromArea
  ring

/-- Conditional quartic horizon-entropy law.  If the clock-classified response
acts on the two tangential frame directions, the physical area and hence the
Bekenstein--Hawking entropy scale by the exact quartic factor.  No Immirzi
parameter occurs in the statement. -/
theorem unorientedClock_forces_horizonEntropyResponse
    (M : Matrix (Fin 2) (Fin 2) ℝ) (q G hbar : ℝ)
    (before₀ before₁ after₀ after₁ : Fin 2 → ℝ)
    (hq : 1 < q)
    (hexchange : IsChannelExchangeSymmetric M)
    (hmean : HasUnitDiagonalMean M)
    (hcore : HasUnorientedCoreWeight M q)
    (hcarrier : IsTangentialFrameResponse
      M before₀ before₁ after₀ after₁) :
    horizonEntropyFromArea G hbar
        (triadSurfaceArea2 after₀ after₁) =
      ((2 * q - 1) / q ^ 2) *
        horizonEntropyFromArea G hbar
          (triadSurfaceArea2 before₀ before₁) := by
  rw [unorientedClock_forces_triadAreaResponse
    M q before₀ before₁ after₀ after₁ hq
      hexchange hmean hcore hcarrier]
  exact horizonEntropyFromArea_scale G hbar
    (triadSurfaceArea2 before₀ before₁) ((2 * q - 1) / q ^ 2)

/-- The determinant, physical area, and horizon entropy all carry the same
quartic response under the named clock and surface-carrier hypotheses. -/
theorem unorientedClock_areaEntropy_capstone
    (M : Matrix (Fin 2) (Fin 2) ℝ) (q G hbar : ℝ)
    (before₀ before₁ after₀ after₁ : Fin 2 → ℝ)
    (hq : 1 < q)
    (hexchange : IsChannelExchangeSymmetric M)
    (hmean : HasUnitDiagonalMean M)
    (hcore : HasUnorientedCoreWeight M q)
    (hcarrier : IsTangentialFrameResponse
      M before₀ before₁ after₀ after₁) :
    Matrix.det M = (2 * q - 1) / q ^ 2 ∧
      triadSurfaceArea2 after₀ after₁ =
        Matrix.det M * triadSurfaceArea2 before₀ before₁ ∧
      horizonEntropyFromArea G hbar
          (triadSurfaceArea2 after₀ after₁) =
        Matrix.det M *
          horizonEntropyFromArea G hbar
            (triadSurfaceArea2 before₀ before₁) := by
  have hdet := unorientedClockWeight_forces_quarticResponse
    M q (by linarith) hexchange hmean hcore
  refine ⟨hdet, ?_, ?_⟩
  · rw [hdet]
    exact unorientedClock_forces_triadAreaResponse
      M q before₀ before₁ after₀ after₁ hq
        hexchange hmean hcore hcarrier
  · rw [hdet]
    exact unorientedClock_forces_horizonEntropyResponse
      M q G hbar before₀ before₁ after₀ after₁ hq
        hexchange hmean hcore hcarrier

/-- Full two-scale capstone.  The `rho * q` scalar response supplies the
224-dimensional bulk determinant, while the clock-classified two-channel
block supplies the separate quartic horizon determinant.  Their product,
divided by the projective boundary factor `pi^4`, is the reciprocal of the
displayed PDT gravitational coupling.  The horizon entropy carries only the
local quartic determinant. -/
theorem rhoQClock_fullGravity_horizonEntropy_capstone
    (M : Matrix (Fin 2) (Fin 2) ℝ) (rho q G hbar : ℝ)
    (before₀ before₁ after₀ after₁ : Fin 2 → ℝ)
    (hrho : rho ≠ 0) (hq : 1 < q)
    (hexchange : IsChannelExchangeSymmetric M)
    (hmean : HasUnitDiagonalMean M)
    (hcore : HasUnorientedCoreWeight M q)
    (hcarrier : IsTangentialFrameResponse
      M before₀ before₁ after₀ after₁) :
    1 / gravitationalCoupling rho q =
        (Matrix.det
            (scalarResponseMatrix gravitationalExponent (rho * q)) *
          Matrix.det M) / Real.pi ^ 4 ∧
      Matrix.det M = (2 * q - 1) / q ^ 2 ∧
      horizonEntropyFromArea G hbar
          (triadSurfaceArea2 after₀ after₁) =
        Matrix.det M *
          horizonEntropyFromArea G hbar
            (triadSurfaceArea2 before₀ before₁) := by
  have hq0 : q ≠ 0 := by linarith
  have hscale : rho * q ≠ 0 := mul_ne_zero hrho hq0
  have hscreenPos : 0 < screening (lambda4 q) := by
    rw [quartic_screening_identity q hq0]
    exact div_pos (by linarith) (sq_pos_of_ne_zero hq0)
  have hscreen : screening (lambda4 q) ≠ 0 := ne_of_gt hscreenPos
  have hdet : Matrix.det M = (2 * q - 1) / q ^ 2 :=
    unorientedClockWeight_forces_quarticResponse
      M q hq0 hexchange hmean hcore
  have hblock : Matrix.det M =
      Matrix.det (constitutiveBlock (lambda4 q)) := by
    rw [hdet, constitutiveBlock_det,
      quartic_screening_identity q hq0]
  refine ⟨?_, hdet, ?_⟩
  · rw [hblock]
    exact gravitationalCoupling_inverse_eq_combinedResponse
      rho q hscale hscreen
  · rw [hdet]
    exact unorientedClock_forces_horizonEntropyResponse
      M q G hbar before₀ before₁ after₀ after₁ hq
        hexchange hmean hcore hcarrier

/-- Jacobson placement capstone.  The finite dilation conserves the combined
exterior-plus-hidden observable while the horizon surface channel scales by
the quartic determinant.  If the former is read as total boost heat and the
latter as the entropy-density response, Jacobson's scalar relation forces the
inverse-screened Newton coupling shown in the final conjunct. -/
theorem unorientedClock_conservedHeat_Jacobson_capstone {n : ℕ}
    (M : Matrix (Fin 2) (Fin 2) ℝ) (q baselineG : ℝ)
    (before₀ before₁ after₀ after₁ : Fin 2 → ℝ)
    (k : Fin n → ℝ) (psi : Fin n → ℂ)
    (hq : 1 < q)
    (hexchange : IsChannelExchangeSymmetric M)
    (hmean : HasUnitDiagonalMean M)
    (hcore : HasUnorientedCoreWeight M q)
    (hcarrier : IsTangentialFrameResponse
      M before₀ before₁ after₀ after₁) :
    exteriorDataExpectation k (quarticErasureDilation q psi) +
        hiddenDataExpectation k (quarticErasureDilation q psi) =
      finiteDiagonalExpectation k psi ∧
    triadSurfaceArea2 after₀ after₁ =
      ((2 * q - 1) / q ^ 2) *
        triadSurfaceArea2 before₀ before₁ ∧
    jacobsonScaledCoupling baselineG 1 (Matrix.det M) =
      baselineG / ((2 * q - 1) / q ^ 2) := by
  have hcap := unorientedClock_surfaceFlux_information_capstone
    M q before₀ before₁ after₀ after₁ k psi hq
      hexchange hmean hcore hcarrier
  have hdet : Matrix.det M = (2 * q - 1) / q ^ 2 := hcap.1
  refine ⟨hcap.2.2.2, ?_, ?_⟩
  · exact unorientedClock_forces_triadAreaResponse
      M q before₀ before₁ after₀ after₁ hq
        hexchange hmean hcore hcarrier
  · rw [hdet]
    exact jacobsonScaledCoupling_entropy_only baselineG
      ((2 * q - 1) / q ^ 2)

#print axioms GravityScreening.lqgFacet_clausius_eq_areaEntropy
#print axioms GravityScreening.lqgFacet_fixedArea_entropy_independent
#print axioms GravityScreening.lqgFacetBoostWeight_eq_areaRatio
#print axioms GravityScreening.matchedRhoQHorizonArea_ratio
#print axioms GravityScreening.lqgFacet_matches_rhoQBoost_iff_area
#print axioms GravityScreening.singleFacet_rhoQBoostMatch_fixes_immirzi
#print axioms GravityScreening.horizonEntropyFromArea_scale
#print axioms GravityScreening.unorientedClock_forces_horizonEntropyResponse
#print axioms GravityScreening.unorientedClock_areaEntropy_capstone
#print axioms GravityScreening.rhoQClock_fullGravity_horizonEntropy_capstone
#print axioms GravityScreening.unorientedClock_conservedHeat_Jacobson_capstone

end GravityScreening
