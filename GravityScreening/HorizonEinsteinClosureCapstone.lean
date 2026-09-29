module
public import GravityScreening.LocalEinsteinClosure
public import GravityScreening.HodgeBulkScreen

@[expose] public section

/-!
# Integrated horizon-to-Einstein capstone

This file joins the principal parts of the construction in one theorem: the
separate Hodge products for the rho Q bulk divide and quartic screen,
classification from an assumed quartic KMS/core boundary line, exact
null-ray/optical identities, and pointwise null-cone closure to the Einstein
tensor with the determinant identity for the defined dimensionless rho Q
coupling.  The same defined scalar is used in the horizon residual and Einstein
coefficient.  The physical placement, initial horizon residual, and local
null Clausius relation remain explicit hypotheses.
-/

namespace GravityScreening

/-- Integrated conditional PDT horizon-to-Einstein closure.  Exchange
symmetry, unit normalization, and an assumed unoriented quartic KMS/core line
classify the affine screen flow and its quadratic shear/area response.  The
positive-orientation branch has an explicit null-ray realization and satisfies
the scalar Raychaudhuri-form identity; both orientations have the same scalar
determinant and shear square.  The horizon balance is conditional.  If the local
null Clausius contraction holds with the defined dimensionless rho Q
coupling in electron-mass natural units, null-cone
rigidity produces the Einstein-tensor form and the exact determinant identity
is retained. -/
theorem horizonEinsteinClosure_capstone
    (M : Matrix (Fin 2) (Fin 2) ℝ)
    (ricci stress : Matrix (Fin 4) (Fin 4) ℝ)
    (rho q u charge K area : ℝ)
    (screenLabel : Fin 2 → ℝ)
    (hrho3 : rho ^ 3 = rho + 1) (hrho1 : 1 < rho)
    (hq4 : q ^ 4 = q + 1) (hq1 : 1 < q)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hexchange : IsChannelExchangeSymmetric M)
    (hmean : HasUnitDiagonalMean M)
    (hcore : HasUnorientedCoreWeight M q)
    (hconstraint :
      horizonConstraintResidual charge K
        (1 / gravitationalCoupling rho q) area = 0)
    (hricci : ricci.transpose = ricci)
    (hstress : stress.transpose = stress)
    (hnull : ∀ v : Fin 4 → ℝ,
      localMinkowskiSq v = 0 →
        localQuadraticContraction
          (ricci - (8 * Real.pi * gravitationalCoupling rho q) • stress)
          v = 0) :
    ((∀ t, affineScreenFlow M t =
        perronOpticalJacobi (lambda4 q) t) ∨
      (∀ t, affineScreenFlow M t =
        perronOpticalJacobi (-lambda4 q) t)) ∧
      Matrix.det M = screening (lambda4 q) ∧
      lambda4 q = quarticBiResidualCoefficient q ∧
      unitBoostWeightedInitialShearFlux (lambda4 q) = lambda4 q ^ 2 ∧
      unitBoostWeightedInitialShearFlux (lambda4 q) = 1 - Matrix.det M ∧
      doubleNullMinkowskiSq
          (perronNullTangent (lambda4 q) screenLabel) = 0 ∧
      (perronNullGeodesic (lambda4 q) screenLabel u 2 =
          (perronOpticalJacobi (lambda4 q) u).mulVec screenLabel 0 ∧
        perronNullGeodesic (lambda4 q) screenLabel u 3 =
          (perronOpticalJacobi (lambda4 q) u).mulVec screenLabel 1) ∧
      HasDerivAt (perronOpticalExpansion (lambda4 q))
        (perronOpticalExpansionRate (lambda4 q) u) u ∧
      perronOpticalExpansionRate (lambda4 q) u =
        -(perronOpticalExpansion (lambda4 q) u) ^ 2 / 2 -
          perronOpticalShearSq (lambda4 q) u ∧
      horizonConstraintResidual charge
          (K + perronOpticalModularEnergyIncrement
            (1 / gravitationalCoupling rho q) area (lambda4 q))
          (1 / gravitationalCoupling rho q)
          (Matrix.det M * area) = 0 ∧
      (hodgeDivide rho q * hodgeDivideFlip rho q =
          ((rho * q : ℝ) : ℂ) •
            (1 : Matrix HodgeSide HodgeSide ℂ) ∧
        hodgeResponse (lambda4 q) * hodgeResponseFlip (lambda4 q) =
          ((((2 * q - 1) / q ^ 2 : ℝ)) : ℂ) •
            (1 : Matrix HodgeSide HodgeSide ℂ)) ∧
      Irrational (Real.log rho / Real.log q) ∧
      (∃ cosmological : ℝ,
        ricci - (localMinkowskiTrace ricci / 2) • localMinkowskiMetric +
            cosmological • localMinkowskiMetric =
          (8 * Real.pi * gravitationalCoupling rho q) • stress) ∧
      1 / gravitationalCoupling rho q =
        (Matrix.det
            (scalarResponseMatrix gravitationalExponent (rho * q)) *
          Matrix.det (perronCompressedConstitutiveBlock q)) /
          Real.pi ^ 4 := by
  have hrho0 : rho ≠ 0 := by linarith
  have hq0 : q ≠ 0 := by linarith
  have hscale : rho * q ≠ 0 := mul_ne_zero hrho0 hq0
  have hscreen0 : screening (lambda4 q) ≠ 0 :=
    ne_of_gt (quarticScreening_pos q hq1)
  have hcoupling : gravitationalCoupling rho q ≠ 0 := by
    unfold gravitationalCoupling
    exact div_ne_zero (pow_ne_zero _ Real.pi_ne_zero)
      (mul_ne_zero (pow_ne_zero _ hscale) hscreen0)
  have hinverseG : 1 / gravitationalCoupling rho q ≠ 0 :=
    one_div_ne_zero hcoupling
  rcases quarticKMSOpticalBoundarySelection_capstone
      M q charge K (1 / gravitationalCoupling rho q) area hq4 hq1
      hinverseG hexchange hmean hcore
      hconstraint with
    ⟨hflow, hdet, hresidual, _hdetpos, hflux, hfluxdet,
      _hzeroExpansion, hbalance⟩
  have hray := quarticPerronOptical_Raychaudhuri_on_unitInterval
    q u hq1 hu0 hu1
  have hhodge := hodgeBulkAndQuarticScreen rho q hq0
  rcases pdtNullClausius_forces_localEinsteinShape
      ricci stress rho q hrho3 hrho1 hq4 hq1 hricci hstress hnull with
    ⟨hclock, heinstein, hcoupling⟩
  exact ⟨hflow, hdet, hresidual, hflux, hfluxdet,
    perronNullTangent_isNull (lambda4 q) screenLabel,
    perronNullGeodesic_screen_eq_Jacobi (lambda4 q) screenLabel u,
    hray.1, hray.2, hbalance, hhodge, hclock, heinstein, hcoupling⟩

#print axioms GravityScreening.horizonEinsteinClosure_capstone

end GravityScreening
