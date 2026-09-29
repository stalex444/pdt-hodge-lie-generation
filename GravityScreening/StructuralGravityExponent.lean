module
public import GravityScreening.PdtStabilizer
public import GravityScreening.ConformalGeneratorCount
public import GravityScreening.ConformalResponseAlgebra

@[expose] public section

/-!
# Structural derivation of the gravitational exponent

This file connects the conformal generator count and the general
orbit--stabilizer theorem to the determinant appearing in the PDT
gravitational coupling.  The chain starts with `dim so(4,2) = 15`, then obtains
`224` as `dim sl(15)`, while `209` is the stabilizer dimension for the
surjective action of `sl(15)` on a nonzero vector.  Thus `224 = 15 + 209` is a
dimension decomposition, rather than a numeral inserted into the determinant
formula.
-/

namespace GravityScreening

open Module

/-- The electromagnetic exponent is the dimension of `sl(4)`. -/
theorem electromagneticExponent_eq_finrank_sl_four :
    electromagneticExponent = finrank ℚ (PdtStabilizer.sl 4) := by
  rw [PdtStabilizer.finrank_sl_four]
  rfl

/-- The gravitational exponent is the dimension of `sl(15)`. -/
theorem gravitationalExponent_eq_finrank_sl_fifteen :
    gravitationalExponent = finrank ℚ (PdtStabilizer.sl 15) := by
  symm
  simpa [gravitationalExponent] using
    (PdtStabilizer.finrank_sl (N := 15) (by norm_num))

/-- The complete dimension chain: feed the kernel-computed generator count of
`so(4,2)` into the special-linear dimension. -/
theorem gravitationalExponent_eq_finrank_sl_conformalCount :
    gravitationalExponent =
      finrank ℚ
        (PdtStabilizer.sl (finrank ℝ conformalLieAlgebra)) := by
  rw [finrank_conformalLieAlgebra]
  exact gravitationalExponent_eq_finrank_sl_fifteen

/-- The complementary exponent is the stabilizer dimension in `sl(15)` for
every nonzero vector in the defining 15-dimensional module. -/
theorem gravitationalComplementExponent_eq_finrank_stabilizer
    {v : Fin 15 → ℚ} (hv : v ≠ 0) :
    gravitationalComplementExponent =
      finrank ℚ (PdtStabilizer.stabilizer v) := by
  symm
  simpa [gravitationalComplementExponent] using
    (PdtStabilizer.finrank_stabilizer_fifteen hv)

/-- Orbit--stabilizer supplies the structural split `224 = 15 + 209`. -/
theorem gravitationalExponent_orbit_stabilizer
    {v : Fin 15 → ℚ} (hv : v ≠ 0) :
    finrank ℚ (PdtStabilizer.sl 15) =
      15 + finrank ℚ (PdtStabilizer.stabilizer v) := by
  rw [PdtStabilizer.finrank_stabilizer_fifteen hv]
  simpa using (PdtStabilizer.finrank_sl_eq_add (N := 15) (by norm_num))

/-- The scalar bulk response therefore has determinant `(rho*q)^224`, with
the exponent supplied by the dimension of `sl(15)`. -/
theorem structuralGravitationalBulkResponse_det (rho q : ℝ) :
    Matrix.det
        (scalarResponseMatrix
          (finrank ℚ
            (PdtStabilizer.sl (finrank ℝ conformalLieAlgebra)))
          (rho * q)) =
      (rho * q) ^ gravitationalExponent := by
  rw [scalarResponseMatrix_det]
  rw [← gravitationalExponent_eq_finrank_sl_conformalCount]

/-- The complete inverse-coupling response combines the structurally derived
224-dimensional bulk determinant with the exact quartic screen determinant. -/
theorem structuralQuarticCombinedResponse_det (rho q : ℝ) :
    Matrix.det
          (scalarResponseMatrix
            (finrank ℚ
              (PdtStabilizer.sl (finrank ℝ conformalLieAlgebra)))
            (rho * q)) *
        Matrix.det (constitutiveBlock (lambda4 q)) =
      (rho * q) ^ gravitationalExponent * screening (lambda4 q) := by
  rw [structuralGravitationalBulkResponse_det, constitutiveBlock_det]

/-- One theorem exposes the complete exponent lineage and its screened
determinant consequence. -/
theorem structuralGravityExponentPackage
    {v : Fin 15 → ℚ} (hv : v ≠ 0) (rho q : ℝ) :
    electromagneticExponent = finrank ℝ conformalLieAlgebra ∧
    electromagneticExponent = finrank ℚ (PdtStabilizer.sl 4) ∧
    gravitationalComplementExponent =
      finrank ℚ (PdtStabilizer.stabilizer v) ∧
    gravitationalExponent =
      finrank ℚ
        (PdtStabilizer.sl (finrank ℝ conformalLieAlgebra)) ∧
    finrank ℚ (PdtStabilizer.sl 15) =
      15 + finrank ℚ (PdtStabilizer.stabilizer v) ∧
    Matrix.det
          (scalarResponseMatrix
            (finrank ℚ
              (PdtStabilizer.sl (finrank ℝ conformalLieAlgebra)))
            (rho * q)) *
        Matrix.det (constitutiveBlock (lambda4 q)) =
      (rho * q) ^ gravitationalExponent * screening (lambda4 q) := by
  exact ⟨electromagneticExponent_eq_finrank_conformalLieAlgebra,
    electromagneticExponent_eq_finrank_sl_four,
    gravitationalComplementExponent_eq_finrank_stabilizer hv,
    gravitationalExponent_eq_finrank_sl_conformalCount,
    gravitationalExponent_orbit_stabilizer hv,
    structuralQuarticCombinedResponse_det rho q⟩

#print axioms GravityScreening.gravitationalExponent_eq_finrank_sl_fifteen
#print axioms GravityScreening.gravitationalExponent_eq_finrank_sl_conformalCount
#print axioms GravityScreening.gravitationalComplementExponent_eq_finrank_stabilizer
#print axioms GravityScreening.gravitationalExponent_orbit_stabilizer
#print axioms GravityScreening.structuralQuarticCombinedResponse_det
#print axioms GravityScreening.structuralGravityExponentPackage

end GravityScreening
