module
public import GravityScreening.ClockHodgeBridge

@[expose] public section

/-!
# Conditional closure of the effective spin-two normalization

This file packages the exact consequence of one explicit physical premise:
the coefficient of the complete sourced Pauli--Fierz action is the normalized,
orientation-even quadratic response of the quartic direction.  Normalization
at zero overlap and vanishing independent geometric information at unit
overlap force that response to be `1-l^2`.

The theorem does not derive the premise that this scalar multiplies the full
physical spin-two action, including its constraint terms.
-/

namespace GravityScreening

/-- A candidate complete spin-two normalization obtained by multiplying a
baseline coefficient by a quadratic response on the background/time plane. -/
noncomputable def fullSpinTwoNormalization
    (baseline a b c l : ℝ) : ℝ :=
  baseline * quadraticSpacetimeScalar a b c 1 l

/-- Linear response of a source to a nonzero scalar kinetic normalization. -/
noncomputable def spinTwoSourceResponse
    (normalization source : ℝ) : ℝ :=
  source / normalization

/-- The normalized, orientation-even, unit-null quadratic premises uniquely
force the complete spin-two normalization to be `baseline * (1-l^2)`. -/
theorem fullSpinTwoNormalization_forced
    (baseline a b c l : ℝ)
    (hbase : quadraticSpacetimeScalar a b c 1 0 = 1)
    (heven : ∀ t : ℝ,
      quadraticSpacetimeScalar a b c 1 t =
        quadraticSpacetimeScalar a b c 1 (-t))
    (hnull : quadraticSpacetimeScalar a b c 1 1 = 0) :
    fullSpinTwoNormalization baseline a b c l =
      screening l * baseline := by
  unfold fullSpinTwoNormalization
  rw [normalized_even_null_quadratic_forced a b c l hbase heven hnull]
  ring

/-- With an independently normalized source, the forced spin-two coefficient
produces the reciprocal screened response. -/
theorem spinTwoSourceResponse_forced
    (baseline source a b c l : ℝ)
    (hbaseline : baseline ≠ 0)
    (hscreen : screening l ≠ 0)
    (hbase : quadraticSpacetimeScalar a b c 1 0 = 1)
    (heven : ∀ t : ℝ,
      quadraticSpacetimeScalar a b c 1 t =
        quadraticSpacetimeScalar a b c 1 (-t))
    (hnull : quadraticSpacetimeScalar a b c 1 1 = 0) :
    spinTwoSourceResponse
        (fullSpinTwoNormalization baseline a b c l) source =
      spinTwoSourceResponse baseline source / screening l := by
  rw [fullSpinTwoNormalization_forced baseline a b c l hbase heven hnull]
  unfold spinTwoSourceResponse
  field_simp [hbaseline, hscreen]

/-- At the quartic residue, the complete forced normalization has the exact
rational coefficient `(2q-1)/q^2`. -/
theorem quartic_fullSpinTwoNormalization_forced
    (q baseline a b c : ℝ)
    (hq : q ≠ 0)
    (hbase : quadraticSpacetimeScalar a b c 1 0 = 1)
    (heven : ∀ t : ℝ,
      quadraticSpacetimeScalar a b c 1 t =
        quadraticSpacetimeScalar a b c 1 (-t))
    (hnull : quadraticSpacetimeScalar a b c 1 1 = 0) :
    fullSpinTwoNormalization baseline a b c (lambda4 q) =
      ((2 * q - 1) / q ^ 2) * baseline := by
  rw [fullSpinTwoNormalization_forced baseline a b c (lambda4 q)
    hbase heven hnull]
  rw [quartic_screening_identity q hq]

/-- For `q>1` and a positive baseline, the quartic-completed spin-two
normalization is positive, so the scalar response introduces no sign flip. -/
theorem quartic_fullSpinTwoNormalization_pos
    (q baseline a b c : ℝ)
    (hq : 1 < q) (hbaseline : 0 < baseline)
    (hbase : quadraticSpacetimeScalar a b c 1 0 = 1)
    (heven : ∀ t : ℝ,
      quadraticSpacetimeScalar a b c 1 t =
        quadraticSpacetimeScalar a b c 1 (-t))
    (hnull : quadraticSpacetimeScalar a b c 1 1 = 0) :
    0 < fullSpinTwoNormalization baseline a b c (lambda4 q) := by
  rw [fullSpinTwoNormalization_forced baseline a b c (lambda4 q)
    hbase heven hnull]
  have hq0 : 0 < q := by linarith
  have hinv0 : 0 < 1 / q := one_div_pos.mpr hq0
  have hinv1 : 1 / q < 1 := by
    rw [div_lt_one hq0]
    exact hq
  have hl0 : 0 < lambda4 q := by
    unfold lambda4
    linarith
  have hl1 : lambda4 q < 1 := by
    unfold lambda4
    linarith
  exact mul_pos (screening_pos ⟨by linarith, hl1⟩) hbaseline

/-- The clock/Hodge completion and the forced full spin-two normalization use
the same quartic coefficient: the Hodge eigenweight product equals the scalar
coefficient multiplying the complete action. -/
theorem clockHodge_to_fullSpinTwo_coefficient
    (q baseline partner a b c : ℝ)
    (hq : 1 < q)
    (hmean : (partner + 1 / q) / 2 = 1)
    (hbase : quadraticSpacetimeScalar a b c 1 0 = 1)
    (heven : ∀ t : ℝ,
      quadraticSpacetimeScalar a b c 1 t =
        quadraticSpacetimeScalar a b c 1 (-t))
    (hnull : quadraticSpacetimeScalar a b c 1 1 = 0) :
    fullSpinTwoNormalization baseline a b c (lambda4 q) =
      (partner * (1 / q)) * baseline := by
  have hq0 : q ≠ 0 := by linarith
  rw [fullSpinTwoNormalization_forced baseline a b c (lambda4 q)
    hbase heven hnull]
  rw [meanPreserving_coreWeight_product q partner hq0 hmean]

#print axioms GravityScreening.fullSpinTwoNormalization_forced
#print axioms GravityScreening.spinTwoSourceResponse_forced
#print axioms GravityScreening.quartic_fullSpinTwoNormalization_forced
#print axioms GravityScreening.quartic_fullSpinTwoNormalization_pos
#print axioms GravityScreening.clockHodge_to_fullSpinTwo_coefficient

end GravityScreening
