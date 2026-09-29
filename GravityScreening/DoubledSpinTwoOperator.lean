module
public import GravityScreening.LorentzPauliFierzSymbol

@[expose] public section

/-!
# Operator-level reduction of the doubled spin-two system

The quartic constitutive block can act on the output of an arbitrary linear
operator.  Eliminating the source-free partner then multiplies the complete
operator equation by `1-l^2`.  No inverse of the operator is used, so the
result applies in the presence of a gauge kernel.
-/

namespace GravityScreening

section DoubledOperator

variable {V W : Type*}
variable [AddCommGroup V] [Module ℝ V]
variable [AddCommGroup W] [Module ℝ W]

/-- Electric equation of the two-channel completion of a linear operator. -/
def doubledOperatorElectric
    (l : ℝ) (E : V →ₗ[ℝ] W) (field partner : V) : W :=
  E field - l • E partner

/-- Source-free partner equation of the two-channel completion. -/
def doubledOperatorMagnetic
    (l : ℝ) (E : V →ₗ[ℝ] W) (field partner : V) : W :=
  E partner - l • E field

/-- Eliminating the source-free partner reduces the complete linear operator,
not merely an individual mode.  The proof never assumes that `E` is
injective or invertible. -/
theorem doubledLinearOperator_sourceReduction
    (l : ℝ) (E : V →ₗ[ℝ] W) (field partner : V) (source : W) :
    (doubledOperatorElectric l E field partner = source ∧
        doubledOperatorMagnetic l E field partner = 0) ↔
      (screening l • E field = source ∧
        E partner = l • E field) := by
  constructor
  · rintro ⟨helectric, hmagnetic⟩
    have hpartner : E partner = l • E field := by
      exact sub_eq_zero.mp hmagnetic
    have hreduce :
        E field - l • (l • E field) = screening l • E field := by
      calc
        E field - l • (l • E field) =
            (1 : ℝ) • E field - (l * l) • E field := by
              simp [smul_smul]
        _ = (1 - l * l) • E field := by rw [sub_smul]
        _ = screening l • E field := by
          congr 1
          simp [screening, pow_two]
    constructor
    · calc
        screening l • E field =
            E field - l • (l • E field) := hreduce.symm
        _ = doubledOperatorElectric l E field partner := by
          rw [doubledOperatorElectric, hpartner]
        _ = source := helectric
    · exact hpartner
  · rintro ⟨helectric, hpartner⟩
    constructor
    · rw [doubledOperatorElectric, hpartner]
      calc
        E field - l • (l • E field) =
            (1 : ℝ) • E field - (l * l) • E field := by
              simp [smul_smul]
        _ = (1 - l * l) • E field := by rw [sub_smul]
        _ = screening l • E field := by
          congr 1
          simp [screening, pow_two]
        _ = source := helectric
    · simp [doubledOperatorMagnetic, hpartner]

/-- Quartic specialization of the complete operator reduction. -/
theorem quartic_doubledLinearOperator_sourceReduction
    (q : ℝ) (E : V →ₗ[ℝ] W) (field partner : V) (source : W)
    (hq : q ≠ 0) :
    (doubledOperatorElectric (lambda4 q) E field partner = source ∧
        doubledOperatorMagnetic (lambda4 q) E field partner = 0) ↔
      (((2 * q - 1) / q ^ 2) • E field = source ∧
        E partner = lambda4 q • E field) := by
  rw [doubledLinearOperator_sourceReduction]
  rw [quartic_screening_identity q hq]

/-- Adding arbitrary elements of the gauge kernel to both fields leaves the
doubled electric equation unchanged. -/
theorem doubledOperatorElectric_gaugeInvariant
    (l : ℝ) (E : V →ₗ[ℝ] W)
    (field partner gaugeField gaugePartner : V)
    (hgaugeField : E gaugeField = 0)
    (hgaugePartner : E gaugePartner = 0) :
    doubledOperatorElectric l E (field + gaugeField)
        (partner + gaugePartner) =
      doubledOperatorElectric l E field partner := by
  simp [doubledOperatorElectric, map_add, hgaugeField, hgaugePartner]

/-- The source-free partner equation has the same gauge invariance. -/
theorem doubledOperatorMagnetic_gaugeInvariant
    (l : ℝ) (E : V →ₗ[ℝ] W)
    (field partner gaugeField gaugePartner : V)
    (hgaugeField : E gaugeField = 0)
    (hgaugePartner : E gaugePartner = 0) :
    doubledOperatorMagnetic l E (field + gaugeField)
        (partner + gaugePartner) =
      doubledOperatorMagnetic l E field partner := by
  simp [doubledOperatorMagnetic, map_add, hgaugeField, hgaugePartner]

/-- If a linear conservation operator annihilates the original field
operator, it also annihilates both completed channels. -/
theorem doubledOperator_preserves_conservation
    {Z : Type*} [AddCommGroup Z] [Module ℝ Z]
    (l : ℝ) (E : V →ₗ[ℝ] W) (D : W →ₗ[ℝ] Z)
    (hconserved : D.comp E = 0)
    (field partner : V) :
    D (doubledOperatorElectric l E field partner) = 0 ∧
      D (doubledOperatorMagnetic l E field partner) = 0 := by
  have hDE : ∀ x, D (E x) = 0 := by
    intro x
    have hx := LinearMap.congr_fun hconserved x
    simpa using hx
  constructor <;>
    simp [doubledOperatorElectric, doubledOperatorMagnetic, hDE]

/-- A conserved source is necessary for the sourced completed equation, just
as it is for the original gauge operator. -/
theorem doubledOperator_source_is_conserved
    {Z : Type*} [AddCommGroup Z] [Module ℝ Z]
    (l : ℝ) (E : V →ₗ[ℝ] W) (D : W →ₗ[ℝ] Z)
    (hconserved : D.comp E = 0)
    (field partner : V) (source : W)
    (hsource : doubledOperatorElectric l E field partner = source) :
    D source = 0 := by
  rw [← hsource]
  exact (doubledOperator_preserves_conservation l E D hconserved
    field partner).1

#print axioms GravityScreening.doubledLinearOperator_sourceReduction
#print axioms GravityScreening.quartic_doubledLinearOperator_sourceReduction
#print axioms GravityScreening.doubledOperatorElectric_gaugeInvariant
#print axioms GravityScreening.doubledOperatorMagnetic_gaugeInvariant
#print axioms GravityScreening.doubledOperator_preserves_conservation
#print axioms GravityScreening.doubledOperator_source_is_conserved

end DoubledOperator

end GravityScreening
