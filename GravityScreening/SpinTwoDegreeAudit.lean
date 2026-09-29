module
public import GravityScreening.DoubledSpinTwoAction

@[expose] public section

/-!
# Channel and degree audit for the doubled quadratic action

The symmetric two-field action diagonalizes into even and odd field
combinations.  The source coupled to the original field couples to both
diagonal combinations.  These identities expose the extra-mode question that
must be resolved before the partner can be interpreted as a dual description
of one graviton rather than a second massless spin-two field.
-/

namespace GravityScreening

section ChannelAudit

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Orientation-even field combination. -/
def evenChannel (field partner : V) : V := field + partner

/-- Orientation-odd field combination. -/
def oddChannel (field partner : V) : V := field - partner

/-- The original field is recovered from the two channel combinations. -/
theorem field_eq_half_even_add_odd (field partner : V) :
    field = (1 / 2 : ℝ) •
      (evenChannel field partner + oddChannel field partner) := by
  simp [evenChannel, oddChannel]
  rw [← add_smul]
  norm_num

/-- The partner field is recovered from the two channel combinations. -/
theorem partner_eq_half_even_sub_odd (field partner : V) :
    partner = (1 / 2 : ℝ) •
      (evenChannel field partner - oddChannel field partner) := by
  simp [evenChannel, oddChannel]
  rw [← add_smul]
  norm_num

/-- Exact diagonalization of the doubled source-free quadratic form. -/
theorem doubledQuadraticEnergy_channel_decomposition
    (l : ℝ) (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsymm : ∀ x y, B x y = B y x)
    (field partner : V) :
    4 * doubledQuadraticEnergy l B field partner =
      (1 - l) * B (evenChannel field partner) (evenChannel field partner) +
      (1 + l) * B (oddChannel field partner) (oddChannel field partner) := by
  unfold doubledQuadraticEnergy evenChannel oddChannel
  simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply]
  rw [hsymm partner field]
  ring

/-- A source coupled to the original field splits equally between the even
and odd channel variables. -/
theorem source_couples_to_both_channels
    (J : V →ₗ[ℝ] ℝ) (field partner : V) :
    J field = (1 / 2 : ℝ) *
      (J (evenChannel field partner) + J (oddChannel field partner)) := by
  simp [evenChannel, oddChannel]
  ring

/-- Exact channel form of the complete doubled action. -/
theorem doubledQuadraticAction_channel_decomposition
    (l : ℝ) (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (J : V →ₗ[ℝ] ℝ)
    (hsymm : ∀ x y, B x y = B y x)
    (field partner : V) :
    4 * doubledQuadraticAction l B J field partner =
      (1 - l) * B (evenChannel field partner) (evenChannel field partner) +
      (1 + l) * B (oddChannel field partner) (oddChannel field partner) -
      2 * (J (evenChannel field partner) + J (oddChannel field partner)) := by
  unfold doubledQuadraticAction
  rw [mul_sub]
  rw [doubledQuadraticEnergy_channel_decomposition l B hsymm]
  rw [source_couples_to_both_channels J field partner]
  ring

/-- At the quartic coupling, the two diagonal channel weights are the core
weight `1/q` and its mean-preserving partner `2-1/q`. -/
theorem quartic_channel_weights (q : ℝ) :
    1 - lambda4 q = 1 / q ∧
      1 + lambda4 q = 2 - 1 / q := by
  unfold lambda4
  constructor <;> ring

#print axioms GravityScreening.field_eq_half_even_add_odd
#print axioms GravityScreening.partner_eq_half_even_sub_odd
#print axioms GravityScreening.doubledQuadraticEnergy_channel_decomposition
#print axioms GravityScreening.source_couples_to_both_channels
#print axioms GravityScreening.doubledQuadraticAction_channel_decomposition
#print axioms GravityScreening.quartic_channel_weights

end ChannelAudit

end GravityScreening
