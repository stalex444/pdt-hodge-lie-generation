module
public import GravityScreening.SymplecticReduction

@[expose] public section

/-!
# Electric-source reduction of the doubled constraint block

This file applies the same two-channel block to a pair of linear constraint
values.  It separates a vanishing magnetic *source equation* from a vanishing
raw partner coordinate.  The distinction is decisive for any proposed
identification of the second channel with a NUT charge.
-/

namespace GravityScreening

/-- Electric component of the doubled constitutive constraint. -/
def electricConstraintResponse
    (l electric magnetic : ℝ) : ℝ :=
  electric - l * magnetic

/-- Magnetic component of the doubled constitutive constraint. -/
def magneticConstraintResponse
    (l electric magnetic : ℝ) : ℝ :=
  magnetic - l * electric

/-- The lapse/shift-multiplier model for an electric source and no magnetic
source.  Requiring this expression to vanish for all two multipliers enforces
the two sourced constraint equations. -/
def sourcedConstraintMultiplierTerm
    (l electric magnetic source electricMultiplier magneticMultiplier : ℝ) : ℝ :=
  electricMultiplier *
      (electricConstraintResponse l electric magnetic - source) +
    magneticMultiplier * magneticConstraintResponse l electric magnetic

/-- Arbitrary electric and magnetic multipliers enforce exactly the two
constitutive constraint equations. -/
theorem constraintMultipliers_force_equations
    (l electric magnetic source : ℝ) :
    (∀ electricMultiplier magneticMultiplier : ℝ,
      sourcedConstraintMultiplierTerm l electric magnetic source
        electricMultiplier magneticMultiplier = 0) ↔
      electricConstraintResponse l electric magnetic = source ∧
        magneticConstraintResponse l electric magnetic = 0 := by
  constructor
  · intro h
    constructor
    · have he := h 1 0
      apply sub_eq_zero.mp
      simpa [sourcedConstraintMultiplierTerm] using he
    · have hm := h 0 1
      simpa [sourcedConstraintMultiplierTerm] using hm
  · rintro ⟨he, hm⟩ electricMultiplier magneticMultiplier
    simp [sourcedConstraintMultiplierTerm, he, hm]

/-- Eliminating the zero-source magnetic equation gives the screened electric
constraint and fixes the partner as a constitutive response. -/
theorem electricSource_constraint_reduction
    (l electric magnetic source : ℝ) :
    (electricConstraintResponse l electric magnetic = source ∧
        magneticConstraintResponse l electric magnetic = 0) ↔
      (screening l * electric = source ∧ magnetic = l * electric) := by
  constructor
  · rintro ⟨he, hm⟩
    have hpartner : magnetic = l * electric := by
      simpa [magneticConstraintResponse, sub_eq_zero] using hm
    constructor
    · rw [← he, hpartner]
      simp [electricConstraintResponse, screening]
      ring
    · exact hpartner
  · rintro ⟨he, hpartner⟩
    constructor
    · rw [hpartner] at ⊢
      calc
        electricConstraintResponse l electric (l * electric) =
            screening l * electric := by
          simp [electricConstraintResponse, screening]
          ring
        _ = source := he
    · simp [magneticConstraintResponse, hpartner]

/-- When the screening coefficient is nonzero, the sourced doubled constraint
system has the unique displayed solution. -/
theorem electricSource_constraint_solution_unique
    (l electric magnetic source : ℝ) (hs : screening l ≠ 0) :
    (electricConstraintResponse l electric magnetic = source ∧
        magneticConstraintResponse l electric magnetic = 0) ↔
      (electric = source / screening l ∧
        magnetic = l * (source / screening l)) := by
  rw [electricSource_constraint_reduction]
  constructor
  · rintro ⟨he, hm⟩
    constructor
    · apply (eq_div_iff hs).2
      simpa [mul_comm] using he
    · rw [hm]
      congr 1
      apply (eq_div_iff hs).2
      simpa [mul_comm] using he
  · rintro ⟨he, hm⟩
    constructor
    · rw [he]
      field_simp [hs]
    · rw [he, hm]

/-- The magnetic source equation remains exactly zero even though the raw
partner coordinate generally responds to the electric source. -/
theorem zero_magnetic_source_preserved
    (l source : ℝ) (_hs : screening l ≠ 0) :
    magneticConstraintResponse l
        (source / screening l)
        (l * (source / screening l)) = 0 := by
  simp [magneticConstraintResponse]

/-- Directly identifying the raw partner coordinate with a magnetic/NUT
charge is incompatible with a nonzero electric source whenever the mixing is
nonzero.  The doubled equations force that raw partner to be nonzero. -/
theorem rawMagneticCoordinate_nonzero
    (l electric magnetic source : ℝ)
    (hl : l ≠ 0) (hsource : source ≠ 0)
    (hequations : electricConstraintResponse l electric magnetic = source ∧
      magneticConstraintResponse l electric magnetic = 0) :
    magnetic ≠ 0 := by
  intro hmagnetic
  have hm := hequations.2
  have helectric : electric = 0 := by
    simp [magneticConstraintResponse, hmagnetic] at hm
    exact hm.resolve_left hl
  have he := hequations.1
  simp [electricConstraintResponse, helectric, hmagnetic] at he
  exact hsource he.symm

/-- Equivalently, imposing a zero raw magnetic coordinate on the mixed
constraint block forces the electric source itself to vanish. -/
theorem zeroRawMagnetic_forces_zeroElectricSource
    (l electric magnetic source : ℝ)
    (hl : l ≠ 0) (hmagnetic : magnetic = 0)
    (hequations : electricConstraintResponse l electric magnetic = source ∧
      magneticConstraintResponse l electric magnetic = 0) :
    source = 0 := by
  by_contra hsource
  exact rawMagneticCoordinate_nonzero l electric magnetic source hl hsource
    hequations hmagnetic

/-- At the quartic residue, the electric constraint carries exactly the PDT
screening coefficient while the zero-source partner is fixed by `lambda4`. -/
theorem quartic_electricSource_constraint_reduction
    (q electric magnetic source : ℝ) (hq : q ≠ 0) :
    (electricConstraintResponse (lambda4 q) electric magnetic = source ∧
        magneticConstraintResponse (lambda4 q) electric magnetic = 0) ↔
      (((2 * q - 1) / q ^ 2) * electric = source ∧
        magnetic = lambda4 q * electric) := by
  rw [electricSource_constraint_reduction]
  rw [quartic_screening_identity q hq]

/-- For the positive quartic regime `q>1`, a nonzero ordinary source cannot
coexist with a vanishing raw second coordinate in the mixed block. -/
theorem quartic_rawMagneticCoordinate_nonzero
    (q electric magnetic source : ℝ)
    (hq : 1 < q) (hsource : source ≠ 0)
    (hequations :
      electricConstraintResponse (lambda4 q) electric magnetic = source ∧
        magneticConstraintResponse (lambda4 q) electric magnetic = 0) :
    magnetic ≠ 0 := by
  have hq0 : 0 < q := by linarith
  have hinv : 1 / q < 1 := by
    rw [div_lt_one hq0]
    exact hq
  have hl : lambda4 q ≠ 0 := by
    unfold lambda4
    linarith
  exact rawMagneticCoordinate_nonzero (lambda4 q) electric magnetic source
    hl hsource hequations

/-! ## Uniform constraint families

The same two-channel calculation applies pointwise to any family of
constraints.  For linearized gravity the family can contain the Hamiltonian
constraint and the three momentum constraints enforced by lapse and shift.
-/

/-- The doubled source reduction is uniform over an arbitrary set of
constraint labels. -/
theorem electricSource_constraintFamily_reduction
    {ι : Type*} (l : ℝ)
    (electric magnetic source : ι → ℝ) :
    (∀ i,
      electricConstraintResponse l (electric i) (magnetic i) = source i ∧
        magneticConstraintResponse l (electric i) (magnetic i) = 0) ↔
      (∀ i,
        screening l * electric i = source i ∧
          magnetic i = l * electric i) := by
  constructor <;> intro h i
  · exact (electricSource_constraint_reduction l
      (electric i) (magnetic i) (source i)).1 (h i)
  · exact (electricSource_constraint_reduction l
      (electric i) (magnetic i) (source i)).2 (h i)

/-- Four labels represent the one Hamiltonian and three momentum constraints
of the linearized lapse/shift sector. -/
abbrev PauliFierzConstraintLabel := Fin 4

/-- Quartic specialization for all four lapse/shift constraint channels at
once.  The result is conditional only on applying the same internal block to
this complete constraint family. -/
theorem quartic_fullPauliFierzConstraint_reduction
    (q : ℝ)
    (electric magnetic source : PauliFierzConstraintLabel → ℝ)
    (hq : q ≠ 0) :
    (∀ i,
      electricConstraintResponse (lambda4 q)
          (electric i) (magnetic i) = source i ∧
        magneticConstraintResponse (lambda4 q)
          (electric i) (magnetic i) = 0) ↔
      (∀ i,
        ((2 * q - 1) / q ^ 2) * electric i = source i ∧
          magnetic i = lambda4 q * electric i) := by
  rw [electricSource_constraintFamily_reduction]
  constructor <;> intro h i
  · have hi := h i
    rwa [quartic_screening_identity q hq] at hi
  · have hi := h i
    rwa [quartic_screening_identity q hq]

#print axioms GravityScreening.electricSource_constraintFamily_reduction
#print axioms GravityScreening.quartic_fullPauliFierzConstraint_reduction

#print axioms GravityScreening.constraintMultipliers_force_equations
#print axioms GravityScreening.electricSource_constraint_reduction
#print axioms GravityScreening.electricSource_constraint_solution_unique
#print axioms GravityScreening.zero_magnetic_source_preserved
#print axioms GravityScreening.rawMagneticCoordinate_nonzero
#print axioms GravityScreening.zeroRawMagnetic_forces_zeroElectricSource
#print axioms GravityScreening.quartic_electricSource_constraint_reduction
#print axioms GravityScreening.quartic_rawMagneticCoordinate_nonzero

end GravityScreening
