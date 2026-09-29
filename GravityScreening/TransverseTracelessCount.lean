module
public import GravityScreening.FirstOrderSourceAction
public import Mathlib.LinearAlgebra.Dimension.Constructions

@[expose] public section

/-!
# Explicit transverse-traceless degree count

For a nonzero spatial momentum chosen along the third axis, a symmetric,
transverse, traceless spatial tensor has exactly two real components.  The
first-order duality pair therefore has a four-dimensional reduced phase space,
or two canonical configuration degrees of freedom.
-/

namespace GravityScreening

abbrev SpatialIndex := Fin 3
abbrev TTCoordinates := Fin 2 → ℝ

/-- The two standard transverse-traceless polarizations for momentum along
the third spatial axis. -/
def ttTensor (plus cross : ℝ) : Matrix SpatialIndex SpatialIndex ℝ :=
  !![plus, cross, 0;
     cross, -plus, 0;
     0, 0, 0]

/-- Symmetric, transverse to the third axis, and traceless. -/
def IsTTAlongZ (h : Matrix SpatialIndex SpatialIndex ℝ) : Prop :=
  (∀ i j, h i j = h j i) ∧
  (∀ j, h 2 j = 0) ∧
  h 0 0 + h 1 1 + h 2 2 = 0

theorem ttTensor_isTT (plus cross : ℝ) :
    IsTTAlongZ (ttTensor plus cross) := by
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> rfl
  constructor
  · intro j
    fin_cases j <;> rfl
  · simp [ttTensor]

/-- The two displayed polarization coordinates exhaust every TT tensor at
fixed momentum along the third axis. -/
theorem ttTensor_complete
    (h : Matrix SpatialIndex SpatialIndex ℝ) (hh : IsTTAlongZ h) :
    h = ttTensor (h 0 0) (h 0 1) := by
  rcases hh with ⟨hsymm, htrans, htrace⟩
  have h20 := htrans (0 : SpatialIndex)
  have h21 := htrans (1 : SpatialIndex)
  have h22 := htrans (2 : SpatialIndex)
  have h02 : h 0 2 = 0 := by rw [hsymm 0 2]; exact h20
  have h12 : h 1 2 = 0 := by rw [hsymm 1 2]; exact h21
  have h10 : h 1 0 = h 0 1 := hsymm 1 0
  have h11 : h 1 1 = -h 0 0 := by linarith
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ttTensor, h20, h21, h22, h02, h12, h10, h11]

/-- The TT conditions form a real linear subspace. -/
def ttSubspace : Submodule ℝ (Matrix SpatialIndex SpatialIndex ℝ) where
  carrier := {h | IsTTAlongZ h}
  zero_mem' := by
    constructor
    · intro i j
      rfl
    constructor
    · intro j
      rfl
    · norm_num
  add_mem' := by
    rintro x y ⟨hsx, htx, hrx⟩ ⟨hsy, hty, hry⟩
    constructor
    · intro i j
      simp [hsx i j, hsy i j]
    constructor
    · intro j
      simp [htx j, hty j]
    · change
        (x 0 0 + y 0 0) + (x 1 1 + y 1 1) +
          (x 2 2 + y 2 2) = 0
      linarith
  smul_mem' := by
    rintro a x ⟨hsx, htx, hrx⟩
    constructor
    · intro i j
      simp [hsx i j]
    constructor
    · intro j
      simp [htx j]
    · change a * x 0 0 + a * x 1 1 + a * x 2 2 = 0
      rw [← mul_add, ← mul_add, hrx, mul_zero]

/-- Read the plus and cross polarization coordinates from a TT tensor. -/
noncomputable def ttToCoordinates : ttSubspace →ₗ[ℝ] TTCoordinates where
  toFun h := ![h.1 0 0, h.1 0 1]
  map_add' := by
    intro x y
    funext i
    fin_cases i <;> rfl
  map_smul' := by
    intro a x
    funext i
    fin_cases i <;> rfl

/-- Build a TT tensor from its plus and cross polarizations. -/
noncomputable def coordinatesToTT : TTCoordinates →ₗ[ℝ] ttSubspace where
  toFun x := ⟨ttTensor (x 0) (x 1), ttTensor_isTT (x 0) (x 1)⟩
  map_add' := by
    intro x y
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ttTensor]
    ring
  map_smul' := by
    intro a x
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ttTensor]

/-- Explicit linear equivalence between the fixed-momentum TT space and two
real polarization coordinates. -/
noncomputable def ttLinearEquiv : ttSubspace ≃ₗ[ℝ] TTCoordinates where
  toLinearMap := ttToCoordinates
  invFun := coordinatesToTT
  left_inv := by
    intro h
    apply Subtype.ext
    exact (ttTensor_complete h.1 h.2).symm
  right_inv := by
    intro x
    funext i
    fin_cases i <;> rfl

theorem ttSubspace_finrank : Module.finrank ℝ ttSubspace = 2 := by
  rw [LinearEquiv.finrank_eq ttLinearEquiv]
  simp [TTCoordinates]

abbrev TTCanonicalPhaseSpace := ttSubspace × ttSubspace

/-- Position and momentum for the two TT polarizations give a four-dimensional
reduced phase space. -/
theorem ttCanonicalPhaseSpace_finrank :
    Module.finrank ℝ TTCanonicalPhaseSpace = 4 := by
  rw [Module.finrank_prod, ttSubspace_finrank]

/-- Half the reduced phase-space dimension is the ordinary two-polarization
configuration-space degree count. -/
theorem ttCanonical_configuration_degree_count :
    Module.finrank ℝ TTCanonicalPhaseSpace / 2 = 2 := by
  rw [ttCanonicalPhaseSpace_finrank]

#print axioms GravityScreening.ttTensor_isTT
#print axioms GravityScreening.ttTensor_complete
#print axioms GravityScreening.ttSubspace_finrank
#print axioms GravityScreening.ttCanonicalPhaseSpace_finrank
#print axioms GravityScreening.ttCanonical_configuration_degree_count

end GravityScreening
