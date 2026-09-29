module
public import GravityScreening.LorentzPauliFierzSymbol
public import Mathlib.LinearAlgebra.UnitaryGroup

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# The rotation gauge left by a classical rest observer

In the diagonal Minkowski frame, a Lorentz matrix that fixes the future
unit time vector restricts to an orthogonal transformation of the observer's
three-dimensional rest space.  Its spatial determinant is therefore `+1` or
`-1`; choosing an orientation selects the `SO(3)` component.
-/

namespace GravityScreening

open Matrix

/-- The component function packaged as a square matrix so matrix products
retain their index information during elaboration. -/
def observerMinkowskiForm : Matrix FlatIndex FlatIndex ℝ :=
  minkowskiMetric

/-- A real four-by-four matrix preserves the chosen Minkowski form. -/
def PreservesMinkowski (M : Matrix FlatIndex FlatIndex ℝ) : Prop :=
  M.transpose * observerMinkowskiForm * M = observerMinkowskiForm

/-- The matrix fixes the future unit time vector `e₀`. -/
def FixesRestObserver (M : Matrix FlatIndex FlatIndex ℝ) : Prop :=
  M 0 0 = 1 ∧ M 1 0 = 0 ∧ M 2 0 = 0 ∧ M 3 0 = 0

/-- The three-by-three block acting on the observer's spatial rest frame. -/
def observerSpatialBlock
    (M : Matrix FlatIndex FlatIndex ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => M i.succ j.succ

/-- Extend a spatial three-frame by the identity on the observer's time
axis. -/
noncomputable def restFrameLift
    (R : Matrix (Fin 3) (Fin 3) ℝ) : Matrix FlatIndex FlatIndex ℝ :=
  !![1, 0, 0, 0;
     0, R 0 0, R 0 1, R 0 2;
     0, R 1 0, R 1 1, R 1 2;
     0, R 2 0, R 2 1, R 2 2]

theorem restFrameLift_fixesRestObserver
    (R : Matrix (Fin 3) (Fin 3) ℝ) :
    FixesRestObserver (restFrameLift R) := by
  constructor
  · rfl
  constructor
  · rfl
  constructor <;> rfl

theorem restFrameLift_spatialBlock
    (R : Matrix (Fin 3) (Fin 3) ℝ) :
    observerSpatialBlock (restFrameLift R) = R := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- Lorentz preservation plus a fixed rest observer forces the time row to
be `(1,0,0,0)`, so the transformation has no residual boost component. -/
theorem lorentzFixingRestObserver_timeRow
    (M : Matrix FlatIndex FlatIndex ℝ)
    (hLorentz : PreservesMinkowski M)
    (hObserver : FixesRestObserver M) :
    M 0 0 = 1 ∧ M 0 1 = 0 ∧ M 0 2 = 0 ∧ M 0 3 = 0 := by
  unfold PreservesMinkowski at hLorentz
  rcases hObserver with ⟨h00, h10, h20, h30⟩
  have h01 := congrArg (fun A => A 0 1) hLorentz
  have h02 := congrArg (fun A => A 0 2) hLorentz
  have h03 := congrArg (fun A => A 0 3) hLorentz
  simp [observerMinkowskiForm, Matrix.mul_apply, minkowskiMetric,
    minkowskiSign, Fin.sum_univ_succ, h00, h10, h20, h30] at h01 h02 h03
  exact ⟨h00, h01, h02, h03⟩

/-- The residual action on the rest space is an orthogonal three-frame. -/
theorem lorentzFixingRestObserver_spatialBlock_orthogonal
    (M : Matrix FlatIndex FlatIndex ℝ)
    (hLorentz : PreservesMinkowski M)
    (hObserver : FixesRestObserver M) :
    (observerSpatialBlock M).transpose * observerSpatialBlock M = 1 := by
  have hLorentzEntries := hLorentz
  unfold PreservesMinkowski at hLorentzEntries
  rcases lorentzFixingRestObserver_timeRow M hLorentz hObserver with
    ⟨_, h01, h02, h03⟩
  ext i j
  have h := congrArg (fun A => A i.succ j.succ) hLorentzEntries
  fin_cases i <;> fin_cases j
  all_goals
    simp [observerMinkowskiForm,
      observerSpatialBlock, Matrix.mul_apply,
      minkowskiMetric, minkowskiSign, Fin.sum_univ_succ,
      h01, h02, h03] at h ⊢
    linarith

/-- Conversely, every orthogonal spatial three-frame extends to a Lorentz
matrix fixing the rest observer. -/
theorem restFrameLift_preservesMinkowski
    (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : R.transpose * R = 1) :
    PreservesMinkowski (restFrameLift R) := by
  have h00 := congrArg (fun A => A 0 0) hR
  have h01 := congrArg (fun A => A 0 1) hR
  have h02 := congrArg (fun A => A 0 2) hR
  have h10 := congrArg (fun A => A 1 0) hR
  have h11 := congrArg (fun A => A 1 1) hR
  have h12 := congrArg (fun A => A 1 2) hR
  have h20 := congrArg (fun A => A 2 0) hR
  have h21 := congrArg (fun A => A 2 1) hR
  have h22 := congrArg (fun A => A 2 2) hR
  unfold PreservesMinkowski
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [restFrameLift, observerMinkowskiForm, minkowskiMetric,
      minkowskiSign, Matrix.mul_apply, Matrix.one_apply,
      Fin.sum_univ_succ] at h00 h01 h02 h10 h11 h12 h20 h21 h22 ⊢ <;>
    assumption

/-- A Lorentz matrix fixing the chosen rest observer is exactly the lift of
its spatial block. -/
theorem lorentzFixingRestObserver_eq_restFrameLift
    (M : Matrix FlatIndex FlatIndex ℝ)
    (hLorentz : PreservesMinkowski M)
    (hObserver : FixesRestObserver M) :
    M = restFrameLift (observerSpatialBlock M) := by
  rcases hObserver with ⟨h00, h10, h20, h30⟩
  have hObserver' : FixesRestObserver M := ⟨h00, h10, h20, h30⟩
  rcases lorentzFixingRestObserver_timeRow M hLorentz hObserver' with
    ⟨_, h01, h02, h03⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [restFrameLift, observerSpatialBlock, h00, h10, h20, h30,
      h01, h02, h03]

/-- Exact observer-stabilizer classification: spatial restriction and
identity-on-time lift are inverse, and Lorentz preservation is equivalent to
orthogonality of the spatial block. -/
theorem restFrameLift_preservesMinkowski_iff
    (R : Matrix (Fin 3) (Fin 3) ℝ) :
    PreservesMinkowski (restFrameLift R) ↔ R.transpose * R = 1 := by
  constructor
  · intro h
    simpa [restFrameLift_spatialBlock] using
      lorentzFixingRestObserver_spatialBlock_orthogonal
        (restFrameLift R) h (restFrameLift_fixesRestObserver R)
  · exact restFrameLift_preservesMinkowski R

/-- The matrix stabilizer of the chosen future rest observer. -/
def RestObserverStabilizer :=
  {M : Matrix FlatIndex FlatIndex ℝ //
    PreservesMinkowski M ∧ FixesRestObserver M}

/-- Restrict a rest-observer stabilizer element to the spatial rest frame. -/
noncomputable def restObserverStabilizerToO3
    (M : RestObserverStabilizer) :
    Matrix.orthogonalGroup (Fin 3) ℝ :=
  ⟨observerSpatialBlock M.1,
    (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).2
      (lorentzFixingRestObserver_spatialBlock_orthogonal
        M.1 M.2.1 M.2.2)⟩

/-- Lift an orthogonal spatial frame by the identity on time. -/
noncomputable def o3ToRestObserverStabilizer
    (R : Matrix.orthogonalGroup (Fin 3) ℝ) :
    RestObserverStabilizer :=
  ⟨restFrameLift R.1,
    restFrameLift_preservesMinkowski R.1
      ((Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).1 R.2),
    restFrameLift_fixesRestObserver R.1⟩

/-- Exact classification: the Lorentz stabilizer of a chosen future unit rest
observer is equivalent to the three-dimensional orthogonal group. -/
noncomputable def restObserverStabilizerEquivO3 :
    RestObserverStabilizer ≃ Matrix.orthogonalGroup (Fin 3) ℝ where
  toFun := restObserverStabilizerToO3
  invFun := o3ToRestObserverStabilizer
  left_inv M := by
    apply Subtype.ext
    exact (lorentzFixingRestObserver_eq_restFrameLift
      M.1 M.2.1 M.2.2).symm
  right_inv R := by
    apply Subtype.ext
    exact restFrameLift_spatialBlock R.1

/-- An orthogonal three-frame has one of the two possible orientations. -/
theorem orthogonalThreeFrame_det_eq_one_or_neg_one
    (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : R.transpose * R = 1) :
    Matrix.det R = 1 ∨ Matrix.det R = -1 := by
  have hdet := congrArg Matrix.det hR
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hdet
  rcases sq_eq_one_iff.mp (by simpa [pow_two] using hdet) with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- Consequently, the rest-observer stabilizer has `O(3)` spatial blocks:
their determinants are exactly the two signs. -/
theorem lorentzFixingRestObserver_spatialDet_dichotomy
    (M : Matrix FlatIndex FlatIndex ℝ)
    (hLorentz : PreservesMinkowski M)
    (hObserver : FixesRestObserver M) :
    Matrix.det (observerSpatialBlock M) = 1 ∨
      Matrix.det (observerSpatialBlock M) = -1 :=
  orthogonalThreeFrame_det_eq_one_or_neg_one _
    (lorentzFixingRestObserver_spatialBlock_orthogonal M hLorentz hObserver)

/-- If the apparatus also preserves spatial orientation, the remaining
three-frame is in the `SO(3)` component. -/
theorem orientedLorentzRestFrame_has_SO3_block
    (M : Matrix FlatIndex FlatIndex ℝ)
    (hLorentz : PreservesMinkowski M)
    (hObserver : FixesRestObserver M)
    (hOrientation : 0 < Matrix.det (observerSpatialBlock M)) :
    (observerSpatialBlock M).transpose * observerSpatialBlock M = 1 ∧
      Matrix.det (observerSpatialBlock M) = 1 := by
  have hOrth := lorentzFixingRestObserver_spatialBlock_orthogonal
    M hLorentz hObserver
  refine ⟨hOrth, ?_⟩
  rcases orthogonalThreeFrame_det_eq_one_or_neg_one _ hOrth with h | h
  · exact h
  · linarith

/-- The same conclusion in Mathlib's actual special-orthogonal-group type. -/
theorem orientedLorentzRestFrame_spatialBlock_mem_SO3
    (M : Matrix FlatIndex FlatIndex ℝ)
    (hLorentz : PreservesMinkowski M)
    (hObserver : FixesRestObserver M)
    (hOrientation : 0 < Matrix.det (observerSpatialBlock M)) :
    observerSpatialBlock M ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_specialOrthogonalGroup_iff,
    Matrix.mem_orthogonalGroup_iff']
  exact orientedLorentzRestFrame_has_SO3_block
    M hLorentz hObserver hOrientation

#print axioms GravityScreening.lorentzFixingRestObserver_timeRow
#print axioms GravityScreening.lorentzFixingRestObserver_spatialBlock_orthogonal
#print axioms GravityScreening.restFrameLift_preservesMinkowski_iff
#print axioms GravityScreening.lorentzFixingRestObserver_eq_restFrameLift
#print axioms GravityScreening.restObserverStabilizerEquivO3
#print axioms GravityScreening.orthogonalThreeFrame_det_eq_one_or_neg_one
#print axioms GravityScreening.orientedLorentzRestFrame_has_SO3_block
#print axioms GravityScreening.orientedLorentzRestFrame_spatialBlock_mem_SO3

end GravityScreening
