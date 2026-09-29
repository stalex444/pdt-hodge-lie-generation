module
public import GravityScreening.ClockGravityFactorization
public import GravityScreening.HodgeOrientationGauge
public import GravityScreening.ConservedFlux

@[expose] public section

/-!
# The clock-to-gravity bridge without an orientation choice

The parity-even screening coefficient does not require deciding which exchange
eigenspace is called even.  If an exchange-symmetric two-channel response has
unit mean diagonal and carries the quartic clock weight `1/q` on either of its
two exchange lines, then the response is `constitutiveBlock (lambda4 q)` or
its sign-gauge conjugate `constitutiveBlock (-lambda4 q)`.  Both have exactly
the same determinant and hence the same screened source coefficient.

This weakens the remaining physical placement question.  One must connect the
quartic modular/KMS line to one gravitational exchange channel, but no separate
chirality-sign assignment is needed for parity-even gravity.
-/

namespace GravityScreening

/-- The orientation-odd exchange line carries the retained clock weight. -/
def HasOddCoreWeight (M : Matrix (Fin 2) (Fin 2) ℝ) (q : ℝ) : Prop :=
  M.mulVec oddChannelVector = (1 / q) • oddChannelVector

/-- The clock line occurs in one of the two exchange eigenspaces, without
choosing their orientation label. -/
def HasUnorientedCoreWeight (M : Matrix (Fin 2) (Fin 2) ℝ) (q : ℝ) : Prop :=
  HasEvenCoreWeight M q ∨ HasOddCoreWeight M q

/-- If the clock weight occupies the odd exchange line, symmetry and unit
mean force the sign-flipped constitutive response. -/
theorem oddClockWeight_forces_constitutiveBlock
    (M : Matrix (Fin 2) (Fin 2) ℝ) (q : ℝ)
    (hexchange : IsChannelExchangeSymmetric M)
    (hmean : HasUnitDiagonalMean M)
    (hcore : HasOddCoreWeight M q) :
    M = constitutiveBlock (-lambda4 q) := by
  have h00 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 0 0)
    hexchange
  have h01 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 0 1)
    hexchange
  have hcore0 := congrFun hcore (0 : Fin 2)
  simp [channelExchange, Matrix.mul_apply, Matrix.vecMul, dotProduct,
    Fin.sum_univ_succ] at h00 h01
  simp [HasUnitDiagonalMean] at hmean
  simp [oddChannelVector, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] at hcore0
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [constitutiveBlock, lambda4] <;> linarith

/-- With no orientation label, the response is unique up to the exact Hodge
sign gauge. -/
theorem unorientedClockWeight_forces_response_or_flip
    (M : Matrix (Fin 2) (Fin 2) ℝ) (q : ℝ)
    (hexchange : IsChannelExchangeSymmetric M)
    (hmean : HasUnitDiagonalMean M)
    (hcore : HasUnorientedCoreWeight M q) :
    M = constitutiveBlock (lambda4 q) ∨
      M = constitutiveBlock (-lambda4 q) := by
  rcases hcore with heven | hodd
  · exact Or.inl
      (clockWeight_forces_constitutiveBlock M q hexchange hmean heven)
  · exact Or.inr
      (oddClockWeight_forces_constitutiveBlock M q hexchange hmean hodd)

/-- Both orientation branches force exactly the same screening determinant. -/
theorem unorientedClockWeight_forces_screening
    (M : Matrix (Fin 2) (Fin 2) ℝ) (q : ℝ)
    (hexchange : IsChannelExchangeSymmetric M)
    (hmean : HasUnitDiagonalMean M)
    (hcore : HasUnorientedCoreWeight M q) :
    Matrix.det M = screening (lambda4 q) := by
  rcases unorientedClockWeight_forces_response_or_flip
      M q hexchange hmean hcore with h | h
  · rw [h]
    exact constitutiveBlock_det (lambda4 q)
  · rw [h, constitutiveBlock_det]
    simp [screening]

/-- For nonzero `q`, the unoriented clock placement fixes the same exact
quartic rational response. -/
theorem unorientedClockWeight_forces_quarticResponse
    (M : Matrix (Fin 2) (Fin 2) ℝ) (q : ℝ) (hq : q ≠ 0)
    (hexchange : IsChannelExchangeSymmetric M)
    (hmean : HasUnitDiagonalMean M)
    (hcore : HasUnorientedCoreWeight M q) :
    Matrix.det M = (2 * q - 1) / q ^ 2 := by
  rw [unorientedClockWeight_forces_screening M q hexchange hmean hcore]
  exact quartic_screening_identity q hq

/-- The complete sign-free classification: the clock-containing response is
one of two basis-gauge branches and its determinant is fixed. -/
theorem unorientedClockWeight_classification
    (M : Matrix (Fin 2) (Fin 2) ℝ) (q : ℝ) (hq : q ≠ 0)
    (hexchange : IsChannelExchangeSymmetric M)
    (hmean : HasUnitDiagonalMean M)
    (hcore : HasUnorientedCoreWeight M q) :
    (M = constitutiveBlock (lambda4 q) ∨
      M = constitutiveBlock (-lambda4 q)) ∧
      Matrix.det M = (2 * q - 1) / q ^ 2 :=
  ⟨unorientedClockWeight_forces_response_or_flip M q hexchange hmean hcore,
    unorientedClockWeight_forces_quarticResponse
      M q hq hexchange hmean hcore⟩

/-- Information/gravity capstone in the finite dilation model.  The response
coefficient forced by the unoriented quartic clock is exactly the fraction of
every diagonal observable retained in the exterior branch, while exterior
plus hidden expectation remains equal to the original global expectation. -/
theorem unorientedClock_informationGravity_conservation {n : ℕ}
    (M : Matrix (Fin 2) (Fin 2) ℝ) (q : ℝ)
    (k : Fin n → ℝ) (psi : Fin n → ℂ)
    (hq : 1 < q)
    (hexchange : IsChannelExchangeSymmetric M)
    (hmean : HasUnitDiagonalMean M)
    (hcore : HasUnorientedCoreWeight M q) :
    Matrix.det M = screening (lambda4 q) ∧
      exteriorDataExpectation k (quarticErasureDilation q psi) =
        Matrix.det M * finiteDiagonalExpectation k psi ∧
      exteriorDataExpectation k (quarticErasureDilation q psi) +
          hiddenDataExpectation k (quarticErasureDilation q psi) =
        finiteDiagonalExpectation k psi := by
  have hdet := unorientedClockWeight_forces_screening
    M q hexchange hmean hcore
  refine ⟨hdet, ?_, quarticErasureDilation_total_expectation q k psi hq⟩
  rw [hdet]
  unfold quarticErasureDilation
  exact erasureDilation_exterior_expectation
    (screening (lambda4 q)) k psi (quarticScreening_bounds q hq).1

#print axioms GravityScreening.oddClockWeight_forces_constitutiveBlock
#print axioms GravityScreening.unorientedClockWeight_forces_response_or_flip
#print axioms GravityScreening.unorientedClockWeight_forces_screening
#print axioms GravityScreening.unorientedClockWeight_forces_quarticResponse
#print axioms GravityScreening.unorientedClockWeight_classification
#print axioms GravityScreening.unorientedClock_informationGravity_conservation

end GravityScreening
