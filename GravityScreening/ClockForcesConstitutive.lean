module
public import GravityScreening.TransverseTracelessCount

@[expose] public section

/-!
# The quartic clock weight uniquely fixes the exchange-symmetric constitutive block

An internal two-channel metric is fixed by three structural conditions:
exchange symmetry of the paired channels, unit mean diagonal normalization,
and the retained clock weight `1/q` on the even channel.  The unique result is
the PDT constitutive block with off-diagonal coefficient `-lambda4 q`.
-/

namespace GravityScreening

/-- Exchange the two internal channels. -/
def channelExchange : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 1; 1, 0]

/-- Invariance under interchanging both channel labels. -/
def IsChannelExchangeSymmetric (M : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  channelExchange * M * channelExchange = M

/-- The common diagonal baseline has normalized arithmetic mean one. -/
def HasUnitDiagonalMean (M : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  (M 0 0 + M 1 1) / 2 = 1

/-- The orientation-even vector carries the retained quartic clock weight. -/
def HasEvenCoreWeight (M : Matrix (Fin 2) (Fin 2) ℝ) (q : ℝ) : Prop :=
  M.mulVec ![1, 1] = (1 / q) • ![1, 1]

/-- Exchange symmetry, unit baseline normalization, and the retained weight
`1/q` uniquely force the complete constitutive matrix. -/
theorem clockWeight_forces_constitutiveBlock
    (M : Matrix (Fin 2) (Fin 2) ℝ) (q : ℝ)
    (hexchange : IsChannelExchangeSymmetric M)
    (hmean : HasUnitDiagonalMean M)
    (hcore : HasEvenCoreWeight M q) :
    M = constitutiveBlock (lambda4 q) := by
  have h00 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 0 0)
    hexchange
  have h01 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 0 1)
    hexchange
  have hcore0 := congrFun hcore (0 : Fin 2)
  simp [channelExchange, Matrix.mul_apply, Matrix.vecMul, dotProduct,
    Fin.sum_univ_succ] at h00 h01
  simp [HasUnitDiagonalMean] at hmean
  simp [Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] at hcore0
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [constitutiveBlock, lambda4] <;> linarith

/-- The forced matrix has the quartic screening determinant. -/
theorem clockWeight_forced_constitutive_det
    (M : Matrix (Fin 2) (Fin 2) ℝ) (q : ℝ)
    (hexchange : IsChannelExchangeSymmetric M)
    (hmean : HasUnitDiagonalMean M)
    (hcore : HasEvenCoreWeight M q) :
    Matrix.det M = screening (lambda4 q) := by
  rw [clockWeight_forces_constitutiveBlock M q hexchange hmean hcore]
  exact constitutiveBlock_det (lambda4 q)

/-- For nonzero `q`, the determinant forced by the clock weight has the exact
quartic rational form. -/
theorem clockWeight_forced_quartic_det
    (M : Matrix (Fin 2) (Fin 2) ℝ) (q : ℝ) (hq : q ≠ 0)
    (hexchange : IsChannelExchangeSymmetric M)
    (hmean : HasUnitDiagonalMean M)
    (hcore : HasEvenCoreWeight M q) :
    Matrix.det M = (2 * q - 1) / q ^ 2 := by
  rw [clockWeight_forced_constitutive_det M q hexchange hmean hcore]
  exact quartic_screening_identity q hq

#print axioms GravityScreening.clockWeight_forces_constitutiveBlock
#print axioms GravityScreening.clockWeight_forced_constitutive_det
#print axioms GravityScreening.clockWeight_forced_quartic_det

end GravityScreening
