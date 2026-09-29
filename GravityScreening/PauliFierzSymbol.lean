module
public import GravityScreening.PauliFierzUniqueness

@[expose] public section

/-!
# Four-dimensional symbol test for the massless spin-two operator

This file derives the coefficient relations used in
`PauliFierzUniqueness.lean` from operator properties.  It works with the
Fourier symbol of the standard parity-even, local, two-derivative five-term
ansatz on symmetric rank-two fields in four flat dimensions.

The calculation is written with a Euclidean flat metric.  The coefficient
relations are polynomial and unchanged by continuation to a nondegenerate
Lorentzian flat metric; an explicit Lorentz-signature development remains a
separate strengthening.
-/

namespace GravityScreening

abbrev FlatIndex := Fin 4

/-- Euclidean momentum square used by the polynomial symbol calculation. -/
def flatMomentumSq (k : FlatIndex → ℝ) : ℝ :=
  ∑ i, k i * k i

/-- Trace of a rank-two field in the flat frame. -/
def flatTensorTrace (h : Matrix FlatIndex FlatIndex ℝ) : ℝ :=
  ∑ i, h i i

/-- Divergence on the first tensor index. -/
def flatTensorDivergence
    (k : FlatIndex → ℝ) (h : Matrix FlatIndex FlatIndex ℝ)
    (nu : FlatIndex) : ℝ :=
  ∑ rho, k rho * h rho nu

/-- Divergence on the second tensor index. -/
def flatTensorReverseDivergence
    (k : FlatIndex → ℝ) (h : Matrix FlatIndex FlatIndex ℝ)
    (mu : FlatIndex) : ℝ :=
  ∑ rho, k rho * h mu rho

/-- Double divergence of a rank-two field. -/
def flatTensorDoubleDivergence
    (k : FlatIndex → ℝ) (h : Matrix FlatIndex FlatIndex ℝ) : ℝ :=
  ∑ mu, k mu * flatTensorReverseDivergence k h mu

/-- Kronecker delta in the chosen flat frame. -/
def flatDelta (mu nu : FlatIndex) : ℝ :=
  if mu = nu then 1 else 0

/-- Fourier symbol of the standard five-term local two-derivative operator
on a symmetric rank-two field.  Symmetrization in the `b` term has weight
`1/2`. -/
noncomputable def pauliFierzSymbol
    (a b c d e : ℝ)
    (k : FlatIndex → ℝ) (h : Matrix FlatIndex FlatIndex ℝ)
    (mu nu : FlatIndex) : ℝ :=
  a * flatMomentumSq k * h mu nu +
    (b / 2) *
      (k mu * flatTensorDivergence k h nu +
        k nu * flatTensorReverseDivergence k h mu) +
    c * k mu * k nu * flatTensorTrace h +
    d * flatDelta mu nu * flatTensorDoubleDivergence k h +
    e * flatDelta mu nu * flatMomentumSq k * flatTensorTrace h

/-- Momentum divergence of the five-term symbol. -/
noncomputable def pauliFierzSymbolDivergence
    (a b c d e : ℝ)
    (k : FlatIndex → ℝ) (h : Matrix FlatIndex FlatIndex ℝ)
    (nu : FlatIndex) : ℝ :=
  ∑ mu, k mu * pauliFierzSymbol a b c d e k h mu nu

/-- Exact decomposition of the symbol divergence into the three independent
Ward coefficients. -/
theorem pauliFierzSymbolDivergence_decomposition
    (a b c d e : ℝ)
    (k : FlatIndex → ℝ) (h : Matrix FlatIndex FlatIndex ℝ)
    (nu : FlatIndex) :
    pauliFierzSymbolDivergence a b c d e k h nu =
      (a + b / 2) * flatMomentumSq k * flatTensorDivergence k h nu +
      (b / 2 + d) * k nu * flatTensorDoubleDivergence k h +
      (c + e) * k nu * flatMomentumSq k * flatTensorTrace h := by
  classical
  fin_cases nu <;>
    simp [pauliFierzSymbolDivergence, pauliFierzSymbol,
      flatMomentumSq, flatTensorTrace, flatTensorDivergence,
      flatTensorReverseDivergence, flatTensorDoubleDivergence, flatDelta,
      Fin.sum_univ_succ] <;>
    ring

/-- Symmetry predicate for the rank-two test fields. -/
def IsSymmetricFlatTensor (h : Matrix FlatIndex FlatIndex ℝ) : Prop :=
  ∀ i j, h i j = h j i

/-- The Ward identity on all symmetric test fields and momenta. -/
def HasSpinTwoWardIdentity (a b c d e : ℝ) : Prop :=
  ∀ (k : FlatIndex → ℝ) (h : Matrix FlatIndex FlatIndex ℝ),
    IsSymmetricFlatTensor h →
      ∀ nu, pauliFierzSymbolDivergence a b c d e k h nu = 0

def timeMomentum : FlatIndex → ℝ := ![1, 0, 0, 0]

def mixedTimeSpaceTensor : Matrix FlatIndex FlatIndex ℝ :=
  !![0, 1, 0, 0;
     1, 0, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 0]

def traceFreeTimeTensor : Matrix FlatIndex FlatIndex ℝ :=
  !![1,  0, 0, 0;
     0, -1, 0, 0;
     0,  0, 0, 0;
     0,  0, 0, 0]

def spatialTraceTensor : Matrix FlatIndex FlatIndex ℝ :=
  !![0, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 0]

def timeTraceTensor : Matrix FlatIndex FlatIndex ℝ :=
  !![1, 0, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 0]

theorem mixedTimeSpaceTensor_symmetric :
    IsSymmetricFlatTensor mixedTimeSpaceTensor := by
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

theorem traceFreeTimeTensor_symmetric :
    IsSymmetricFlatTensor traceFreeTimeTensor := by
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

theorem spatialTraceTensor_symmetric :
    IsSymmetricFlatTensor spatialTraceTensor := by
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

theorem timeTraceTensor_symmetric :
    IsSymmetricFlatTensor timeTraceTensor := by
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The operator Ward identity forces the three divergence relations.  The
proof uses three explicit symmetric polarization tensors at one nonzero
momentum, so no independence assumption is hidden in the conclusion. -/
theorem spinTwoWardIdentity_forces_relations
    (a b c d e : ℝ)
    (hward : HasSpinTwoWardIdentity a b c d e) :
    a + b / 2 = 0 ∧ b / 2 + d = 0 ∧ c + e = 0 := by
  have hWave := hward timeMomentum mixedTimeSpaceTensor
    mixedTimeSpaceTensor_symmetric (1 : FlatIndex)
  rw [pauliFierzSymbolDivergence_decomposition] at hWave
  have hWave' : a + b / 2 = 0 := by
    simpa [timeMomentum, mixedTimeSpaceTensor, flatMomentumSq,
      flatTensorDivergence, flatTensorDoubleDivergence, flatTensorTrace,
      flatTensorReverseDivergence, Fin.sum_univ_succ] using hWave
  have hTrace := hward timeMomentum spatialTraceTensor
    spatialTraceTensor_symmetric (0 : FlatIndex)
  rw [pauliFierzSymbolDivergence_decomposition] at hTrace
  have hTrace' : c + e = 0 := by
    simpa [timeMomentum, spatialTraceTensor, flatMomentumSq,
      flatTensorDivergence, flatTensorDoubleDivergence, flatTensorTrace,
      flatTensorReverseDivergence, Fin.sum_univ_succ] using hTrace
  have hDouble := hward timeMomentum traceFreeTimeTensor
    traceFreeTimeTensor_symmetric (0 : FlatIndex)
  rw [pauliFierzSymbolDivergence_decomposition] at hDouble
  have hDouble' : b / 2 + d = 0 := by
    simp [timeMomentum, traceFreeTimeTensor, flatMomentumSq,
      flatTensorDivergence, flatTensorDoubleDivergence, flatTensorTrace,
      flatTensorReverseDivergence, Fin.sum_univ_succ] at hDouble
    linarith
  exact ⟨hWave', hDouble', hTrace'⟩

/-- Pairing of one test tensor with the output symbol on another. -/
def flatSymbolPairing
    (g : Matrix FlatIndex FlatIndex ℝ)
    (output : Matrix FlatIndex FlatIndex ℝ) : ℝ :=
  ∑ mu, ∑ nu, g mu nu * output mu nu

/-- Formal self-adjointness of the symbol on symmetric test tensors. -/
def IsSpinTwoSymbolSelfAdjoint (a b c d e : ℝ) : Prop :=
  ∀ (k : FlatIndex → ℝ)
      (g h : Matrix FlatIndex FlatIndex ℝ),
    IsSymmetricFlatTensor g → IsSymmetricFlatTensor h →
      flatSymbolPairing g (fun mu nu =>
        pauliFierzSymbol a b c d e k h mu nu) =
      flatSymbolPairing h (fun mu nu =>
        pauliFierzSymbol a b c d e k g mu nu)

/-- Self-adjointness forces the trace-Hessian and metric-double-divergence
coefficients to agree.  Two explicit diagonal test tensors witness the
otherwise unmatched cross terms. -/
theorem spinTwoSelfAdjoint_forces_traceRelation
    (a b c d e : ℝ)
    (hself : IsSpinTwoSymbolSelfAdjoint a b c d e) :
    c = d := by
  have h := hself timeMomentum spatialTraceTensor timeTraceTensor
    spatialTraceTensor_symmetric timeTraceTensor_symmetric
  simp [flatSymbolPairing, pauliFierzSymbol, timeMomentum,
    spatialTraceTensor, timeTraceTensor, flatMomentumSq,
    flatTensorDivergence, flatTensorReverseDivergence,
    flatTensorDoubleDivergence, flatTensorTrace, flatDelta,
    Fin.sum_univ_succ] at h
  linarith

/-- Direct operator-property version of Pauli--Fierz uniqueness.  Within the
standard five-term ansatz, the Ward identity and self-adjointness force one
overall scale. -/
theorem pauliFierzSymbol_operatorProperties_unique
    (a b c d e : ℝ)
    (hward : HasSpinTwoWardIdentity a b c d e)
    (hself : IsSpinTwoSymbolSelfAdjoint a b c d e) :
    b = -2 * a ∧ c = a ∧ d = a ∧ e = -a := by
  obtain ⟨h1, h2, h3⟩ :=
    spinTwoWardIdentity_forces_relations a b c d e hward
  have h4 := spinTwoSelfAdjoint_forces_traceRelation a b c d e hself
  exact pauliFierz_coefficients_unique a b c d e h1 h2 h3 h4

/-- If the wave coefficient is the Q screening factor, the actual Ward and
self-adjointness properties of the four-dimensional symbol force the complete
quartic Pauli--Fierz normalization. -/
theorem quartic_symbolProperties_force_fullNormalization
    (q a b c d e : ℝ) (hq : q ≠ 0)
    (hwave : a = screening (lambda4 q))
    (hward : HasSpinTwoWardIdentity a b c d e)
    (hself : IsSpinTwoSymbolSelfAdjoint a b c d e) :
    a = (2 * q - 1) / q ^ 2 ∧
      b = -2 * ((2 * q - 1) / q ^ 2) ∧
      c = (2 * q - 1) / q ^ 2 ∧
      d = (2 * q - 1) / q ^ 2 ∧
      e = -((2 * q - 1) / q ^ 2) := by
  obtain ⟨h1, h2, h3⟩ :=
    spinTwoWardIdentity_forces_relations a b c d e hward
  have h4 := spinTwoSelfAdjoint_forces_traceRelation a b c d e hself
  exact quartic_waveNormalization_forces_fullPauliFierzNormalization
    q a b c d e hq hwave h1 h2 h3 h4

#print axioms GravityScreening.pauliFierzSymbolDivergence_decomposition
#print axioms GravityScreening.spinTwoWardIdentity_forces_relations
#print axioms GravityScreening.spinTwoSelfAdjoint_forces_traceRelation
#print axioms GravityScreening.pauliFierzSymbol_operatorProperties_unique
#print axioms GravityScreening.quartic_symbolProperties_force_fullNormalization

end GravityScreening
