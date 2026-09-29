module
public import GravityScreening.PauliFierzSymbol

@[expose] public section

/-!
# Lorentz-signature Ward test for the massless spin-two symbol

This file repeats the Pauli--Fierz coefficient derivation directly with the
Minkowski metric `diag(-1,1,1,1)`.  Covariant momentum components are the
inputs; index raising, traces, divergences, and the tensor pairing all carry
the Lorentz signs explicitly.
-/

namespace GravityScreening

/-- Diagonal signs of the Minkowski metric in the chosen frame. -/
def minkowskiSign : FlatIndex → ℝ := ![-1, 1, 1, 1]

/-- Raise a covariant momentum index with `diag(-1,1,1,1)`. -/
def lorentzRaisedMomentum (k : FlatIndex → ℝ) (mu : FlatIndex) : ℝ :=
  minkowskiSign mu * k mu

/-- Lorentzian momentum square `k^mu k_mu`. -/
def lorentzMomentumSq (k : FlatIndex → ℝ) : ℝ :=
  ∑ mu, lorentzRaisedMomentum k mu * k mu

/-- Lorentzian trace `eta^(mu nu) h_(mu nu)` for a covariant tensor. -/
def lorentzTensorTrace (h : Matrix FlatIndex FlatIndex ℝ) : ℝ :=
  ∑ mu, minkowskiSign mu * h mu mu

/-- Lorentzian divergence `k^rho h_(rho nu)`. -/
def lorentzTensorDivergence
    (k : FlatIndex → ℝ) (h : Matrix FlatIndex FlatIndex ℝ)
    (nu : FlatIndex) : ℝ :=
  ∑ rho, lorentzRaisedMomentum k rho * h rho nu

/-- Lorentzian divergence on the second tensor index. -/
def lorentzTensorReverseDivergence
    (k : FlatIndex → ℝ) (h : Matrix FlatIndex FlatIndex ℝ)
    (mu : FlatIndex) : ℝ :=
  ∑ rho, lorentzRaisedMomentum k rho * h mu rho

/-- Lorentzian double divergence `k^mu k^nu h_(mu nu)`. -/
def lorentzTensorDoubleDivergence
    (k : FlatIndex → ℝ) (h : Matrix FlatIndex FlatIndex ℝ) : ℝ :=
  ∑ mu, lorentzRaisedMomentum k mu *
    lorentzTensorReverseDivergence k h mu

/-- Covariant Minkowski metric components in the diagonal frame. -/
def minkowskiMetric (mu nu : FlatIndex) : ℝ :=
  if mu = nu then minkowskiSign mu else 0

/-- Lorentz-signature Fourier symbol of the standard parity-even five-term
local two-derivative operator on a covariant symmetric rank-two field. -/
noncomputable def lorentzPauliFierzSymbol
    (a b c d e : ℝ)
    (k : FlatIndex → ℝ) (h : Matrix FlatIndex FlatIndex ℝ)
    (mu nu : FlatIndex) : ℝ :=
  a * lorentzMomentumSq k * h mu nu +
    (b / 2) *
      (k mu * lorentzTensorDivergence k h nu +
        k nu * lorentzTensorReverseDivergence k h mu) +
    c * k mu * k nu * lorentzTensorTrace h +
    d * minkowskiMetric mu nu * lorentzTensorDoubleDivergence k h +
    e * minkowskiMetric mu nu * lorentzMomentumSq k *
      lorentzTensorTrace h

/-- Raised-index divergence `k^mu E_(mu nu)` of the Lorentzian symbol. -/
noncomputable def lorentzPauliFierzSymbolDivergence
    (a b c d e : ℝ)
    (k : FlatIndex → ℝ) (h : Matrix FlatIndex FlatIndex ℝ)
    (nu : FlatIndex) : ℝ :=
  ∑ mu, lorentzRaisedMomentum k mu *
    lorentzPauliFierzSymbol a b c d e k h mu nu

/-- The Lorentzian symbol divergence has the same three Ward coefficients,
derived here with every signature sign explicit. -/
theorem lorentzPauliFierzSymbolDivergence_decomposition
    (a b c d e : ℝ)
    (k : FlatIndex → ℝ) (h : Matrix FlatIndex FlatIndex ℝ)
    (nu : FlatIndex) :
    lorentzPauliFierzSymbolDivergence a b c d e k h nu =
      (a + b / 2) * lorentzMomentumSq k *
        lorentzTensorDivergence k h nu +
      (b / 2 + d) * k nu * lorentzTensorDoubleDivergence k h +
      (c + e) * k nu * lorentzMomentumSq k *
        lorentzTensorTrace h := by
  classical
  fin_cases nu <;>
    simp [lorentzPauliFierzSymbolDivergence, lorentzPauliFierzSymbol,
      lorentzRaisedMomentum, lorentzMomentumSq, lorentzTensorTrace,
      lorentzTensorDivergence, lorentzTensorReverseDivergence,
      lorentzTensorDoubleDivergence, minkowskiMetric, minkowskiSign,
      Fin.sum_univ_succ] <;>
    ring

/-- Lorentzian Ward identity on all symmetric tensor polarizations. -/
def HasLorentzSpinTwoWardIdentity (a b c d e : ℝ) : Prop :=
  ∀ (k : FlatIndex → ℝ) (h : Matrix FlatIndex FlatIndex ℝ),
    IsSymmetricFlatTensor h →
      ∀ nu, lorentzPauliFierzSymbolDivergence a b c d e k h nu = 0

/-- A tensor with vanishing Lorentz trace and nonzero time-time component. -/
def lorentzTraceFreeTimeTensor : Matrix FlatIndex FlatIndex ℝ :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 0]

theorem lorentzTraceFreeTimeTensor_symmetric :
    IsSymmetricFlatTensor lorentzTraceFreeTimeTensor := by
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The Lorentzian Ward identity itself forces all three divergence
relations.  Three explicit symmetric polarizations at timelike momentum
provide witnesses. -/
theorem lorentzSpinTwoWardIdentity_forces_relations
    (a b c d e : ℝ)
    (hward : HasLorentzSpinTwoWardIdentity a b c d e) :
    a + b / 2 = 0 ∧ b / 2 + d = 0 ∧ c + e = 0 := by
  have hWave := hward timeMomentum mixedTimeSpaceTensor
    mixedTimeSpaceTensor_symmetric (1 : FlatIndex)
  rw [lorentzPauliFierzSymbolDivergence_decomposition] at hWave
  have hWave' : a + b / 2 = 0 := by
    simpa [timeMomentum, mixedTimeSpaceTensor, lorentzRaisedMomentum,
      lorentzMomentumSq, lorentzTensorDivergence,
      lorentzTensorDoubleDivergence, lorentzTensorReverseDivergence,
      lorentzTensorTrace, minkowskiSign, Fin.sum_univ_succ] using hWave
  have hTrace := hward timeMomentum spatialTraceTensor
    spatialTraceTensor_symmetric (0 : FlatIndex)
  rw [lorentzPauliFierzSymbolDivergence_decomposition] at hTrace
  have hTrace' : c + e = 0 := by
    simp [timeMomentum, spatialTraceTensor, lorentzRaisedMomentum,
      lorentzMomentumSq, lorentzTensorDivergence,
      lorentzTensorDoubleDivergence, lorentzTensorReverseDivergence,
      lorentzTensorTrace, minkowskiSign, Fin.sum_univ_succ] at hTrace
    linarith
  have hDouble := hward timeMomentum lorentzTraceFreeTimeTensor
    lorentzTraceFreeTimeTensor_symmetric (0 : FlatIndex)
  rw [lorentzPauliFierzSymbolDivergence_decomposition] at hDouble
  have hDouble' : b / 2 + d = 0 := by
    simp [timeMomentum, lorentzTraceFreeTimeTensor,
      lorentzRaisedMomentum, lorentzMomentumSq,
      lorentzTensorDivergence, lorentzTensorDoubleDivergence,
      lorentzTensorReverseDivergence, lorentzTensorTrace,
      minkowskiSign, Fin.sum_univ_succ] at hDouble
    linarith
  exact ⟨hWave', hDouble', hTrace'⟩

/-- Lorentzian contraction `g^(mu nu) output_(mu nu)`. -/
def lorentzSymbolPairing
    (g output : Matrix FlatIndex FlatIndex ℝ) : ℝ :=
  ∑ mu, ∑ nu,
    minkowskiSign mu * minkowskiSign nu * g mu nu * output mu nu

/-- Formal self-adjointness in the Lorentz tensor pairing. -/
def IsLorentzSpinTwoSymbolSelfAdjoint (a b c d e : ℝ) : Prop :=
  ∀ (k : FlatIndex → ℝ)
      (g h : Matrix FlatIndex FlatIndex ℝ),
    IsSymmetricFlatTensor g → IsSymmetricFlatTensor h →
      lorentzSymbolPairing g (fun mu nu =>
        lorentzPauliFierzSymbol a b c d e k h mu nu) =
      lorentzSymbolPairing h (fun mu nu =>
        lorentzPauliFierzSymbol a b c d e k g mu nu)

/-- Lorentzian self-adjointness forces equality of the two mutually adjoint
trace/divergence coefficients. -/
theorem lorentzSpinTwoSelfAdjoint_forces_traceRelation
    (a b c d e : ℝ)
    (hself : IsLorentzSpinTwoSymbolSelfAdjoint a b c d e) :
    c = d := by
  have h := hself timeMomentum spatialTraceTensor timeTraceTensor
    spatialTraceTensor_symmetric timeTraceTensor_symmetric
  simp [lorentzSymbolPairing, lorentzPauliFierzSymbol, timeMomentum,
    spatialTraceTensor, timeTraceTensor, lorentzRaisedMomentum,
    lorentzMomentumSq, lorentzTensorDivergence,
    lorentzTensorReverseDivergence, lorentzTensorDoubleDivergence,
    lorentzTensorTrace, minkowskiMetric, minkowskiSign,
    Fin.sum_univ_succ] at h
  linarith

/-- Direct Lorentz-signature uniqueness theorem for the standard massless
spin-two symbol. -/
theorem lorentzPauliFierzSymbol_operatorProperties_unique
    (a b c d e : ℝ)
    (hward : HasLorentzSpinTwoWardIdentity a b c d e)
    (hself : IsLorentzSpinTwoSymbolSelfAdjoint a b c d e) :
    b = -2 * a ∧ c = a ∧ d = a ∧ e = -a := by
  obtain ⟨h1, h2, h3⟩ :=
    lorentzSpinTwoWardIdentity_forces_relations a b c d e hward
  have h4 := lorentzSpinTwoSelfAdjoint_forces_traceRelation
    a b c d e hself
  exact pauliFierz_coefficients_unique a b c d e h1 h2 h3 h4

/-- Direct Lorentz-signature quartic specialization. -/
theorem quartic_lorentzSymbolProperties_force_fullNormalization
    (q a b c d e : ℝ) (hq : q ≠ 0)
    (hwave : a = screening (lambda4 q))
    (hward : HasLorentzSpinTwoWardIdentity a b c d e)
    (hself : IsLorentzSpinTwoSymbolSelfAdjoint a b c d e) :
    a = (2 * q - 1) / q ^ 2 ∧
      b = -2 * ((2 * q - 1) / q ^ 2) ∧
      c = (2 * q - 1) / q ^ 2 ∧
      d = (2 * q - 1) / q ^ 2 ∧
      e = -((2 * q - 1) / q ^ 2) := by
  obtain ⟨h1, h2, h3⟩ :=
    lorentzSpinTwoWardIdentity_forces_relations a b c d e hward
  have h4 := lorentzSpinTwoSelfAdjoint_forces_traceRelation
    a b c d e hself
  exact quartic_waveNormalization_forces_fullPauliFierzNormalization
    q a b c d e hq hwave h1 h2 h3 h4

#print axioms GravityScreening.lorentzPauliFierzSymbolDivergence_decomposition
#print axioms GravityScreening.lorentzSpinTwoWardIdentity_forces_relations
#print axioms GravityScreening.lorentzSpinTwoSelfAdjoint_forces_traceRelation
#print axioms GravityScreening.lorentzPauliFierzSymbol_operatorProperties_unique
#print axioms GravityScreening.quartic_lorentzSymbolProperties_force_fullNormalization

end GravityScreening
