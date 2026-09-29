module
public import GravityScreening.InformationToGravityChain
public import GravityScreening.TransverseTracelessCount

@[expose] public section

/-!
# Horizon shear and the Newton-normalization ambiguity

At fixed nonzero momentum, the physical graviton is the two-dimensional
transverse-traceless tensor proved in `TransverseTracelessCount`.  The same two
coordinates describe the two components of a horizon shear.  This file makes
their quadratic norm explicit and proves the precise ambiguity that remains:
the quartic factor can arise either from scaling the shear amplitude by
`sqrt S_Q` at fixed coupling, or from scaling `1/G` by `S_Q` while holding the
same physical shear fixed.
-/

namespace GravityScreening

/-- Frobenius pairing on spatial tensors. -/
def tensorPairing
    (h k : Matrix SpatialIndex SpatialIndex ℝ) : ℝ :=
  ∑ i, ∑ j, h i j * k i j

/-- The two physical shear coordinates carry the Euclidean pairing inherited
from the transverse-traceless tensor, with the conventional factor two. -/
def ttShearPairing
    (plus cross plus' cross' : ℝ) : ℝ :=
  2 * (plus * plus' + cross * cross')

/-- Direct tensor calculation: the Frobenius pairing of two TT tensors is the
two-polarization shear pairing. -/
theorem ttTensor_pairing
    (plus cross plus' cross' : ℝ) :
    tensorPairing (ttTensor plus cross) (ttTensor plus' cross') =
      ttShearPairing plus cross plus' cross' := by
  simp [tensorPairing, ttTensor, ttShearPairing, Fin.sum_univ_succ]
  ring

/-- Squared horizon-shear norm of the two physical polarizations. -/
def ttShearNormSq (plus cross : ℝ) : ℝ :=
  ttShearPairing plus cross plus cross

theorem ttShearNormSq_eq (plus cross : ℝ) :
    ttShearNormSq plus cross = 2 * (plus ^ 2 + cross ^ 2) := by
  simp [ttShearNormSq, ttShearPairing, pow_two]

theorem ttShearNormSq_pos
    (plus cross : ℝ) (hmode : plus ≠ 0 ∨ cross ≠ 0) :
    0 < ttShearNormSq plus cross := by
  rw [ttShearNormSq_eq]
  rcases hmode with hp | hc
  · positivity
  · positivity

/-- Scaling the two shear amplitudes by `d` scales their quadratic norm by
`d^2`. -/
theorem ttShearNormSq_smul (d plus cross : ℝ) :
    ttShearNormSq (d * plus) (d * cross) =
      d ^ 2 * ttShearNormSq plus cross := by
  simp [ttShearNormSq_eq]
  ring

/-- Scalar model of the horizon shear contribution to gravitational canonical
energy.  All universal numerical and geometric factors can be included in
`inverseG`; the point at issue is its multiplicative dependence on `1/G` and
on the two-polarization shear norm. -/
def horizonShearEnergy (inverseG plus cross : ℝ) : ℝ :=
  inverseG * ttShearNormSq plus cross

/-- The quartic coframe/amplitude reading: if `d^2=S_Q`, scaling both physical
shear polarizations by `d` contracts their energy by `S_Q` at fixed coupling. -/
theorem quarticShear_amplitude_contraction
    (q d inverseG plus cross : ℝ)
    (hd : d ^ 2 = screening (lambda4 q)) :
    horizonShearEnergy inverseG (d * plus) (d * cross) =
      screening (lambda4 q) *
        horizonShearEnergy inverseG plus cross := by
  simp [horizonShearEnergy, ttShearNormSq_smul, hd]
  ring

/-- The same contracted shear energy is reproduced by leaving the physical
mode unchanged and scaling the inverse Newton coupling by `S_Q`.  Thus the
shear-squared law alone cannot decide between amplitude loss and coupling
screening. -/
theorem quarticShear_amplitude_coupling_degeneracy
    (q d inverseG plus cross : ℝ)
    (hd : d ^ 2 = screening (lambda4 q)) :
    horizonShearEnergy inverseG (d * plus) (d * cross) =
      horizonShearEnergy
        (screening (lambda4 q) * inverseG) plus cross := by
  rw [quarticShear_amplitude_contraction q d inverseG plus cross hd]
  simp [horizonShearEnergy]
  ring

/-- Once the same nonzero physical shear is fixed independently at the two
endpoints, an `S_Q` contraction of its canonical energy is equivalent to an
`S_Q` contraction of the inverse gravitational coupling. -/
theorem horizonShear_same_mode_iff
    (inverseG0 inverseG1 plus cross s : ℝ)
    (hmode : plus ≠ 0 ∨ cross ≠ 0) :
    horizonShearEnergy inverseG1 plus cross =
        s * horizonShearEnergy inverseG0 plus cross ↔
      inverseG1 = s * inverseG0 := by
  have hnorm : ttShearNormSq plus cross ≠ 0 :=
    ne_of_gt (ttShearNormSq_pos plus cross hmode)
  constructor
  · intro h
    apply mul_right_cancel₀ hnorm
    simpa [horizonShearEnergy, mul_assoc] using h
  · intro h
    simp [horizonShearEnergy, h]
    ring

/-- Conditional local-horizon capstone.  If the same nonzero TT shear mode is
compared before and after the quartic information contraction, the screened
Newton response follows exactly. -/
theorem quarticHorizonShear_forces_newtonResponse
    (q G0 GQ plus cross : ℝ)
    (hq1 : 1 < q) (hG0 : G0 ≠ 0) (hGQ : GQ ≠ 0)
    (hmode : plus ≠ 0 ∨ cross ≠ 0)
    (henergy :
      horizonShearEnergy (1 / GQ) plus cross =
        screening (lambda4 q) *
          horizonShearEnergy (1 / G0) plus cross) :
    GQ = G0 / ((2 * q - 1) / q ^ 2) := by
  have hq0 : q ≠ 0 := by linarith
  have hSpos : 0 < screening (lambda4 q) := by
    rw [quartic_screening_identity q hq0]
    have hnum : 0 < 2 * q - 1 := by linarith
    have hden : 0 < q ^ 2 := by positivity
    exact div_pos hnum hden
  have hS : screening (lambda4 q) ≠ 0 := ne_of_gt hSpos
  have hcoupling :
      1 / GQ = screening (lambda4 q) * (1 / G0) :=
    (horizonShear_same_mode_iff
      (1 / G0) (1 / GQ) plus cross (screening (lambda4 q)) hmode).mp
      henergy
  have hresponse :=
    (inverseCoupling_scale_iff G0 GQ (screening (lambda4 q))
      hG0 hGQ hS).mp hcoupling
  rw [quartic_screening_identity q hq0] at hresponse
  exact hresponse

/-- A nonzero same-mode horizon-shear normalization fixes the wave coefficient.
The spin-two Ward identities and self-adjointness then propagate that one
coefficient to every term of the Pauli--Fierz operator. -/
theorem quarticHorizonShear_forces_fullPauliFierzNormalization
    (q a b c d e plus cross : ℝ) (hq0 : q ≠ 0)
    (hmode : plus ≠ 0 ∨ cross ≠ 0)
    (hwaveEnergy :
      horizonShearEnergy a plus cross =
        screening (lambda4 q) * horizonShearEnergy 1 plus cross)
    (hdivergenceWave : a + b / 2 = 0)
    (hdivergenceDouble : b / 2 + d = 0)
    (hdivergenceTrace : c + e = 0)
    (hselfAdjoint : c = d) :
    a = (2 * q - 1) / q ^ 2 ∧
      b = -2 * ((2 * q - 1) / q ^ 2) ∧
      c = (2 * q - 1) / q ^ 2 ∧
      d = (2 * q - 1) / q ^ 2 ∧
      e = -((2 * q - 1) / q ^ 2) := by
  have hwave : a = screening (lambda4 q) := by
    have h :=
      (horizonShear_same_mode_iff
        1 a plus cross (screening (lambda4 q)) hmode).mp hwaveEnergy
    simpa using h
  exact quartic_waveNormalization_forces_fullPauliFierzNormalization
    q a b c d e hq0 hwave hdivergenceWave hdivergenceDouble
      hdivergenceTrace hselfAdjoint

section CompleteSpinTwo

variable {V W : Type*}
variable [AddCommGroup V] [Module ℝ V]
variable [AddCommGroup W] [Module ℝ W]

/-- The local linear-gravity chain in one theorem.  A same-mode quartic
contraction of one nonzero physical shear fixes the propagating wave
normalization; the Ward identities force the complete Pauli--Fierz
normalization; and the source-free canonical partner reduces the complete
sourced operator to the screened equation. -/
theorem quarticHorizonShear_closes_completeLinearResponse
    (q a b c d e plus cross : ℝ) (hq0 : q ≠ 0)
    (hmode : plus ≠ 0 ∨ cross ≠ 0)
    (hwaveEnergy :
      horizonShearEnergy a plus cross =
        screening (lambda4 q) * horizonShearEnergy 1 plus cross)
    (hdivergenceWave : a + b / 2 = 0)
    (hdivergenceDouble : b / 2 + d = 0)
    (hdivergenceTrace : c + e = 0)
    (hselfAdjoint : c = d)
    (E : V →ₗ[ℝ] W) (field partner : V) (source : W)
    (hequations :
      doubledOperatorElectric (lambda4 q) E field partner = source ∧
        doubledOperatorMagnetic (lambda4 q) E field partner = 0) :
    (a = (2 * q - 1) / q ^ 2 ∧
      b = -2 * ((2 * q - 1) / q ^ 2) ∧
      c = (2 * q - 1) / q ^ 2 ∧
      d = (2 * q - 1) / q ^ 2 ∧
      e = -((2 * q - 1) / q ^ 2)) ∧
      ((2 * q - 1) / q ^ 2) • E field = source ∧
      E partner = lambda4 q • E field := by
  have hcoeff :=
    quarticHorizonShear_forces_fullPauliFierzNormalization
      q a b c d e plus cross hq0 hmode hwaveEnergy hdivergenceWave
        hdivergenceDouble hdivergenceTrace hselfAdjoint
  have hsource :=
    (quartic_doubledLinearOperator_sourceReduction
      q E field partner source hq0).mp hequations
  exact ⟨hcoeff, hsource⟩

end CompleteSpinTwo

#print axioms GravityScreening.ttTensor_pairing
#print axioms GravityScreening.ttShearNormSq_smul
#print axioms GravityScreening.quarticShear_amplitude_contraction
#print axioms GravityScreening.quarticShear_amplitude_coupling_degeneracy
#print axioms GravityScreening.horizonShear_same_mode_iff
#print axioms GravityScreening.quarticHorizonShear_forces_newtonResponse
#print axioms GravityScreening.quarticHorizonShear_forces_fullPauliFierzNormalization
#print axioms GravityScreening.quarticHorizonShear_closes_completeLinearResponse

end GravityScreening
