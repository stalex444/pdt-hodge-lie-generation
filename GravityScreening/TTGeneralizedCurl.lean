module
public import GravityScreening.TTHorizonCode

@[expose] public section

/-!
# Generalized curl on a transverse-traceless Fourier mode

Barnich--Troessaert's duality-symmetric spin-two action uses the generalized
curl

`(O h)_{mn} = (1/2) (epsilon_{mpq} partial^p h^q_n
                         + epsilon_{npq} partial^p h^q_m)`.

For a Fourier mode whose spatial momentum points along the third axis, this
file evaluates that differential symbol on the complete complexified TT
subspace.  It is `i k` times the plus/cross quarter-turn, and its square is
`k^2 I = -Delta`.  The scalar exterior response selected by the quartic
erasure channel commutes with this kinetic symbol exactly.

The result establishes operator compatibility on the physical polarization
space.  Identifying the quartic erasure data with the graviton prepotential
mode remains a physics premise.
-/

namespace GravityScreening

abbrev ComplexTTCoordinates := Fin 2 → ℂ

/-- Complexification of the standard plus/cross TT tensor for momentum along
the third spatial axis. -/
def complexTTTensor (plus cross : ℂ) :
    Matrix SpatialIndex SpatialIndex ℂ :=
  !![plus, cross, 0;
     cross, -plus, 0;
     0, 0, 0]

/-- A complexified plus/cross tensor remains symmetric. -/
theorem complexTTTensor_transpose (plus cross : ℂ) :
    (complexTTTensor plus cross).transpose =
      complexTTTensor plus cross := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- Fourier symbol of the ordinary vector curl for momentum `(0,0,k)`, with
the convention `partial_z -> i k`. -/
noncomputable def zFourierCurlSymbol (k : ℝ) :
    Matrix SpatialIndex SpatialIndex ℂ :=
  !![0, -(Complex.I * (k : ℂ)), 0;
     Complex.I * (k : ℂ), 0, 0;
     0, 0, 0]

/-- The symmetrized generalized spin-two curl used in the prepotential
formulation of linearized gravity. -/
noncomputable def spinTwoGeneralizedCurlZ (k : ℝ)
    (h : Matrix SpatialIndex SpatialIndex ℂ) :
    Matrix SpatialIndex SpatialIndex ℂ :=
  (1 / 2 : ℂ) •
    (zFourierCurlSymbol k * h +
      (zFourierCurlSymbol k * h).transpose)

/-- Coordinate action of the generalized curl on plus/cross amplitudes. -/
noncomputable def complexTTCurlCoordinates (k : ℝ)
    (x : ComplexTTCoordinates) : ComplexTTCoordinates :=
  ![-(Complex.I * (k : ℂ)) * x 1,
    (Complex.I * (k : ℂ)) * x 0]

/-- The unsymmetrized vector-curl symbol is already symmetric on a TT tensor
and rotates plus into cross and cross into minus plus. -/
theorem zFourierCurlSymbol_mul_complexTTTensor
    (k : ℝ) (plus cross : ℂ) :
    zFourierCurlSymbol k * complexTTTensor plus cross =
      complexTTTensor
        (-(Complex.I * (k : ℂ)) * cross)
        ((Complex.I * (k : ℂ)) * plus) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [zFourierCurlSymbol, complexTTTensor, Matrix.mul_apply,
      Fin.sum_univ_succ]

/-- On the complete TT subspace, the generalized spin-two curl is precisely
`i k` times the polarization quarter-turn. -/
theorem spinTwoGeneralizedCurlZ_complexTTTensor
    (k : ℝ) (plus cross : ℂ) :
    spinTwoGeneralizedCurlZ k (complexTTTensor plus cross) =
      complexTTTensor
        (-(Complex.I * (k : ℂ)) * cross)
        ((Complex.I * (k : ℂ)) * plus) := by
  unfold spinTwoGeneralizedCurlZ
  rw [zFourierCurlSymbol_mul_complexTTTensor]
  rw [complexTTTensor_transpose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexTTTensor] <;> ring

/-- Tensor and polarization-coordinate descriptions of the generalized curl
agree exactly. -/
theorem spinTwoGeneralizedCurlZ_coordinates
    (k : ℝ) (x : ComplexTTCoordinates) :
    spinTwoGeneralizedCurlZ k (complexTTTensor (x 0) (x 1)) =
      complexTTTensor
        (complexTTCurlCoordinates k x 0)
        (complexTTCurlCoordinates k x 1) := by
  rw [spinTwoGeneralizedCurlZ_complexTTTensor]
  rfl

/-- The generalized curl squares to `k^2` on each TT polarization.  Since the
Fourier symbol of `Delta` is `-k^2`, this is the fixed-momentum identity
`O^2 = -Delta`. -/
theorem complexTTCurlCoordinates_sq
    (k : ℝ) (x : ComplexTTCoordinates) :
    complexTTCurlCoordinates k (complexTTCurlCoordinates k x) =
      fun i => ((k ^ 2 : ℝ) : ℂ) * x i := by
  funext i
  fin_cases i <;>
    simp [complexTTCurlCoordinates] <;>
    ring_nf <;>
    rw [Complex.I_sq] <;> ring

/-- The generalized curl gives both TT polarizations the same momentum-
squared norm. -/
theorem finiteNormSq_complexTTCurlCoordinates
    (k : ℝ) (x : ComplexTTCoordinates) :
    finiteNormSq (complexTTCurlCoordinates k x) =
      k ^ 2 * finiteNormSq x := by
  simp [finiteNormSq, complexTTCurlCoordinates, Fin.sum_univ_succ,
    Complex.normSq_mul, Complex.normSq_I, Complex.normSq_ofReal]
  ring

/-- The two circular polarization vectors diagonalize the generalized curl.
This convention assigns eigenvalue `+k` to `(1,i)`. -/
noncomputable def ttCurlPositiveEigenmode : ComplexTTCoordinates :=
  ![1, Complex.I]

/-- The opposite circular polarization has generalized-curl eigenvalue
`-k`. -/
noncomputable def ttCurlNegativeEigenmode : ComplexTTCoordinates :=
  ![1, -Complex.I]

theorem complexTTCurlCoordinates_positive_eigenmode (k : ℝ) :
    complexTTCurlCoordinates k ttCurlPositiveEigenmode =
      fun i => (k : ℂ) * ttCurlPositiveEigenmode i := by
  funext i
  fin_cases i <;>
    simp [complexTTCurlCoordinates, ttCurlPositiveEigenmode] <;>
    ring_nf
  all_goals rw [Complex.I_sq]
  all_goals ring

theorem complexTTCurlCoordinates_negative_eigenmode (k : ℝ) :
    complexTTCurlCoordinates k ttCurlNegativeEigenmode =
      fun i => -(k : ℂ) * ttCurlNegativeEigenmode i := by
  funext i
  fin_cases i <;>
    simp [complexTTCurlCoordinates, ttCurlNegativeEigenmode] <;>
    ring_nf
  all_goals rw [Complex.I_sq]
  all_goals ring

/-- Tensor form of `O^2 = -Delta` on the complexified TT subspace. -/
theorem spinTwoGeneralizedCurlZ_sq_complexTTTensor
    (k : ℝ) (plus cross : ℂ) :
    spinTwoGeneralizedCurlZ k
        (spinTwoGeneralizedCurlZ k (complexTTTensor plus cross)) =
      ((k ^ 2 : ℝ) : ℂ) • complexTTTensor plus cross := by
  rw [spinTwoGeneralizedCurlZ_complexTTTensor,
    spinTwoGeneralizedCurlZ_complexTTTensor]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexTTTensor] <;>
    ring_nf <;>
    rw [Complex.I_sq] <;> ring

/-- Complexified exterior response on the TT polarization vector. -/
noncomputable def complexTTExteriorCoordinates (s : ℝ)
    (x : ComplexTTCoordinates) : ComplexTTCoordinates :=
  fun i => (Real.sqrt s : ℂ) * x i

/-- The complexified exterior block contracts the full polarization norm by
its retention weight. -/
theorem finiteNormSq_complexTTExteriorCoordinates
    (s : ℝ) (x : ComplexTTCoordinates) (hs : 0 ≤ s) :
    finiteNormSq (complexTTExteriorCoordinates s x) =
      s * finiteNormSq x := by
  have hsqrt : Real.sqrt s * Real.sqrt s = s :=
    Real.mul_self_sqrt hs
  simp [finiteNormSq, complexTTExteriorCoordinates, Fin.sum_univ_succ,
    Complex.normSq_mul, Complex.normSq_ofReal, hsqrt]
  ring

/-- A polarization-blind passive exterior response commutes with the actual
spin-two generalized-curl symbol. -/
theorem complexTTCurlCoordinates_exterior_commute
    (s k : ℝ) (x : ComplexTTCoordinates) :
    complexTTCurlCoordinates k (complexTTExteriorCoordinates s x) =
      complexTTExteriorCoordinates s (complexTTCurlCoordinates k x) := by
  funext i
  fin_cases i <;>
    simp [complexTTCurlCoordinates, complexTTExteriorCoordinates] <;> ring

/-- The same commutation statement in the tensor representation. -/
theorem spinTwoGeneralizedCurlZ_exterior_commute
    (s k : ℝ) (x : ComplexTTCoordinates) :
    spinTwoGeneralizedCurlZ k
        (complexTTTensor
          (complexTTExteriorCoordinates s x 0)
          (complexTTExteriorCoordinates s x 1)) =
      complexTTTensor
        (complexTTExteriorCoordinates s
          (complexTTCurlCoordinates k x) 0)
        (complexTTExteriorCoordinates s
          (complexTTCurlCoordinates k x) 1) := by
  rw [spinTwoGeneralizedCurlZ_coordinates,
    complexTTCurlCoordinates_exterior_commute]

/-- Quartic specialization: the `sqrt(S_Q) I_2` response commutes with the
duality-symmetric graviton kinetic symbol for every fixed momentum. -/
theorem quarticSpinTwoGeneralizedCurlZ_exterior_commute
    (q k : ℝ) (x : ComplexTTCoordinates) :
    spinTwoGeneralizedCurlZ k
        (complexTTTensor
          (complexTTExteriorCoordinates (screening (lambda4 q)) x 0)
          (complexTTExteriorCoordinates (screening (lambda4 q)) x 1)) =
      complexTTTensor
        (complexTTExteriorCoordinates (screening (lambda4 q))
          (complexTTCurlCoordinates k x) 0)
        (complexTTExteriorCoordinates (screening (lambda4 q))
          (complexTTCurlCoordinates k x) 1) := by
  exact spinTwoGeneralizedCurlZ_exterior_commute
    (screening (lambda4 q)) k x

/-- The quartic response changes only the common TT spectral weight.  It
multiplies the generalized-curl norm by `(2q-1)/q^2` without splitting the
two circular polarizations. -/
theorem quarticExterior_generalizedCurl_normSq
    (q k : ℝ) (x : ComplexTTCoordinates) (hq : 1 < q) :
    finiteNormSq
        (complexTTExteriorCoordinates (screening (lambda4 q))
          (complexTTCurlCoordinates k x)) =
      ((2 * q - 1) / q ^ 2) * k ^ 2 * finiteNormSq x := by
  have hq0 : q ≠ 0 := ne_of_gt (lt_trans (by norm_num) hq)
  rw [finiteNormSq_complexTTExteriorCoordinates
    (screening (lambda4 q)) (complexTTCurlCoordinates k x)
      (quarticScreening_bounds q hq).1]
  rw [finiteNormSq_complexTTCurlCoordinates]
  rw [quartic_screening_identity q hq0]
  ring

#print axioms GravityScreening.zFourierCurlSymbol_mul_complexTTTensor
#print axioms GravityScreening.complexTTTensor_transpose
#print axioms GravityScreening.spinTwoGeneralizedCurlZ_complexTTTensor
#print axioms GravityScreening.spinTwoGeneralizedCurlZ_coordinates
#print axioms GravityScreening.complexTTCurlCoordinates_sq
#print axioms GravityScreening.finiteNormSq_complexTTCurlCoordinates
#print axioms GravityScreening.complexTTCurlCoordinates_positive_eigenmode
#print axioms GravityScreening.complexTTCurlCoordinates_negative_eigenmode
#print axioms GravityScreening.spinTwoGeneralizedCurlZ_sq_complexTTTensor
#print axioms GravityScreening.finiteNormSq_complexTTExteriorCoordinates
#print axioms GravityScreening.complexTTCurlCoordinates_exterior_commute
#print axioms GravityScreening.spinTwoGeneralizedCurlZ_exterior_commute
#print axioms GravityScreening.quarticSpinTwoGeneralizedCurlZ_exterior_commute
#print axioms GravityScreening.quarticExterior_generalizedCurl_normSq

end GravityScreening
