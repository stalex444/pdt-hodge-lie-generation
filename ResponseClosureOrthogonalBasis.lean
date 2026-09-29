module
public import Mathlib
public import ResponseClosureGeometry

@[expose] public section

/-!
# The fifteen explicit generators span the full orthogonal matrix algebra

The signs and pair order are those of ResponseClosureGeometry.lean.
All identities below are proved over an arbitrary field. Characteristic two
is excluded only when deducing a zero diagonal from eta-skewness.
-/

namespace GravityScreening.ResponseClosureOrthogonalBasis

open scoped Matrix

set_option maxHeartbeats 2000000

/-- The same lexicographic pair order as the integral geometry certificate. -/
def basisPairs : Fin 15 → Fin 6 × Fin 6 :=
  ![(0,1), (0,2), (0,3), (0,4), (0,5), (1,2), (1,3), (1,4),
    (1,5), (2,3), (2,4), (2,5), (3,4), (3,5), (4,5)]

section Field

variable {K : Type*} [Field K]

abbrev AmbientMatrix := Matrix (Fin 6) (Fin 6) K

def eta : Fin 6 → K := ![1, 1, 1, -1, 1, -1]

def metric : AmbientMatrix (K := K) := Matrix.diagonal eta

/-- L_ab = eta_b E_ab - eta_a E_ba, over the current field. -/
def orthogonalGenerator (p : Fin 15) : AmbientMatrix (K := K) :=
  Matrix.single (basisPairs p).1 (basisPairs p).2 (eta (basisPairs p).2) -
    Matrix.single (basisPairs p).2 (basisPairs p).1 (eta (basisPairs p).1)

def coordinates (M : AmbientMatrix (K := K)) (p : Fin 15) : K :=
  eta (basisPairs p).2 * M (basisPairs p).1 (basisPairs p).2

def realize (v : Fin 15 → K) : AmbientMatrix (K := K) :=
  ∑ p, v p • orthogonalGenerator p

def IsEtaSkew (M : AmbientMatrix (K := K)) : Prop :=
  M.transpose * metric + metric * M = 0

theorem eta_ne_zero (i : Fin 6) : (eta (K := K)) i ≠ 0 := by
  fin_cases i <;> norm_num [eta]

theorem isEtaSkew_iff_entries (M : AmbientMatrix (K := K)) :
    IsEtaSkew M ↔ ∀ i j, M j i * eta j + eta i * M i j = 0 := by
  constructor
  · intro h i j
    have he := congrFun (congrFun h i) j
    simpa [metric, Matrix.mul_diagonal, Matrix.diagonal_mul,
      Matrix.transpose_apply] using he
  · intro h
    ext i j
    simpa [metric, Matrix.mul_diagonal, Matrix.diagonal_mul,
      Matrix.transpose_apply] using h i j

/-- Coordinate extraction is a left inverse to synthesis over every field. -/
theorem coordinates_realize (v : Fin 15 → K) : coordinates (realize v) = v := by
  funext p
  fin_cases p <;>
    simp [coordinates, realize, orthogonalGenerator, basisPairs, eta,
      Fin.sum_univ_succ]

theorem realize_injective : Function.Injective (realize (K := K)) := by
  intro v w h
  have hc := congrArg coordinates h
  simpa [coordinates_realize] using hc

/-- Every synthesized matrix satisfies the full metric-skew equation. -/
theorem realize_eta_skew (v : Fin 15 → K) : IsEtaSkew (realize v) := by
  rw [isEtaSkew_iff_entries]
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [realize, orthogonalGenerator, basisPairs, eta,
      Fin.sum_univ_succ]

theorem realize_diagonal_zero (v : Fin 15 → K) (i : Fin 6) :
    realize v i i = 0 := by
  fin_cases i <;>
    simp [realize, orthogonalGenerator, basisPairs, eta, Fin.sum_univ_succ]

/-- Off-diagonal coordinates cannot account for a diagonal in characteristic
two; this is the only point where 2 != 0 is necessary. -/
theorem diagonal_eq_zero (h2 : (2 : K) ≠ 0)
    (M : AmbientMatrix (K := K)) (hM : IsEtaSkew M) (i : Fin 6) :
    M i i = 0 := by
  have he := (isEtaSkew_iff_entries M).mp hM i i
  have hprod : ((2 : K) * eta i) * M i i = 0 := by
    calc
      ((2 : K) * eta i) * M i i = M i i * eta i + eta i * M i i := by ring
      _ = 0 := he
  exact (mul_eq_zero.mp hprod).resolve_left (mul_ne_zero h2 (eta_ne_zero i))

/-- Every eta-skew matrix is synthesized from its explicit fifteen upper
coordinates. This is spanning of the actual orthogonal algebra, not a count. -/
theorem realize_coordinates (h2 : (2 : K) ≠ 0)
    (M : AmbientMatrix (K := K)) (hM : IsEtaSkew M) :
    realize (coordinates M) = M := by
  have hd : ∀ i, M i i = 0 := diagonal_eq_zero h2 M hM
  ext i j
  have he := (isEtaSkew_iff_entries M).mp hM i j
  fin_cases i <;> fin_cases j <;>
    simp [realize, coordinates, orthogonalGenerator, basisPairs, eta,
      Fin.sum_univ_succ, hd] at he ⊢ <;>
    first | linear_combination he | linear_combination -he

/-- The requested explicit reconstruction formula. -/
theorem eta_skew_eq_sum (h2 : (2 : K) ≠ 0)
    (M : AmbientMatrix (K := K))
    (hM : M.transpose * Matrix.diagonal eta + Matrix.diagonal eta * M = 0) :
    M = ∑ p, (eta (basisPairs p).2 * M (basisPairs p).1 (basisPairs p).2) •
      orthogonalGenerator p :=
  (realize_coordinates h2 M hM).symm

/-- There are exactly fifteen independent generators, without any hypothesis
restricting the characteristic for independence itself. -/
theorem orthogonalGenerator_linearIndependent :
    LinearIndependent K (orthogonalGenerator (K := K)) := by
  apply Fintype.linearIndependent_iff.mpr
  intro v h i
  have hc := congrArg coordinates h
  change coordinates (realize v) = coordinates 0 at hc
  rw [coordinates_realize] at hc
  have hi := congrFun hc i
  simpa [coordinates] using hi

/-- Membership in the full orthogonal matrix algebra is equivalent to the
existence of unique coordinates in this displayed generator family. -/
theorem eta_skew_iff_unique_coordinates (h2 : (2 : K) ≠ 0)
    (M : AmbientMatrix (K := K)) :
    IsEtaSkew M ↔ ∃! v : Fin 15 → K, realize v = M := by
  constructor
  · intro hM
    refine ⟨coordinates M, realize_coordinates h2 M hM, ?_⟩
    intro v hv
    have hc := congrArg coordinates hv
    simpa [coordinates_realize] using hc
  · rintro ⟨v, hv, _⟩
    rw [← hv]
    exact realize_eta_skew v

/-- The characteristic restriction is necessary: in characteristic two the
identity is eta-skew but cannot be synthesized from these zero-diagonal generators. -/
theorem characteristicTwo_identity_obstruction (h2 : (2 : K) = 0) :
    IsEtaSkew (1 : AmbientMatrix (K := K)) ∧
      ¬ ∃ v : Fin 15 → K, realize v = 1 := by
  constructor
  · rw [isEtaSkew_iff_entries]
    intro i j
    by_cases hij : i = j
    · subst j
      have hs : eta (K := K) i + eta i = 0 := by
        linear_combination eta i * h2
      simpa using hs
    · simp [hij, Ne.symm hij]
  · rintro ⟨v, hv⟩
    have he := congrFun (congrFun hv 0) 0
    rw [realize_diagonal_zero] at he
    simp at he

/-! Scalar-extension bridge to the actual integral geometry module. -/

theorem basisPairs_eq_geometry : basisPairs = ResponseClosureGeometry.basisPairs := rfl

theorem eta_eq_geometry_cast :
    eta (K := K) = fun i => (ResponseClosureGeometry.eta i : K) := by
  funext i
  fin_cases i <;> norm_num [eta, ResponseClosureGeometry.eta]

theorem metric_eq_geometry_cast :
    metric (K := K) = ResponseClosureGeometry.metric.map (Int.castRingHom K) := by
  ext i j
  simp [metric, ResponseClosureGeometry.metric, Matrix.map_apply,
    Matrix.diagonal_apply, eta_eq_geometry_cast]

/-- Our field generators are exactly entrywise casts of the verified integral
geometric generators, without a change of basis or indexing. -/
theorem orthogonalGenerator_eq_geometry_cast (p : Fin 15) :
    orthogonalGenerator (K := K) p =
      (ResponseClosureGeometry.orthogonalGenerator p).map (Int.castRingHom K) := by
  ext i j
  simp [orthogonalGenerator, ResponseClosureGeometry.orthogonalGenerator,
    Matrix.map_apply, Matrix.single_apply, eta_eq_geometry_cast,
    basisPairs_eq_geometry]

theorem coordinates_geometry_cast (M : ResponseClosureGeometry.AmbientMatrix) :
    coordinates (M.map (Int.castRingHom K)) =
      fun p => (ResponseClosureGeometry.coordinates M p : K) := by
  funext p
  simp [coordinates, ResponseClosureGeometry.coordinates, Matrix.map_apply,
    eta_eq_geometry_cast, basisPairs_eq_geometry]

theorem realize_geometry_cast (v : Fin 15 → ℤ) :
    realize (fun p => (v p : K)) =
      (ResponseClosureGeometry.realize v).map (Int.castRingHom K) := by
  ext i j
  simp only [realize, ResponseClosureGeometry.realize, Matrix.map_apply,
    Matrix.sum_apply, Matrix.smul_apply]
  simp [orthogonalGenerator_eq_geometry_cast, Matrix.map_apply, smul_eq_mul]

/-- Literal spanning statement for the scalar extensions of the integral
geometry generators and metric used by the adjoint-table certificate. -/
theorem geometry_eta_skew_eq_sum (h2 : (2 : K) ≠ 0)
    (M : AmbientMatrix (K := K))
    (hM : M.transpose * ResponseClosureGeometry.metric.map (Int.castRingHom K) +
      ResponseClosureGeometry.metric.map (Int.castRingHom K) * M = 0) :
    M = ∑ p,
      ((ResponseClosureGeometry.eta (ResponseClosureGeometry.basisPairs p).2 : K) *
        M (ResponseClosureGeometry.basisPairs p).1
          (ResponseClosureGeometry.basisPairs p).2) •
      (ResponseClosureGeometry.orthogonalGenerator p).map (Int.castRingHom K) := by
  have hM' : IsEtaSkew M := by
    simpa only [IsEtaSkew, ← metric_eq_geometry_cast] using hM
  simpa only [eta_eq_geometry_cast, basisPairs_eq_geometry,
    orthogonalGenerator_eq_geometry_cast] using eta_skew_eq_sum h2 M hM'

theorem geometry_generators_linearIndependent :
    LinearIndependent K (fun p =>
      (ResponseClosureGeometry.orthogonalGenerator p).map (Int.castRingHom K)) := by
  have hf : orthogonalGenerator (K := K) = fun p =>
      (ResponseClosureGeometry.orthogonalGenerator p).map (Int.castRingHom K) :=
    funext orthogonalGenerator_eq_geometry_cast
  rw [← hf]
  exact orthogonalGenerator_linearIndependent

#print axioms coordinates_realize
#print axioms realize_coordinates
#print axioms eta_skew_eq_sum
#print axioms orthogonalGenerator_linearIndependent
#print axioms eta_skew_iff_unique_coordinates
#print axioms characteristicTwo_identity_obstruction
#print axioms orthogonalGenerator_eq_geometry_cast
#print axioms coordinates_geometry_cast
#print axioms realize_geometry_cast
#print axioms geometry_eta_skew_eq_sum
#print axioms geometry_generators_linearIndependent

end Field

end GravityScreening.ResponseClosureOrthogonalBasis
