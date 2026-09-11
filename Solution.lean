import Mathlib
import GravityScreening.HodgeLieGeneration
import GravityScreening.GeometricResponseRigidity
import ResponseClosureGeometry

/-!
# Local Hodge generation of sl(15) and scalar response rigidity

Fifteen adjoint matrices, calculated from the fixed six-dimensional orthogonal
form and its bivector basis, together with one oriented local Lorentz Hodge
operator generate sl(15,K) over every field with two nonzero. The generated
space has dimension 224. Covariance under the commutator actions of those
same sixteen generators then forces a linear response on that space to be
scalar, with determinant c^224. These are parts of one generation-and-rigidity
theorem; its scalar c is not physically calibrated by the statement.

All geometric data and quantifiers are displayed below. The ordinary fixed
proposition is repeated verbatim in the theorem documentation so the reviewer
can inspect it in the partial declaration view. definition_names remains empty.
The mathematical mechanism and prior-work comparison are in LIE_GENERATION.md.
-/

namespace HorizonEinsteinClosure

noncomputable section

open scoped Matrix
attribute [local instance] LieRing.ofAssociativeRing

abbrev AmbientIntegralMatrix := Matrix (Fin 6) (Fin 6) ℤ
abbrev IntegralResponse := Matrix (Fin 15) (Fin 15) ℤ

/-- Ambient metric with real signature (4,2), whose first four directions
have Lorentz signature (3,1). -/
def eta : Fin 6 → ℤ := ![1, 1, 1, -1, 1, -1]

/-- All increasing bivector index pairs, in lexicographic order. -/
def bivectorPairs : Fin 15 → Fin 6 × Fin 6 :=
  ![(0,1), (0,2), (0,3), (0,4), (0,5), (1,2), (1,3), (1,4),
    (1,5), (2,3), (2,4), (2,5), (3,4), (3,5), (4,5)]

/-- The actual orthogonal matrix L_ab = eta_b E_ab - eta_a E_ba. -/
def orthogonalGenerator (p : Fin 15) : AmbientIntegralMatrix :=
  Matrix.single (bivectorPairs p).1 (bivectorPairs p).2 (eta (bivectorPairs p).2) -
  Matrix.single (bivectorPairs p).2 (bivectorPairs p).1 (eta (bivectorPairs p).1)

/-- Bivector coefficient of a six-dimensional orthogonal matrix. -/
def bivectorCoordinates (M : AmbientIntegralMatrix) (p : Fin 15) : ℤ :=
  eta (bivectorPairs p).2 * M (bivectorPairs p).1 (bivectorPairs p).2

/-- The adjoint matrix is computed from actual six-by-six commutators. -/
def integralAdjoint (p : Fin 15) : IntegralResponse := fun output input =>
  bivectorCoordinates
    (orthogonalGenerator p * orthogonalGenerator input -
      orthogonalGenerator input * orthogonalGenerator p) output

/-- Inversion count for the four-dimensional orientation sign. -/
def inversions4 (a b c d : Fin 6) : ℕ :=
  (if a > b then 1 else 0) + (if a > c then 1 else 0) +
  (if a > d then 1 else 0) + (if b > c then 1 else 0) +
  (if b > d then 1 else 0) + (if c > d then 1 else 0)

/-- Oriented volume of the coordinate four-plane 0123, zero outside it or
when indices repeat. -/
def epsilon4 (a b c d : Fin 6) : ℤ :=
  if a.val < 4 ∧ b.val < 4 ∧ c.val < 4 ∧ d.val < 4 ∧
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d
  then (-1) ^ inversions4 a b c d else 0

/-- Lorentz Hodge star on local bivectors, extended by zero on the other
nine conformal directions. -/
def integralHodge : IntegralResponse := fun output input =>
  eta (bivectorPairs input).1 * eta (bivectorPairs input).2 *
    epsilon4 (bivectorPairs input).1 (bivectorPairs input).2
      (bivectorPairs output).1 (bivectorPairs output).2

abbrev ResponseMatrix (K : Type) := Matrix (Fin 15) (Fin 15) K

/-- Explicit scalar extension of the geometrically computed adjoint matrix. -/
def geometricAdjoint (K : Type) [Field K] (p : Fin 15) : ResponseMatrix K :=
  fun i j => (integralAdjoint p i j : K)

/-- Explicit scalar extension of the local Lorentz Hodge operator. -/
def geometricHodge (K : Type) [Field K] : ResponseMatrix K :=
  fun i j => (integralHodge i j : K)

/-- The least Lie subalgebra containing the adjoint actions and Hodge star. -/
def geometricResponseAlgebra (K : Type) [Field K] :
    LieSubalgebra K (ResponseMatrix K) :=
  LieSubalgebra.lieSpan K (ResponseMatrix K)
    (Set.range (geometricAdjoint K) ∪ {geometricHodge K})

/-- The response acts on the trace-free algebra, of dimension 224. -/
abbrev ResponseSpace (K : Type) [Field K] :=
  LieAlgebra.SpecialLinear.sl (Fin 15) K

/-- Commutator action A X - X A on the trace-free response space. -/
def responseCommutator (K : Type) [Field K] (A : ResponseMatrix K) :
    ResponseSpace K →ₗ[K] ResponseSpace K where
  toFun X := ⟨A * X.val - X.val * A, by
    change (A * X.val - X.val * A).trace = 0
    rw [Matrix.trace_sub, Matrix.trace_mul_comm]
    exact sub_self _⟩
  map_add' X Y := by
    apply Subtype.ext
    change A * (X.val + Y.val) - (X.val + Y.val) * A =
      (A * X.val - X.val * A) + (A * Y.val - Y.val * A)
    noncomm_ring
  map_smul' c X := by
    apply Subtype.ext
    change A * (c • X.val) - (c • X.val) * A = c • (A * X.val - X.val * A)
    rw [Matrix.mul_smul, Matrix.smul_mul, smul_sub]

private theorem geometricAdjoint_eq_cast (K : Type) [Field K] (p : Fin 15) :
    geometricAdjoint K p = GravityScreening.HodgeLieGeneration.castMatrix K
      (GravityScreening.ResponseClosureCertificate.adj p) := by
  rw [GravityScreening.ResponseClosureGeometry.certificate_adjoint]
  rfl

private theorem geometricHodge_eq_cast (K : Type) [Field K] :
    geometricHodge K = GravityScreening.HodgeLieGeneration.castMatrix K
      GravityScreening.ResponseClosureCertificate.hodge := by
  rw [GravityScreening.ResponseClosureGeometry.certificate_hodge]
  rfl

private theorem geometricResponseAlgebra_eq_generated (K : Type) [Field K] :
    geometricResponseAlgebra K = GravityScreening.HodgeLieGeneration.generated K := by
  have ha : geometricAdjoint K = fun p =>
      GravityScreening.HodgeLieGeneration.castMatrix K
        (GravityScreening.ResponseClosureCertificate.adj p) :=
    funext (geometricAdjoint_eq_cast K)
  change LieSubalgebra.lieSpan K (ResponseMatrix K)
      (Set.range (geometricAdjoint K) ∪ {geometricHodge K}) =
    LieSubalgebra.lieSpan K (ResponseMatrix K)
      (Set.range (fun p => GravityScreening.HodgeLieGeneration.castMatrix K
        (GravityScreening.ResponseClosureCertificate.adj p)) ∪
        {GravityScreening.HodgeLieGeneration.castMatrix K
          GravityScreening.ResponseClosureCertificate.hodge})
  rw [ha, geometricHodge_eq_cast]

lemma responseCommutator_geometricAdjoint (K : Type) [Field K]
    (p : Fin 15) (X : ResponseSpace K) :
    responseCommutator K (geometricAdjoint K p) X =
      ⁅GravityScreening.HodgeResponseCovariance.adjointGenerator K p, X⁆ := by
  apply Subtype.ext
  change geometricAdjoint K p * X.val - X.val * geometricAdjoint K p =
    (GravityScreening.HodgeResponseCovariance.adjointGenerator K p).val * X.val -
      X.val * (GravityScreening.HodgeResponseCovariance.adjointGenerator K p).val
  rw [geometricAdjoint_eq_cast,
    GravityScreening.HodgeResponseCovariance.coe_adjointGenerator]

lemma responseCommutator_geometricHodge (K : Type) [Field K]
    (X : ResponseSpace K) :
    responseCommutator K (geometricHodge K) X =
      ⁅GravityScreening.HodgeResponseCovariance.hodgeGenerator K, X⁆ := by
  apply Subtype.ext
  change geometricHodge K * X.val - X.val * geometricHodge K =
    (GravityScreening.HodgeResponseCovariance.hodgeGenerator K).val * X.val -
      X.val * (GravityScreening.HodgeResponseCovariance.hodgeGenerator K).val
  rw [geometricHodge_eq_cast,
    GravityScreening.HodgeResponseCovariance.coe_hodgeGenerator]

def geometricHodgeGenerationStatement : Prop :=
  ∀ (K : Type) [Field K], (2 : K) ≠ 0 →
    geometricResponseAlgebra K = LieAlgebra.SpecialLinear.sl (Fin 15) K ∧
      Module.finrank K (geometricResponseAlgebra K) = 224 ∧
      ∀ R : ResponseSpace K →ₗ[K] ResponseSpace K,
        (∀ p X, R (responseCommutator K (geometricAdjoint K p) X) =
          responseCommutator K (geometricAdjoint K p) (R X)) →
        (∀ X, R (responseCommutator K (geometricHodge K) X) =
          responseCommutator K (geometricHodge K) (R X)) →
        ∃ c : K, R = c • LinearMap.id ∧ LinearMap.det R = c ^ 224

/-- Complete statement proved below. The complete geometric data are as follows. The ambient metric is
eta = diag(1,1,1,-1,1,-1). The ordered bivector basis is
01,02,03,04,05,12,13,14,15,23,24,25,34,35,45, with
L_ab = eta_b E_ab - eta_a E_ba as actual six-by-six matrices.
The adjoint generator indexed by p sends L_c to [L_p,L_c]; its coefficient
along L_ab is eta_b times the (a,b) entry of that actual matrix commutator.

The oriented Lorentz four-plane is 0123. Its local Hodge operator satisfies
H(L01)=L23, H(L23)=-L01; H(L02)=-L13, H(L13)=L02;
H(L03)=-L12, H(L12)=L03. It is zero on the other nine basis vectors.
The displayed integer coefficients are extended entrywise to K.
Here geometricResponseAlgebra K is the smallest K-linear matrix subspace
containing these fifteen adjoint actions and H and closed under AB-BA.
The conclusion identifies that generated algebra with all trace-free
fifteen-by-fifteen matrices; its dimension is a consequence of generation.

The final clause concerns a linear response R on ResponseSpace K = sl(15,K),
the 224-dimensional algebra itself. Here responseCommutator K A X = A X-X A.
If R commutes with these commutator actions for each of the sixteen displayed
generators, R is forced to be scalar and its determinant is c^224 for that
same scalar c. No simplicity hypothesis or value of c is assumed. This holds
also in odd characteristics dividing fifteen. Physical calibration of c is
not a conclusion of the statement.

The displayed definition is an exact copy
of the fixed proposition immediately above; Comparator checks its full body.

```lean
def geometricHodgeGenerationStatement : Prop :=
  ∀ (K : Type) [Field K], (2 : K) ≠ 0 →
    geometricResponseAlgebra K = LieAlgebra.SpecialLinear.sl (Fin 15) K ∧
      Module.finrank K (geometricResponseAlgebra K) = 224 ∧
      ∀ R : ResponseSpace K →ₗ[K] ResponseSpace K,
        (∀ p X, R (responseCommutator K (geometricAdjoint K p) X) =
          responseCommutator K (geometricAdjoint K p) (R X)) →
        (∀ X, R (responseCommutator K (geometricHodge K) X) =
          responseCommutator K (geometricHodge K) (R X)) →
        ∃ c : K, R = c • LinearMap.id ∧ LinearMap.det R = c ^ 224
```
-/
theorem geometricHodgeGeneration : geometricHodgeGenerationStatement := by
  intro K _ htwo
  refine ⟨?_, ?_, ?_⟩
  · rw [geometricResponseAlgebra_eq_generated]
    exact GravityScreening.HodgeLieGeneration.generated_eq_sl K htwo
  · rw [geometricResponseAlgebra_eq_generated]
    exact GravityScreening.HodgeLieGeneration.finrank_generated K htwo
  · intro R ha hh
    apply GravityScreening.GeometricResponseRigidity.geometric_response_scalar_and_determinant
      K htwo R
    · intro p X
      simpa only [responseCommutator_geometricAdjoint] using ha p X
    · intro X
      simpa only [responseCommutator_geometricHodge] using hh X

#print axioms HorizonEinsteinClosure.geometricHodgeGeneration

end

end HorizonEinsteinClosure
