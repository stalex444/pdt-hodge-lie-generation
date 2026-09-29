module
public import ResponseClosureCertificate
public import Mathlib.LinearAlgebra.Matrix.Trace

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Geometric identification of the integral response generators

The adjoint table is identified with brackets of explicit six-dimensional
orthogonal generators.  The Hodge table is identified with the complementary
bivector operation on the oriented coordinate four-plane 0123, with metric
signature +++-, and is zero on the remaining nine bivectors.

All finite certificates use Lean's kernel evaluator.  The definitions below
are geometric formulas, independent of the tables in the certificate module.
-/

namespace GravityScreening.ResponseClosureGeometry

open ResponseClosureCertificate

abbrev AmbientMatrix := Matrix (Fin 6) (Fin 6) ℤ

/-- The fixed six-dimensional metric, with real signature (4,2). -/
def eta : Fin 6 → ℤ := ![1, 1, 1, -1, 1, -1]

/-- All increasing index pairs, in lexicographic order. -/
def basisPairs : Fin 15 → Fin 6 × Fin 6 :=
  ![(0,1), (0,2), (0,3), (0,4), (0,5), (1,2), (1,3), (1,4),
    (1,5), (2,3), (2,4), (2,5), (3,4), (3,5), (4,5)]

/-- Matrix of the fixed bilinear form. -/
def metric : AmbientMatrix := Matrix.diagonal eta

/-- The orthogonal generator L_ab = eta_b E_ab - eta_a E_ba. -/
def orthogonalGenerator (p : Fin 15) : AmbientMatrix :=
  Matrix.single (basisPairs p).1 (basisPairs p).2 (eta (basisPairs p).2) -
  Matrix.single (basisPairs p).2 (basisPairs p).1 (eta (basisPairs p).1)

/-- Extract the coefficient of L_ab from an orthogonal matrix. -/
def coordinates (A : AmbientMatrix) (p : Fin 15) : ℤ :=
  eta (basisPairs p).2 * A (basisPairs p).1 (basisPairs p).2

/-- Synthesize a six-dimensional matrix from bivector coordinates. -/
def realize (v : Fin 15 → ℤ) : AmbientMatrix :=
  ∑ p, v p • orthogonalGenerator p

/-- Actual matrix commutator in dimension six. -/
def ambientBracket (A B : AmbientMatrix) : AmbientMatrix := A * B - B * A

/-- Adjoint action in bivector coordinates, calculated from 6-by-6 brackets. -/
def geometricAdjoint (p : Fin 15) : IMat := fun r c =>
  coordinates (ambientBracket (orthogonalGenerator p) (orthogonalGenerator c)) r

/-- Inversion count of an ordered four-tuple. -/
def inversions4 (a b c d : Fin 6) : ℕ :=
  (if a > b then 1 else 0) + (if a > c then 1 else 0) +
  (if a > d then 1 else 0) + (if b > c then 1 else 0) +
  (if b > d then 1 else 0) + (if c > d then 1 else 0)

/-- Oriented volume of the coordinate four-plane 0123: zero unless the
indices are distinct and lie in this plane, otherwise their permutation sign. -/
def epsilon4 (a b c d : Fin 6) : ℤ :=
  if a.val < 4 ∧ b.val < 4 ∧ c.val < 4 ∧ d.val < 4 ∧
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d
  then (-1) ^ inversions4 a b c d else 0

/-- Lorentz Hodge on increasing bivectors: the complementary bivector carries
the metric sign eta_a eta_b and the orientation sign epsilon_abcd. -/
def hodgeComplement : IMat := fun output input =>
  eta (basisPairs input).1 * eta (basisPairs input).2 *
    epsilon4 (basisPairs input).1 (basisPairs input).2
      (basisPairs output).1 (basisPairs output).2

/-- A bivector is local when both its indices lie in the four-plane 0123. -/
def LocalPair (p : Fin 15) : Prop :=
  (basisPairs p).1.val < 4 ∧ (basisPairs p).2.val < 4

instance (p : Fin 15) : Decidable (LocalPair p) := inferInstanceAs
  (Decidable ((basisPairs p).1.val < 4 ∧ (basisPairs p).2.val < 4))

/-- Coordinate projection onto the six local bivectors. -/
def localProjector : IMat := Matrix.diagonal (fun p => if LocalPair p then 1 else 0)

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem eta_square : ∀ a : Fin 6, eta a * eta a = 1 := by decide +kernel

theorem basisPairs_increasing : ∀ p, (basisPairs p).1 < (basisPairs p).2 := by
  decide +kernel

theorem basisPairs_injective : Function.Injective basisPairs := by decide +kernel

theorem basisPairs_exhaustive : ∀ a b : Fin 6, a < b → ∃ p, basisPairs p = (a,b) := by
  decide +kernel

/-- Every displayed generator lies in the actual orthogonal Lie algebra. -/
theorem orthogonalGenerator_eta_skew : ∀ p,
    (orthogonalGenerator p).transpose * metric + metric * orthogonalGenerator p = 0 := by
  decide +kernel

/-- Coefficient extraction distinguishes the fifteen displayed generators. -/
theorem basis_coordinates : ∀ p q,
    coordinates (orthogonalGenerator q) p = if p = q then 1 else 0 := by
  decide +kernel

/-- The certificate's adjoint matrices really are computed adjoint matrices. -/
theorem certificate_adjoint : ∀ p, adj p = geometricAdjoint p := by
  decide +kernel

/-- Each column of each adjoint matrix reconstructs the actual ambient bracket. -/
theorem basis_bracket : ∀ p q,
    ambientBracket (orthogonalGenerator p) (orthogonalGenerator q) =
      realize (fun r => adj p r q) := by
  decide +kernel

/-- The Hodge table is exactly the metric-and-orientation complement formula. -/
theorem certificate_hodge : hodge = hodgeComplement := by decide +kernel

/-- Zero extension in both source and target directions outside the four-plane. -/
theorem hodge_zero_outside : ∀ p, ¬ LocalPair p → ∀ r,
    hodgeComplement r p = 0 ∧ hodgeComplement p r = 0 := by decide +kernel

/-- Lorentz signature gives star squared equal to minus the local projection. -/
theorem hodge_square : hodgeComplement * hodgeComplement = -localProjector := by
  decide +kernel

/-- The local orientation operator commutes with the Lorentz adjoint generators. -/
theorem hodge_local_equivariance : ∀ p, LocalPair p →
    comm (geometricAdjoint p) hodgeComplement = 0 := by decide +kernel

theorem localPair_count : (Finset.univ.filter LocalPair).card = 6 := by decide +kernel

theorem certificate_bivector_metric : ∀ p,
    q p = eta (basisPairs p).1 * eta (basisPairs p).2 := by decide +kernel

#print axioms certificate_adjoint
#print axioms basis_bracket
#print axioms certificate_hodge
#print axioms hodge_square

end GravityScreening.ResponseClosureGeometry
