module
public import Mathlib.Algebra.Lie.Semisimple.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.FieldTheory.IsAlgClosed.Basic

@[expose] public section

/-!
# Adjoint invariant-subspace interface and scalar response uniqueness

Mathlib already supplies the instance
`[LieAlgebra.IsSimple K L] → LieModule.IsIrreducible K L L`
in `Mathlib.Algebra.Lie.Semisimple.Basic`. This file exposes its consequence
for ordinary linear submodules and the range of `LieAlgebra.ad`, the exact
interface used by the operator-form Schur theorem in the canon's
`PdtSchurExponent.lean`. No additional irreducibility premise is introduced.

The scalar-response theorem concerns `Module.End K L`, acting on the Lie
algebra itself via its adjoint action. For a prospective application to
`sl(15)`, this is the 224-dimensional adjoint space, not its 15-dimensional
natural representation. This file does not assert a new simplicity instance
for `sl(15)`.

The invariant-subspace statement needs neither algebraic closure nor
characteristic zero. The scalar-response theorem uses algebraic closure and
finite dimension to supply an eigenvalue. It also holds in positive
characteristic whenever the displayed simplicity assumption holds. The scalar
`c` remains arbitrary: identifying it with a physical ruler or identifying the
determinant with a coupling is outside these statements.
-/

namespace GravityScreening.AdjointResponseUniqueness

open Module LinearMap

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]

/-- Lie-module irreducibility rules out an ordinary linear subspace invariant
under every adjoint operator. The constructed Lie ideal has exactly the given
underlying submodule. -/
theorem adjoint_invariant_submodule_eq_bot_or_top
    [LieModule.IsIrreducible K L L]
    (W : Submodule K L)
    (hW : ∀ x y : L, y ∈ W → LieAlgebra.ad K L x y ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  let I : LieIdeal K L :=
    { W with lie_mem := fun {x y} hy => hW x y hy }
  rcases IsSimpleOrder.eq_bot_or_eq_top I with hI | hI
  · left
    exact congrArg LieSubmodule.toSubmodule hI
  · right
    exact congrArg LieSubmodule.toSubmodule hI

/-- The exact plain-submodule irreducibility hypothesis used by operator-form
Schur is discharged by simplicity, via Mathlib's existing adjoint instance. -/
theorem simple_adjoint_irreducible [LieAlgebra.IsSimple K L] :
    ∀ W : Submodule K L,
      (∀ s ∈ Set.range (LieAlgebra.ad K L), ∀ y ∈ W, s y ∈ W) →
      W = ⊥ ∨ W = ⊤ := by
  intro W hW
  apply adjoint_invariant_submodule_eq_bot_or_top W
  intro x y hy
  exact hW (LieAlgebra.ad K L x) ⟨x, rfl⟩ y hy

/-- An endomorphism commuting with every adjoint action on a finite-dimensional
simple Lie algebra over an algebraically closed field is scalar. -/
theorem commuting_adjoint_is_scalar
    [LieAlgebra.IsSimple K L] [IsAlgClosed K] [FiniteDimensional K L]
    (T : Module.End K L)
    (hT : ∀ x : L, LieAlgebra.ad K L x * T = T * LieAlgebra.ad K L x) :
    ∃ c : K, T = c • (LinearMap.id : L →ₗ[K] L) := by
  haveI : Nontrivial L := (LieSubmodule.nontrivial_iff K L L).mp inferInstance
  obtain ⟨c, hc⟩ := T.exists_eigenvalue
  have hinv : ∀ s ∈ Set.range (LieAlgebra.ad K L),
      ∀ y ∈ End.eigenspace T c, s y ∈ End.eigenspace T c := by
    rintro s ⟨x, rfl⟩ y hy
    rw [End.mem_eigenspace_iff] at hy ⊢
    have hcomm : (LieAlgebra.ad K L x * T) y =
        (T * LieAlgebra.ad K L x) y := by rw [hT x]
    simpa [hy, map_smul] using hcomm.symm
  rcases simple_adjoint_irreducible (End.eigenspace T c) hinv with hbot | htop
  · exact absurd hbot hc
  · refine ⟨c, ?_⟩
    ext y
    have hy : y ∈ End.eigenspace T c := htop ▸ Submodule.mem_top
    simpa using End.mem_eigenspace_iff.mp hy

/-- Scalarity and the exponent law hold for the same scalar. No value of that
scalar is assumed or selected by the exponent argument. -/
theorem commuting_adjoint_scalar_and_determinant
    [LieAlgebra.IsSimple K L] [IsAlgClosed K] [FiniteDimensional K L]
    (T : Module.End K L)
    (hT : ∀ x : L, LieAlgebra.ad K L x * T = T * LieAlgebra.ad K L x) :
    ∃ c : K, T = c • (LinearMap.id : L →ₗ[K] L) ∧
      LinearMap.det T = c ^ Module.finrank K L := by
  obtain ⟨c, hc⟩ := commuting_adjoint_is_scalar T hT
  refine ⟨c, hc, ?_⟩
  rw [hc, LinearMap.det_smul, LinearMap.det_id, mul_one]

#print axioms adjoint_invariant_submodule_eq_bot_or_top
#print axioms simple_adjoint_irreducible
#print axioms commuting_adjoint_is_scalar
#print axioms commuting_adjoint_scalar_and_determinant

end GravityScreening.AdjointResponseUniqueness
