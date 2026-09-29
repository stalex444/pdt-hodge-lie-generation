module
public import GravityScreening.HorizonBranch

@[expose] public section

/-!
# The modular spectral-line origin of the quartic amplitude

For the canonical KMS state of the quartic graph algebra, standard modular
theory turns a degree-one gauge mode into a GNS modular eigenvector with
eigenvalue `1 / q`.  Formalizing that operator-algebra theorem lies outside the
present finite-dimensional Lean model, so this file takes the resulting
eigenvector equation as an explicit hypothesis and kernel-checks every
algebraic consequence used by the proposed horizon channel.

The physical identification of this graph-GNS spectral subspace with a local
causal-horizon mode is not asserted here.
-/

namespace GravityScreening

/-- On a modular spectral subspace with eigenvalue `1/q`, the one-step defect
`I - Delta` has the exact quartic residue amplitude `lambda4 q`. -/
theorem modularEigenvector_defect
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (Delta : Module.End ℂ V) (xi : V) (q : ℝ)
    (hEigen : Delta xi = ((1 / q : ℝ) : ℂ) • xi) :
    (1 - Delta) xi = (lambda4 q : ℂ) • xi := by
  change xi - Delta xi = (lambda4 q : ℂ) • xi
  rw [hEigen]
  simp [lambda4, sub_smul]

/-- The modular defect has squared Hilbert norm `lambda4 q ^ 2` times the
input norm on its spectral subspace.  This is the precise amplitude-to-Born-
weight step; it does not treat a classical event frequency as an amplitude. -/
theorem modularEigenvector_defect_norm_sq
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (Delta : Module.End ℂ V) (xi : V) (q : ℝ)
    (hEigen : Delta xi = ((1 / q : ℝ) : ℂ) • xi) :
    ‖(1 - Delta) xi‖ ^ 2 =
      lambda4 q ^ 2 * ‖xi‖ ^ 2 := by
  rw [modularEigenvector_defect Delta xi q hEigen, norm_smul]
  simp [mul_pow]

/-- The complete conditional chain.  A modular eigenvalue `1/q` fixes the
defect amplitude, and a norm-preserving complementary branch then scales the
entropy first-law pairing by the quartic factor `(2q-1)/q^2`.

The modular eigenvector equation and the identification of the complementary
branch with visible horizon data remain explicit premises. -/
theorem modularDefect_quarticFirstLaw
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {n : ℕ} (Delta : Module.End ℂ V) (xi : V)
    (k delta : Fin n → ℝ) (q d : ℝ)
    (hEigen : Delta xi = ((1 / q : ℝ) : ℂ) • xi)
    (hq0 : q ≠ 0) (hComplement : d ^ 2 = screening (lambda4 q)) :
    (1 - Delta) xi = (lambda4 q : ℂ) • xi ∧
      firstLawVariation k (scalarBranchPerturbation d delta) =
        ((2 * q - 1) / q ^ 2) * firstLawVariation k delta := by
  exact ⟨modularEigenvector_defect Delta xi q hEigen,
    quarticDefectBranch_firstLaw k delta q d hq0 hComplement⟩

#print axioms GravityScreening.modularEigenvector_defect
#print axioms GravityScreening.modularEigenvector_defect_norm_sq
#print axioms GravityScreening.modularDefect_quarticFirstLaw

end GravityScreening
