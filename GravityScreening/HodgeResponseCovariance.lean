module
public import Mathlib
public import GravityScreening.HodgeLieGeneration
public import ResponseClosureGeometry

@[expose] public section

/-!
# Transporting response covariance through geometric Lie generation

The response in this file is a linear endomorphism of `sl(15,K)`, the
224-dimensional Lie algebra. Its covariance is with respect to commutators
on that space. It is not a linear endomorphism of the natural 15-dimensional
coordinate space.

Covariance under the fifteen geometric adjoint matrices and the local Hodge
matrix extends to covariance under every element of `sl(15,K)`. The proof
uses the existing generation theorem; it does not assume scalarity or any
physical normalization of the response.
-/

namespace GravityScreening.HodgeResponseCovariance

section General

variable {K L : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]

/-- The elements whose adjoint actions commute with a fixed linear response
form a Lie subalgebra. -/
def covarianceSubalgebra (R : L →ₗ[K] L) : LieSubalgebra K L where
  carrier := {a | ∀ x, R ⁅a, x⁆ = ⁅a, R x⁆}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb x
    simp only [Set.mem_setOf_eq] at ha hb
    simp only [add_lie, map_add, ha, hb]
  smul_mem' := by
    intro c a ha x
    simp only [Set.mem_setOf_eq] at ha
    simp only [smul_lie, map_smul, ha]
  lie_mem' := by
    intro a b ha hb x
    simp only [Set.mem_setOf_eq] at ha hb
    simp only [lie_lie, map_sub, ha, hb]

/-- Generator covariance propagates through linear combinations and brackets
in an arbitrary Lie algebra. -/
theorem covariant_of_mem_lieSpan (R : L →ₗ[K] L) (s : Set L)
    (hs : ∀ a ∈ s, ∀ x, R ⁅a, x⁆ = ⁅a, R x⁆)
    {a : L} (ha : a ∈ LieSubalgebra.lieSpan K L s) :
    ∀ x, R ⁅a, x⁆ = ⁅a, R x⁆ := by
  have hle : LieSubalgebra.lieSpan K L s ≤ covarianceSubalgebra R :=
    LieSubalgebra.lieSpan_le.mpr hs
  exact hle ha

end General

section Geometric

attribute [local instance] LieRing.ofAssociativeRing

variable (K : Type*) [Field K]

abbrev ResponseAlgebra := LieAlgebra.SpecialLinear.sl (Fin 15) K

/-- An actual six-dimensional orthogonal adjoint action, in its fifteen
bivector coordinates and now regarded as a trace-free matrix. -/
def adjointGenerator (p : Fin 15) : ResponseAlgebra K :=
  ⟨HodgeLieGeneration.castMatrix K (ResponseClosureGeometry.geometricAdjoint p), by
    change (HodgeLieGeneration.castMatrix K
      (ResponseClosureGeometry.geometricAdjoint p)).trace = 0
    rw [← ResponseClosureGeometry.certificate_adjoint, HodgeLieGeneration.cast_trace,
      ResponseClosureCertificate.adj_trace_zero, Int.cast_zero]⟩

/-- The metric-and-orientation local Hodge operation, extended by zero on
the other nine coordinates, as an element of the response algebra. -/
def hodgeGenerator : ResponseAlgebra K :=
  ⟨HodgeLieGeneration.castMatrix K ResponseClosureGeometry.hodgeComplement, by
    change (HodgeLieGeneration.castMatrix K
      ResponseClosureGeometry.hodgeComplement).trace = 0
    rw [← ResponseClosureGeometry.certificate_hodge, HodgeLieGeneration.cast_trace,
      ResponseClosureCertificate.hodge_trace_zero, Int.cast_zero]⟩

@[simp] theorem coe_adjointGenerator (p : Fin 15) :
    (adjointGenerator K p : Matrix (Fin 15) (Fin 15) K) =
      HodgeLieGeneration.castMatrix K (ResponseClosureCertificate.adj p) := by
  change HodgeLieGeneration.castMatrix K (ResponseClosureGeometry.geometricAdjoint p) = _
  rw [ResponseClosureGeometry.certificate_adjoint]

@[simp] theorem coe_hodgeGenerator :
    (hodgeGenerator K : Matrix (Fin 15) (Fin 15) K) =
      HodgeLieGeneration.castMatrix K ResponseClosureCertificate.hodge := by
  change HodgeLieGeneration.castMatrix K ResponseClosureGeometry.hodgeComplement = _
  rw [ResponseClosureGeometry.certificate_hodge]

/-- Covariance of a response on the 224-dimensional algebra under the sixteen
original geometric generators implies full adjoint covariance. -/
theorem covariant_of_generators (htwo : (2 : K) ≠ 0)
    (R : ResponseAlgebra K →ₗ[K] ResponseAlgebra K)
    (ha : ∀ p x, R ⁅adjointGenerator K p, x⁆ = ⁅adjointGenerator K p, R x⁆)
    (hh : ∀ x, R ⁅hodgeGenerator K, x⁆ = ⁅hodgeGenerator K, R x⁆) :
    ∀ a x : ResponseAlgebra K, R ⁅a, x⁆ = ⁅a, R x⁆ := by
  let C := covarianceSubalgebra R
  let M := C.map (LieAlgebra.SpecialLinear.sl (Fin 15) K).incl
  have hma : ∀ p, HodgeLieGeneration.castMatrix K
      (ResponseClosureCertificate.adj p) ∈ M := by
    intro p
    change ∃ b : ResponseAlgebra K, b ∈ C ∧
      (b : Matrix (Fin 15) (Fin 15) K) =
        HodgeLieGeneration.castMatrix K (ResponseClosureCertificate.adj p)
    exact ⟨adjointGenerator K p, ha p, coe_adjointGenerator K p⟩
  have hmh : HodgeLieGeneration.castMatrix K ResponseClosureCertificate.hodge ∈ M := by
    change ∃ b : ResponseAlgebra K, b ∈ C ∧
      (b : Matrix (Fin 15) (Fin 15) K) =
        HodgeLieGeneration.castMatrix K ResponseClosureCertificate.hodge
    exact ⟨hodgeGenerator K, hh, coe_hodgeGenerator K⟩
  have hle : LieAlgebra.SpecialLinear.sl (Fin 15) K ≤ M :=
    HodgeLieGeneration.tracefree_le K htwo M hma hmh
  intro a x
  have ham : (a : Matrix (Fin 15) (Fin 15) K) ∈ M := hle a.property
  change ∃ b : ResponseAlgebra K, b ∈ C ∧
    (b : Matrix (Fin 15) (Fin 15) K) = (a : Matrix (Fin 15) (Fin 15) K) at ham
  obtain ⟨b, hb, hba⟩ := ham
  have heq : b = a := Subtype.ext hba
  subst b
  exact hb x

/-- The full covariance assumption is equivalent to the finite list of
covariance assumptions on the displayed adjoint and Hodge generators. -/
theorem covariance_iff_generators (htwo : (2 : K) ≠ 0)
    (R : ResponseAlgebra K →ₗ[K] ResponseAlgebra K) :
    (∀ a x : ResponseAlgebra K, R ⁅a, x⁆ = ⁅a, R x⁆) ↔
      (∀ p x, R ⁅adjointGenerator K p, x⁆ = ⁅adjointGenerator K p, R x⁆) ∧
      (∀ x, R ⁅hodgeGenerator K, x⁆ = ⁅hodgeGenerator K, R x⁆) := by
  constructor
  · intro h
    exact ⟨fun p => h (adjointGenerator K p), h (hodgeGenerator K)⟩
  · rintro ⟨ha, hh⟩
    exact covariant_of_generators K htwo R ha hh

#print axioms covariant_of_mem_lieSpan
#print axioms covariant_of_generators
#print axioms covariance_iff_generators

end Geometric

end GravityScreening.HodgeResponseCovariance
