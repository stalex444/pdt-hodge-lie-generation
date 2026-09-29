module
public import GravityScreening.SignedLieGeneration
public import ResponseClosureCertificate

@[expose] public section

/-! Constructive base change of the integral adjoint/Hodge Lie-generation
certificate. The field hypothesis is precisely that two is nonzero. -/

namespace GravityScreening.HodgeLieGeneration

open Matrix
open ResponseClosureCertificate
attribute [local instance] LieRing.ofAssociativeRing

variable (K : Type*) [Field K]

abbrev FMat := Matrix (Fin 15) (Fin 15) K

/-- Entrywise scalar extension of the integral operators. -/
def castMatrix : IMat →+* FMat K := (Int.castRingHom K).mapMatrix

lemma cast_comm (A B : IMat) :
    castMatrix K (comm A B) = ⁅castMatrix K A, castMatrix K B⁆ := by
  simp only [ResponseClosureCertificate.comm, Ring.lie_def, map_sub, map_mul]

def metricSigns (i : Fin 15) : K := (q i : K)

lemma cast_skew (i j : Fin 15) :
    castMatrix K (skew i j) = SignedLieGeneration.skew (metricSigns K) i j := by
  ext a b
  simp [castMatrix, skew, SignedLieGeneration.skew, metricSigns, Matrix.single]

lemma cast_sym (i j : Fin 15) :
    castMatrix K (sym i j) = SignedLieGeneration.sym (metricSigns K) i j := by
  ext a b
  simp [castMatrix, sym, SignedLieGeneration.sym, metricSigns, Matrix.single]

lemma metricSigns_sq (i : Fin 15) : metricSigns K i * metricSigns K i = 1 := by
  have h := congrArg (Int.castRingHom K) (q_sq i)
  simpa [metricSigns] using h

lemma metricSigns_ne_zero (i : Fin 15) : metricSigns K i ≠ 0 := by
  intro h
  have hh := metricSigns_sq K i
  rw [h, zero_mul] at hh
  exact zero_ne_one hh

/-- The Jordan operators are consequences of the specified adjoint and Hodge
operators; they are not additional generators. -/
theorem jordan_mem (L : LieSubalgebra K (FMat K))
    (ha : ∀ i, castMatrix K (adj i) ∈ L) (hh : castMatrix K hodge ∈ L) :
    ∀ i, castMatrix K (jordan i) ∈ L := by
  have h14 : castMatrix K (jordan 14) ∈ L := by
    have h := L.neg_mem hh
    change castMatrix K (jordan 14) ∈ L.toSubmodule
    simpa only [hodge_eq_neg_jordan14, map_neg, neg_neg] using h
  have h04 : castMatrix K (jordan 4) ∈ L := by
    rw [jordan_recipe_04, cast_comm]
    exact L.lie_mem (ha 3) h14
  have h03 : castMatrix K (jordan 3) ∈ L := by
    rw [jordan_recipe_03, cast_comm]
    exact L.lie_mem (ha 4) h14
  have h08 : castMatrix K (jordan 8) ∈ L := by
    rw [jordan_recipe_08, cast_comm]
    exact L.lie_mem (ha 7) h14
  have h07 : castMatrix K (jordan 7) ∈ L := by
    rw [jordan_recipe_07, cast_comm]
    exact L.lie_mem (ha 8) h14
  have h11 : castMatrix K (jordan 11) ∈ L := by
    rw [jordan_recipe_11, cast_comm]
    exact L.lie_mem (ha 10) h14
  have h10 : castMatrix K (jordan 10) ∈ L := by
    rw [jordan_recipe_10, cast_comm]
    exact L.lie_mem (ha 11) h14
  have h13 : castMatrix K (jordan 13) ∈ L := by
    rw [jordan_recipe_13, cast_comm]
    exact L.lie_mem (ha 12) h14
  have h12 : castMatrix K (jordan 12) ∈ L := by
    rw [jordan_recipe_12, cast_comm]
    exact L.lie_mem (ha 13) h14
  have h00 : castMatrix K (jordan 0) ∈ L := by
    rw [jordan_recipe_00, map_neg, cast_comm]
    exact L.neg_mem (L.lie_mem (ha 8) h04)
  have h01 : castMatrix K (jordan 1) ∈ L := by
    rw [jordan_recipe_01, map_neg, cast_comm]
    exact L.neg_mem (L.lie_mem (ha 11) h04)
  have h02 : castMatrix K (jordan 2) ∈ L := by
    rw [jordan_recipe_02, map_neg, cast_comm]
    exact L.neg_mem (L.lie_mem (ha 13) h04)
  have h05 : castMatrix K (jordan 5) ∈ L := by
    rw [jordan_recipe_05, map_neg, cast_comm]
    exact L.neg_mem (L.lie_mem (ha 11) h08)
  have h06 : castMatrix K (jordan 6) ∈ L := by
    rw [jordan_recipe_06, map_neg, cast_comm]
    exact L.neg_mem (L.lie_mem (ha 13) h08)
  have h09 : castMatrix K (jordan 9) ∈ L := by
    rw [jordan_recipe_09, map_neg, cast_comm]
    exact L.neg_mem (L.lie_mem (ha 13) h11)
  intro i
  fin_cases i
  · exact h00
  · exact h01
  · exact h02
  · exact h03
  · exact h04
  · exact h05
  · exact h06
  · exact h07
  · exact h08
  · exact h09
  · exact h10
  · exact h11
  · exact h12
  · exact h13
  · exact h14

/-- Every Lie subalgebra containing the specified sixteen operators contains
all trace-free endomorphisms. -/
theorem tracefree_le (htwo : (2 : K) ≠ 0)
    (L : LieSubalgebra K (FMat K))
    (ha : ∀ i, castMatrix K (adj i) ∈ L) (hh : castMatrix K hodge ∈ L) :
    LieAlgebra.SpecialLinear.sl (Fin 15) K ≤ L := by
  have hj := jordan_mem K L ha hh
  have hk : ∀ i j, SignedLieGeneration.skew (metricSigns K) i j ∈ L := by
    intro i j
    rw [← cast_skew, skew_identity, map_sub, map_neg, cast_comm, cast_comm]
    exact L.sub_mem (L.neg_mem (L.lie_mem (hj i) (hj j))) (L.lie_mem (ha i) (ha j))
  have hs : SignedLieGeneration.sym (metricSigns K) 3 9 ∈ L := by
    rw [← cast_sym, extraction_identity, cast_comm, cast_skew]
    exact L.lie_mem (hk 3 0) hh
  exact SignedLieGeneration.tracefree_le htwo (metricSigns K)
    (metricSigns_ne_zero K) L 3 9 (by decide) hk hs

/-- The specified operator set: all fifteen adjoint basis actions and the
single local Hodge extension. -/
def generators : Set (FMat K) := Set.range (fun i => castMatrix K (adj i)) ∪
  {castMatrix K hodge}

/-- The least Lie subalgebra containing the specified operators. -/
def generated : LieSubalgebra K (FMat K) :=
  LieSubalgebra.lieSpan K (FMat K) (generators K)

lemma cast_trace (A : IMat) : (castMatrix K A).trace = (A.trace : K) := by
  exact (AddMonoidHom.map_trace (Int.castRingHom K) A).symm

/-- Exact Lie generation over every field of characteristic different from two. -/
theorem generated_eq_sl (htwo : (2 : K) ≠ 0) :
    generated K = LieAlgebra.SpecialLinear.sl (Fin 15) K := by
  apply le_antisymm
  · apply LieSubalgebra.lieSpan_le.mpr
    intro M hM
    rcases hM with ⟨i, rfl⟩ | hM
    · change (castMatrix K (adj i)).trace = 0
      rw [cast_trace, adj_trace_zero, Int.cast_zero]
    · have heq : M = castMatrix K hodge := hM
      subst M
      change (castMatrix K hodge).trace = 0
      rw [cast_trace, hodge_trace_zero, Int.cast_zero]
  · apply tracefree_le K htwo (generated K)
    · intro i
      exact LieSubalgebra.subset_lieSpan (Or.inl ⟨i, rfl⟩)
    · exact LieSubalgebra.subset_lieSpan (Or.inr rfl)

/-- Dimension is a consequence of generation, not an input to the closure. -/
theorem finrank_generated (htwo : (2 : K) ≠ 0) :
    Module.finrank K (generated K) = 224 := by
  rw [generated_eq_sl K htwo]
  have h := SignedLieGeneration.finrank_sl_add_one (K := K) (0 : Fin 15)
  simp only [Fintype.card_fin] at h
  exact Nat.add_right_cancel (show _ + 1 = 224 + 1 from h)

#print axioms generated_eq_sl
#print axioms finrank_generated

end GravityScreening.HodgeLieGeneration
