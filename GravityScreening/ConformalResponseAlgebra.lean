module
public import GravityScreening.ConformalGeneratorCount

@[expose] public section

/-!
# The trace-free response algebra on the conformal generator space

This file works directly on the real vector space underlying Mathlib's
`so'(4,2)`.  Its trace-free endomorphisms form a 224-dimensional response
space.  Evaluation at any nonzero conformal generator is surjective, with a
209-dimensional kernel, so rank--nullity gives `224 = 15 + 209` on the actual
conformal generator space.

The mathematics does not assert that gravity must select this full response
space.  That selection is a separate PDT physical identification.
-/

namespace GravityScreening

noncomputable section

open Module
open scoped Matrix

/-! A field-generic coordinate solver used to prove surjectivity after choosing
a basis. -/

namespace TraceFreeMatrixSolver

variable {K : Type*} [Field K] {N : ℕ}

def actionMap (v : Fin N → K) :
    Matrix (Fin N) (Fin N) K →ₗ[K] (Fin N → K) where
  toFun X := X *ᵥ v
  map_add' X Y := Matrix.add_mulVec X Y v
  map_smul' c X := Matrix.smul_mulVec c X v

def traceFree (N : ℕ) : Submodule K (Matrix (Fin N) (Fin N) K) :=
  LinearMap.ker (Matrix.traceLinearMap (Fin N) K K)

def action (v : Fin N → K) : traceFree (K := K) N →ₗ[K] (Fin N → K) :=
  (actionMap v).comp (traceFree (K := K) N).subtype

def columnSolver (v w : Fin N → K) (i : Fin N) :
    Matrix (Fin N) (Fin N) K :=
  Matrix.of fun k l => if l = i then w k / v i else 0

lemma columnSolver_mulVec (v w : Fin N → K) (i : Fin N) (hi : v i ≠ 0) :
    columnSolver v w i *ᵥ v = w := by
  funext k
  simp only [columnSolver, Matrix.mulVec, dotProduct, Matrix.of_apply, ite_mul,
    zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact div_mul_cancel₀ (w k) hi

lemma trace_columnSolver (v w : Fin N → K) (i : Fin N) :
    (columnSolver v w i).trace = w i / v i := by
  simp only [columnSolver, Matrix.trace, Matrix.diag, Matrix.of_apply,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

def traceFixer (v : Fin N → K) (i j : Fin N) :
    Matrix (Fin N) (Fin N) K :=
  Matrix.single j j 1 - Matrix.single j i (v j / v i)

lemma traceFixer_mulVec (v : Fin N → K) (i j : Fin N) (hi : v i ≠ 0) :
    traceFixer v i j *ᵥ v = 0 := by
  rw [traceFixer, Matrix.sub_mulVec, Matrix.single_mulVec,
    Matrix.single_mulVec, one_mul, div_mul_cancel₀ _ hi, sub_self]

lemma trace_traceFixer (v : Fin N → K) (i j : Fin N) (hij : j ≠ i) :
    (traceFixer v i j).trace = 1 := by
  rw [traceFixer, Matrix.trace_sub, Matrix.trace_single_eq_same,
    Matrix.trace_single_eq_of_ne _ _ _ hij, sub_zero]

def solver (v w : Fin N → K) (i j : Fin N) :
    Matrix (Fin N) (Fin N) K :=
  columnSolver v w i - (w i / v i) • traceFixer v i j

lemma solver_mulVec (v w : Fin N → K) (i j : Fin N) (hi : v i ≠ 0) :
    solver v w i j *ᵥ v = w := by
  rw [solver, Matrix.sub_mulVec, Matrix.smul_mulVec,
    columnSolver_mulVec v w i hi, traceFixer_mulVec v i j hi,
    smul_zero, sub_zero]

lemma trace_solver (v w : Fin N → K) (i j : Fin N) (hij : j ≠ i) :
    (solver v w i j).trace = 0 := by
  rw [solver, Matrix.trace_sub, Matrix.trace_smul, trace_columnSolver,
    trace_traceFixer v i j hij, smul_eq_mul, mul_one, sub_self]

/-- For dimension at least two, trace-free endomorphisms can send any nonzero
vector to any target vector. -/
theorem action_surjective (hN : 2 ≤ N) {v : Fin N → K} (hv : v ≠ 0) :
    Function.Surjective (action v) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  simp only [Pi.zero_apply] at hi
  obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card
    (by rw [Fintype.card_fin]; omega) i
  intro w
  refine ⟨⟨solver v w i j, ?_⟩, ?_⟩
  · simp [traceFree, LinearMap.mem_ker, trace_solver v w i j hj]
  · exact solver_mulVec v w i j hi

end TraceFreeMatrixSolver

/-! The coordinate-free response space on `so'(4,2)`. -/

/-- The actual real vector space underlying Mathlib's `so'(4,2)`. -/
abbrev conformalGeneratorSpace := conformalLieAlgebra

/-- Trace-free endomorphisms of the conformal generator space. -/
def conformalResponseAlgebra :
    Submodule ℝ (Module.End ℝ conformalGeneratorSpace) :=
  LinearMap.ker (LinearMap.trace ℝ conformalGeneratorSpace)

/-- Evaluation of a trace-free response at a fixed conformal generator. -/
def conformalResponseAction (v : conformalGeneratorSpace) :
    conformalResponseAlgebra →ₗ[ℝ] conformalGeneratorSpace where
  toFun f := f.1 v
  map_add' f g := by simp
  map_smul' c f := by simp

/-- The responses that fix a chosen generator infinitesimally. -/
def conformalResponseStabilizer (v : conformalGeneratorSpace) :
    Submodule ℝ conformalResponseAlgebra :=
  LinearMap.ker (conformalResponseAction v)

/-- The response exponent is defined structurally as the dimension of the
trace-free endomorphisms of the conformal generator space. -/
def conformalResponseExponent : ℕ :=
  finrank ℝ conformalResponseAlgebra

private theorem conformalTrace_surjective :
    Function.Surjective (LinearMap.trace ℝ conformalGeneratorSpace) := by
  intro c
  refine ⟨(c / 15) • LinearMap.id, ?_⟩
  rw [map_smul, LinearMap.trace_id, finrank_conformalLieAlgebra]
  norm_num

/-- The trace-free endomorphisms of `so'(4,2)` have dimension 224. -/
theorem finrank_conformalResponseAlgebra :
    finrank ℝ conformalResponseAlgebra = 224 := by
  have h := LinearMap.finrank_range_add_finrank_ker
    (LinearMap.trace ℝ conformalGeneratorSpace)
  rw [LinearMap.range_eq_top.mpr conformalTrace_surjective, finrank_top,
    finrank_self, Module.finrank_linearMap, finrank_conformalLieAlgebra] at h
  change finrank ℝ conformalResponseAlgebra = 224
  unfold conformalResponseAlgebra
  norm_num at h
  have h' : 1 + finrank ℝ
      (LinearMap.ker (LinearMap.trace ℝ conformalGeneratorSpace)) = 1 + 224 := by
    simpa using h
  exact Nat.add_left_cancel h'

/-- The structurally defined response exponent evaluates to 224. -/
theorem conformalResponseExponent_eq_224 : conformalResponseExponent = 224 := by
  exact finrank_conformalResponseAlgebra

/-- Evaluation at every nonzero conformal generator is surjective. -/
theorem conformalResponseAction_surjective
    {v : conformalGeneratorSpace} (hv : v ≠ 0) :
    Function.Surjective (conformalResponseAction v) := by
  let b : Basis (Fin 15) ℝ conformalGeneratorSpace :=
    Module.finBasisOfFinrankEq ℝ conformalGeneratorSpace
      finrank_conformalLieAlgebra
  let vv : Fin 15 → ℝ := b.equivFun v
  have hvv : vv ≠ 0 := by
    intro h
    apply hv
    apply b.equivFun.injective
    simpa [vv] using h
  intro w
  let ww : Fin 15 → ℝ := b.equivFun w
  obtain ⟨M, hM⟩ := TraceFreeMatrixSolver.action_surjective
    (K := ℝ) (N := 15) (by norm_num) hvv ww
  let f : Module.End ℝ conformalGeneratorSpace := Matrix.toLin b b M.1
  have hftrace : LinearMap.trace ℝ conformalGeneratorSpace f = 0 := by
    rw [LinearMap.trace_eq_matrix_trace ℝ b]
    change (LinearMap.toMatrix b b (Matrix.toLin b b M.1)).trace = 0
    rw [LinearMap.toMatrix_toLin]
    exact M.2
  let F : conformalResponseAlgebra :=
    ⟨f, by simpa [conformalResponseAlgebra, LinearMap.mem_ker] using hftrace⟩
  refine ⟨F, ?_⟩
  apply b.equivFun.injective
  ext i
  change b.equivFun (f v) i = b.equivFun w i
  rw [b.equivFun_apply, b.equivFun_apply, Matrix.repr_toLin]
  exact congr_fun hM i

/-- The infinitesimal stabilizer at every nonzero generator has dimension
209. -/
theorem finrank_conformalResponseStabilizer
    {v : conformalGeneratorSpace} (hv : v ≠ 0) :
    finrank ℝ (conformalResponseStabilizer v) = 209 := by
  have h := LinearMap.finrank_range_add_finrank_ker (K := ℝ)
    (V := conformalResponseAlgebra) (V₂ := conformalGeneratorSpace)
    (conformalResponseAction v)
  rw [LinearMap.range_eq_top.mpr (conformalResponseAction_surjective hv),
    finrank_top, finrank_conformalLieAlgebra,
    finrank_conformalResponseAlgebra] at h
  change finrank ℝ (conformalResponseStabilizer v) = 209
  unfold conformalResponseStabilizer
  have h' : 15 + finrank ℝ
      (LinearMap.ker (conformalResponseAction v)) = 15 + 209 := by
    simpa using h
  exact Nat.add_left_cancel h'

/-- Rank--nullity on the actual conformal generator space gives
`224 = 15 + 209`. -/
theorem conformalResponse_orbit_stabilizer
    {v : conformalGeneratorSpace} (hv : v ≠ 0) :
    conformalResponseExponent =
      finrank ℝ conformalGeneratorSpace +
        finrank ℝ (conformalResponseStabilizer v) := by
  rw [conformalResponseExponent_eq_224, finrank_conformalLieAlgebra,
    finrank_conformalResponseStabilizer hv]

#print axioms GravityScreening.finrank_conformalResponseAlgebra
#print axioms GravityScreening.conformalResponseAction_surjective
#print axioms GravityScreening.finrank_conformalResponseStabilizer
#print axioms GravityScreening.conformalResponse_orbit_stabilizer

end

end GravityScreening
