module
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Abel
public import Mathlib.LinearAlgebra.Matrix.Trace

@[expose] public section
/-!
# Exact structural certificate for adjoint-plus-local-Hodge generation

Ambient metric: diag(1,1,1,-1,1,-1). Bivector basis in lexicographic order:
01,02,03,04,05,12,13,14,15,23,24,25,34,35,45.

The generator tables are represented sparsely as integer matrix units. All
identities are checked by the Lean kernel, through algebraic simplification,
abelian-group normalization, and finite `decide +kernel` checks. There is no
external result oracle, native_decide, custom axiom, or unfinished proof.
-/

namespace GravityScreening.ResponseClosureCertificate
abbrev IMat := Matrix (Fin 15) (Fin 15) ℤ

def comm (A B : IMat) : IMat := A*B-B*A
def adj00 : IMat := (Matrix.single 1 5 (1 : ℤ)) + (Matrix.single 2 6 (1 : ℤ)) + (Matrix.single 3 7 (1 : ℤ)) + (Matrix.single 4 8 (1 : ℤ)) + -(Matrix.single 5 1 (1 : ℤ)) + -(Matrix.single 6 2 (1 : ℤ)) + -(Matrix.single 7 3 (1 : ℤ)) + -(Matrix.single 8 4 (1 : ℤ))
def adj01 : IMat := -(Matrix.single 0 5 (1 : ℤ)) + (Matrix.single 2 9 (1 : ℤ)) + (Matrix.single 3 10 (1 : ℤ)) + (Matrix.single 4 11 (1 : ℤ)) + (Matrix.single 5 0 (1 : ℤ)) + -(Matrix.single 9 2 (1 : ℤ)) + -(Matrix.single 10 3 (1 : ℤ)) + -(Matrix.single 11 4 (1 : ℤ))
def adj02 : IMat := (Matrix.single 0 6 (1 : ℤ)) + (Matrix.single 1 9 (1 : ℤ)) + -(Matrix.single 3 12 (1 : ℤ)) + -(Matrix.single 4 13 (1 : ℤ)) + (Matrix.single 6 0 (1 : ℤ)) + (Matrix.single 9 1 (1 : ℤ)) + -(Matrix.single 12 3 (1 : ℤ)) + -(Matrix.single 13 4 (1 : ℤ))
def adj03 : IMat := -(Matrix.single 0 7 (1 : ℤ)) + -(Matrix.single 1 10 (1 : ℤ)) + -(Matrix.single 2 12 (1 : ℤ)) + (Matrix.single 4 14 (1 : ℤ)) + (Matrix.single 7 0 (1 : ℤ)) + (Matrix.single 10 1 (1 : ℤ)) + (Matrix.single 12 2 (1 : ℤ)) + -(Matrix.single 14 4 (1 : ℤ))
def adj04 : IMat := (Matrix.single 0 8 (1 : ℤ)) + (Matrix.single 1 11 (1 : ℤ)) + (Matrix.single 2 13 (1 : ℤ)) + (Matrix.single 3 14 (1 : ℤ)) + (Matrix.single 8 0 (1 : ℤ)) + (Matrix.single 11 1 (1 : ℤ)) + (Matrix.single 13 2 (1 : ℤ)) + (Matrix.single 14 3 (1 : ℤ))
def adj05 : IMat := (Matrix.single 0 1 (1 : ℤ)) + -(Matrix.single 1 0 (1 : ℤ)) + (Matrix.single 6 9 (1 : ℤ)) + (Matrix.single 7 10 (1 : ℤ)) + (Matrix.single 8 11 (1 : ℤ)) + -(Matrix.single 9 6 (1 : ℤ)) + -(Matrix.single 10 7 (1 : ℤ)) + -(Matrix.single 11 8 (1 : ℤ))
def adj06 : IMat := -(Matrix.single 0 2 (1 : ℤ)) + -(Matrix.single 2 0 (1 : ℤ)) + (Matrix.single 5 9 (1 : ℤ)) + -(Matrix.single 7 12 (1 : ℤ)) + -(Matrix.single 8 13 (1 : ℤ)) + (Matrix.single 9 5 (1 : ℤ)) + -(Matrix.single 12 7 (1 : ℤ)) + -(Matrix.single 13 8 (1 : ℤ))
def adj07 : IMat := (Matrix.single 0 3 (1 : ℤ)) + -(Matrix.single 3 0 (1 : ℤ)) + -(Matrix.single 5 10 (1 : ℤ)) + -(Matrix.single 6 12 (1 : ℤ)) + (Matrix.single 8 14 (1 : ℤ)) + (Matrix.single 10 5 (1 : ℤ)) + (Matrix.single 12 6 (1 : ℤ)) + -(Matrix.single 14 8 (1 : ℤ))
def adj08 : IMat := -(Matrix.single 0 4 (1 : ℤ)) + -(Matrix.single 4 0 (1 : ℤ)) + (Matrix.single 5 11 (1 : ℤ)) + (Matrix.single 6 13 (1 : ℤ)) + (Matrix.single 7 14 (1 : ℤ)) + (Matrix.single 11 5 (1 : ℤ)) + (Matrix.single 13 6 (1 : ℤ)) + (Matrix.single 14 7 (1 : ℤ))
def adj09 : IMat := -(Matrix.single 1 2 (1 : ℤ)) + -(Matrix.single 2 1 (1 : ℤ)) + -(Matrix.single 5 6 (1 : ℤ)) + -(Matrix.single 6 5 (1 : ℤ)) + -(Matrix.single 10 12 (1 : ℤ)) + -(Matrix.single 11 13 (1 : ℤ)) + -(Matrix.single 12 10 (1 : ℤ)) + -(Matrix.single 13 11 (1 : ℤ))
def adj10 : IMat := (Matrix.single 1 3 (1 : ℤ)) + -(Matrix.single 3 1 (1 : ℤ)) + (Matrix.single 5 7 (1 : ℤ)) + -(Matrix.single 7 5 (1 : ℤ)) + -(Matrix.single 9 12 (1 : ℤ)) + (Matrix.single 11 14 (1 : ℤ)) + (Matrix.single 12 9 (1 : ℤ)) + -(Matrix.single 14 11 (1 : ℤ))
def adj11 : IMat := -(Matrix.single 1 4 (1 : ℤ)) + -(Matrix.single 4 1 (1 : ℤ)) + -(Matrix.single 5 8 (1 : ℤ)) + -(Matrix.single 8 5 (1 : ℤ)) + (Matrix.single 9 13 (1 : ℤ)) + (Matrix.single 10 14 (1 : ℤ)) + (Matrix.single 13 9 (1 : ℤ)) + (Matrix.single 14 10 (1 : ℤ))
def adj12 : IMat := (Matrix.single 2 3 (1 : ℤ)) + (Matrix.single 3 2 (1 : ℤ)) + (Matrix.single 6 7 (1 : ℤ)) + (Matrix.single 7 6 (1 : ℤ)) + (Matrix.single 9 10 (1 : ℤ)) + (Matrix.single 10 9 (1 : ℤ)) + (Matrix.single 13 14 (1 : ℤ)) + (Matrix.single 14 13 (1 : ℤ))
def adj13 : IMat := -(Matrix.single 2 4 (1 : ℤ)) + (Matrix.single 4 2 (1 : ℤ)) + -(Matrix.single 6 8 (1 : ℤ)) + (Matrix.single 8 6 (1 : ℤ)) + -(Matrix.single 9 11 (1 : ℤ)) + (Matrix.single 11 9 (1 : ℤ)) + (Matrix.single 12 14 (1 : ℤ)) + -(Matrix.single 14 12 (1 : ℤ))
def adj14 : IMat := -(Matrix.single 3 4 (1 : ℤ)) + -(Matrix.single 4 3 (1 : ℤ)) + -(Matrix.single 7 8 (1 : ℤ)) + -(Matrix.single 8 7 (1 : ℤ)) + -(Matrix.single 10 11 (1 : ℤ)) + -(Matrix.single 11 10 (1 : ℤ)) + -(Matrix.single 12 13 (1 : ℤ)) + -(Matrix.single 13 12 (1 : ℤ))
def jordan00 : IMat := -(Matrix.single 9 14 (1 : ℤ)) + -(Matrix.single 10 13 (1 : ℤ)) + -(Matrix.single 11 12 (1 : ℤ)) + -(Matrix.single 12 11 (1 : ℤ)) + -(Matrix.single 13 10 (1 : ℤ)) + -(Matrix.single 14 9 (1 : ℤ))
def jordan01 : IMat := (Matrix.single 6 14 (1 : ℤ)) + (Matrix.single 7 13 (1 : ℤ)) + (Matrix.single 8 12 (1 : ℤ)) + (Matrix.single 12 8 (1 : ℤ)) + (Matrix.single 13 7 (1 : ℤ)) + (Matrix.single 14 6 (1 : ℤ))
def jordan02 : IMat := (Matrix.single 5 14 (1 : ℤ)) + -(Matrix.single 7 11 (1 : ℤ)) + -(Matrix.single 8 10 (1 : ℤ)) + (Matrix.single 10 8 (1 : ℤ)) + (Matrix.single 11 7 (1 : ℤ)) + -(Matrix.single 14 5 (1 : ℤ))
def jordan03 : IMat := -(Matrix.single 5 13 (1 : ℤ)) + -(Matrix.single 6 11 (1 : ℤ)) + (Matrix.single 8 9 (1 : ℤ)) + (Matrix.single 9 8 (1 : ℤ)) + -(Matrix.single 11 6 (1 : ℤ)) + -(Matrix.single 13 5 (1 : ℤ))
def jordan04 : IMat := (Matrix.single 5 12 (1 : ℤ)) + (Matrix.single 6 10 (1 : ℤ)) + (Matrix.single 7 9 (1 : ℤ)) + -(Matrix.single 9 7 (1 : ℤ)) + -(Matrix.single 10 6 (1 : ℤ)) + -(Matrix.single 12 5 (1 : ℤ))
def jordan05 : IMat := -(Matrix.single 2 14 (1 : ℤ)) + -(Matrix.single 3 13 (1 : ℤ)) + -(Matrix.single 4 12 (1 : ℤ)) + -(Matrix.single 12 4 (1 : ℤ)) + -(Matrix.single 13 3 (1 : ℤ)) + -(Matrix.single 14 2 (1 : ℤ))
def jordan06 : IMat := -(Matrix.single 1 14 (1 : ℤ)) + (Matrix.single 3 11 (1 : ℤ)) + (Matrix.single 4 10 (1 : ℤ)) + -(Matrix.single 10 4 (1 : ℤ)) + -(Matrix.single 11 3 (1 : ℤ)) + (Matrix.single 14 1 (1 : ℤ))
def jordan07 : IMat := (Matrix.single 1 13 (1 : ℤ)) + (Matrix.single 2 11 (1 : ℤ)) + -(Matrix.single 4 9 (1 : ℤ)) + -(Matrix.single 9 4 (1 : ℤ)) + (Matrix.single 11 2 (1 : ℤ)) + (Matrix.single 13 1 (1 : ℤ))
def jordan08 : IMat := -(Matrix.single 1 12 (1 : ℤ)) + -(Matrix.single 2 10 (1 : ℤ)) + -(Matrix.single 3 9 (1 : ℤ)) + (Matrix.single 9 3 (1 : ℤ)) + (Matrix.single 10 2 (1 : ℤ)) + (Matrix.single 12 1 (1 : ℤ))
def jordan09 : IMat := (Matrix.single 0 14 (1 : ℤ)) + -(Matrix.single 3 8 (1 : ℤ)) + -(Matrix.single 4 7 (1 : ℤ)) + (Matrix.single 7 4 (1 : ℤ)) + (Matrix.single 8 3 (1 : ℤ)) + -(Matrix.single 14 0 (1 : ℤ))
def jordan10 : IMat := -(Matrix.single 0 13 (1 : ℤ)) + -(Matrix.single 2 8 (1 : ℤ)) + (Matrix.single 4 6 (1 : ℤ)) + (Matrix.single 6 4 (1 : ℤ)) + -(Matrix.single 8 2 (1 : ℤ)) + -(Matrix.single 13 0 (1 : ℤ))
def jordan11 : IMat := (Matrix.single 0 12 (1 : ℤ)) + (Matrix.single 2 7 (1 : ℤ)) + (Matrix.single 3 6 (1 : ℤ)) + -(Matrix.single 6 3 (1 : ℤ)) + -(Matrix.single 7 2 (1 : ℤ)) + -(Matrix.single 12 0 (1 : ℤ))
def jordan12 : IMat := (Matrix.single 0 11 (1 : ℤ)) + -(Matrix.single 1 8 (1 : ℤ)) + -(Matrix.single 4 5 (1 : ℤ)) + (Matrix.single 5 4 (1 : ℤ)) + (Matrix.single 8 1 (1 : ℤ)) + -(Matrix.single 11 0 (1 : ℤ))
def jordan13 : IMat := -(Matrix.single 0 10 (1 : ℤ)) + (Matrix.single 1 7 (1 : ℤ)) + -(Matrix.single 3 5 (1 : ℤ)) + -(Matrix.single 5 3 (1 : ℤ)) + (Matrix.single 7 1 (1 : ℤ)) + -(Matrix.single 10 0 (1 : ℤ))
def jordan14 : IMat := (Matrix.single 0 9 (1 : ℤ)) + -(Matrix.single 1 6 (1 : ℤ)) + -(Matrix.single 2 5 (1 : ℤ)) + (Matrix.single 5 2 (1 : ℤ)) + (Matrix.single 6 1 (1 : ℤ)) + -(Matrix.single 9 0 (1 : ℤ))
def adj : Fin 15 → IMat := ![adj00, adj01, adj02, adj03, adj04, adj05, adj06, adj07, adj08, adj09, adj10, adj11, adj12, adj13, adj14]
def jordan : Fin 15 → IMat := ![jordan00, jordan01, jordan02, jordan03, jordan04, jordan05, jordan06, jordan07, jordan08, jordan09, jordan10, jordan11, jordan12, jordan13, jordan14]
def hodge : IMat := -(Matrix.single 0 9 (1 : ℤ)) + (Matrix.single 1 6 (1 : ℤ)) + (Matrix.single 2 5 (1 : ℤ)) + -(Matrix.single 5 2 (1 : ℤ)) + -(Matrix.single 6 1 (1 : ℤ)) + (Matrix.single 9 0 (1 : ℤ))
def q : Fin 15 → ℤ := ![1, 1, -1, 1, -1, 1, -1, 1, -1, -1, 1, -1, -1, 1, -1]
def skew (i j : Fin 15) : IMat :=
  Matrix.single i j (q j) - Matrix.single j i (q i)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

def sym (i j : Fin 15) : IMat :=
  Matrix.single i j (q j) + Matrix.single j i (q i)

theorem hodge_eq_neg_jordan14 : hodge = -jordan 14 := by
  simp [skew, sym, q, comm, adj, jordan, hodge, adj00, adj01, adj02, adj03, adj04, adj05, adj06, adj07, adj08, adj09, adj10, adj11, adj12, adj13, adj14, jordan00, jordan01, jordan02, jordan03, jordan04, jordan05, jordan06, jordan07, jordan08, jordan09, jordan10, jordan11, jordan12, jordan13, jordan14, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, ← Matrix.single_neg] <;> abel

theorem jordan_recipe_04 : jordan 4 = comm (adj 3) (jordan 14) := by
  simp [skew, sym, q, comm, adj, jordan, hodge, adj00, adj01, adj02, adj03, adj04, adj05, adj06, adj07, adj08, adj09, adj10, adj11, adj12, adj13, adj14, jordan00, jordan01, jordan02, jordan03, jordan04, jordan05, jordan06, jordan07, jordan08, jordan09, jordan10, jordan11, jordan12, jordan13, jordan14, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, ← Matrix.single_neg] <;> abel

theorem jordan_recipe_03 : jordan 3 = comm (adj 4) (jordan 14) := by
  simp [skew, sym, q, comm, adj, jordan, hodge, adj00, adj01, adj02, adj03, adj04, adj05, adj06, adj07, adj08, adj09, adj10, adj11, adj12, adj13, adj14, jordan00, jordan01, jordan02, jordan03, jordan04, jordan05, jordan06, jordan07, jordan08, jordan09, jordan10, jordan11, jordan12, jordan13, jordan14, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, ← Matrix.single_neg] <;> abel

theorem jordan_recipe_08 : jordan 8 = comm (adj 7) (jordan 14) := by
  simp [skew, sym, q, comm, adj, jordan, hodge, adj00, adj01, adj02, adj03, adj04, adj05, adj06, adj07, adj08, adj09, adj10, adj11, adj12, adj13, adj14, jordan00, jordan01, jordan02, jordan03, jordan04, jordan05, jordan06, jordan07, jordan08, jordan09, jordan10, jordan11, jordan12, jordan13, jordan14, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, ← Matrix.single_neg] <;> abel

theorem jordan_recipe_07 : jordan 7 = comm (adj 8) (jordan 14) := by
  simp [skew, sym, q, comm, adj, jordan, hodge, adj00, adj01, adj02, adj03, adj04, adj05, adj06, adj07, adj08, adj09, adj10, adj11, adj12, adj13, adj14, jordan00, jordan01, jordan02, jordan03, jordan04, jordan05, jordan06, jordan07, jordan08, jordan09, jordan10, jordan11, jordan12, jordan13, jordan14, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, ← Matrix.single_neg] <;> abel

theorem jordan_recipe_11 : jordan 11 = comm (adj 10) (jordan 14) := by
  simp [skew, sym, q, comm, adj, jordan, hodge, adj00, adj01, adj02, adj03, adj04, adj05, adj06, adj07, adj08, adj09, adj10, adj11, adj12, adj13, adj14, jordan00, jordan01, jordan02, jordan03, jordan04, jordan05, jordan06, jordan07, jordan08, jordan09, jordan10, jordan11, jordan12, jordan13, jordan14, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, ← Matrix.single_neg] <;> abel

theorem jordan_recipe_10 : jordan 10 = comm (adj 11) (jordan 14) := by
  simp [skew, sym, q, comm, adj, jordan, hodge, adj00, adj01, adj02, adj03, adj04, adj05, adj06, adj07, adj08, adj09, adj10, adj11, adj12, adj13, adj14, jordan00, jordan01, jordan02, jordan03, jordan04, jordan05, jordan06, jordan07, jordan08, jordan09, jordan10, jordan11, jordan12, jordan13, jordan14, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, ← Matrix.single_neg] <;> abel

theorem jordan_recipe_13 : jordan 13 = comm (adj 12) (jordan 14) := by
  simp [skew, sym, q, comm, adj, jordan, hodge, adj00, adj01, adj02, adj03, adj04, adj05, adj06, adj07, adj08, adj09, adj10, adj11, adj12, adj13, adj14, jordan00, jordan01, jordan02, jordan03, jordan04, jordan05, jordan06, jordan07, jordan08, jordan09, jordan10, jordan11, jordan12, jordan13, jordan14, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, ← Matrix.single_neg] <;> abel

theorem jordan_recipe_12 : jordan 12 = comm (adj 13) (jordan 14) := by
  simp [skew, sym, q, comm, adj, jordan, hodge, adj00, adj01, adj02, adj03, adj04, adj05, adj06, adj07, adj08, adj09, adj10, adj11, adj12, adj13, adj14, jordan00, jordan01, jordan02, jordan03, jordan04, jordan05, jordan06, jordan07, jordan08, jordan09, jordan10, jordan11, jordan12, jordan13, jordan14, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, ← Matrix.single_neg] <;> abel

theorem jordan_recipe_00 : jordan 0 = -(comm (adj 8) (jordan 4)) := by
  simp [skew, sym, q, comm, adj, jordan, hodge, adj00, adj01, adj02, adj03, adj04, adj05, adj06, adj07, adj08, adj09, adj10, adj11, adj12, adj13, adj14, jordan00, jordan01, jordan02, jordan03, jordan04, jordan05, jordan06, jordan07, jordan08, jordan09, jordan10, jordan11, jordan12, jordan13, jordan14, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, ← Matrix.single_neg] <;> abel

theorem jordan_recipe_01 : jordan 1 = -(comm (adj 11) (jordan 4)) := by
  simp [skew, sym, q, comm, adj, jordan, hodge, adj00, adj01, adj02, adj03, adj04, adj05, adj06, adj07, adj08, adj09, adj10, adj11, adj12, adj13, adj14, jordan00, jordan01, jordan02, jordan03, jordan04, jordan05, jordan06, jordan07, jordan08, jordan09, jordan10, jordan11, jordan12, jordan13, jordan14, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, ← Matrix.single_neg] <;> abel

theorem jordan_recipe_02 : jordan 2 = -(comm (adj 13) (jordan 4)) := by
  simp [skew, sym, q, comm, adj, jordan, hodge, adj00, adj01, adj02, adj03, adj04, adj05, adj06, adj07, adj08, adj09, adj10, adj11, adj12, adj13, adj14, jordan00, jordan01, jordan02, jordan03, jordan04, jordan05, jordan06, jordan07, jordan08, jordan09, jordan10, jordan11, jordan12, jordan13, jordan14, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, ← Matrix.single_neg] <;> abel

theorem jordan_recipe_05 : jordan 5 = -(comm (adj 11) (jordan 8)) := by
  simp [skew, sym, q, comm, adj, jordan, hodge, adj00, adj01, adj02, adj03, adj04, adj05, adj06, adj07, adj08, adj09, adj10, adj11, adj12, adj13, adj14, jordan00, jordan01, jordan02, jordan03, jordan04, jordan05, jordan06, jordan07, jordan08, jordan09, jordan10, jordan11, jordan12, jordan13, jordan14, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, ← Matrix.single_neg] <;> abel

theorem jordan_recipe_06 : jordan 6 = -(comm (adj 13) (jordan 8)) := by
  simp [skew, sym, q, comm, adj, jordan, hodge, adj00, adj01, adj02, adj03, adj04, adj05, adj06, adj07, adj08, adj09, adj10, adj11, adj12, adj13, adj14, jordan00, jordan01, jordan02, jordan03, jordan04, jordan05, jordan06, jordan07, jordan08, jordan09, jordan10, jordan11, jordan12, jordan13, jordan14, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, ← Matrix.single_neg] <;> abel

theorem jordan_recipe_09 : jordan 9 = -(comm (adj 13) (jordan 11)) := by
  simp [skew, sym, q, comm, adj, jordan, hodge, adj00, adj01, adj02, adj03, adj04, adj05, adj06, adj07, adj08, adj09, adj10, adj11, adj12, adj13, adj14, jordan00, jordan01, jordan02, jordan03, jordan04, jordan05, jordan06, jordan07, jordan08, jordan09, jordan10, jordan11, jordan12, jordan13, jordan14, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, ← Matrix.single_neg] <;> abel

private theorem skew_upper_row_00 :
    ∀ j : Fin 15, (0 : Fin 15) < j →
      skew 0 j = -(comm (jordan 0) (jordan j)) - comm (adj 0) (adj j) := by
  intro j hij
  fin_cases j <;> simp_all [skew, sym, q, comm, adj, jordan, hodge, adj00, adj01, adj02, adj03, adj04, adj05, adj06, adj07, adj08, adj09, adj10, adj11, adj12, adj13, adj14, jordan00, jordan01, jordan02, jordan03, jordan04, jordan05, jordan06, jordan07, jordan08, jordan09, jordan10, jordan11, jordan12, jordan13, jordan14, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, ← Matrix.single_neg] <;> abel

private theorem skew_upper_row_01 :
    ∀ j : Fin 15, (1 : Fin 15) < j →
      skew 1 j = -(comm (jordan 1) (jordan j)) - comm (adj 1) (adj j) := by
  intro j hij
  fin_cases j <;> simp_all [skew, sym, q, comm, adj, jordan, hodge, adj00, adj01, adj02, adj03, adj04, adj05, adj06, adj07, adj08, adj09, adj10, adj11, adj12, adj13, adj14, jordan00, jordan01, jordan02, jordan03, jordan04, jordan05, jordan06, jordan07, jordan08, jordan09, jordan10, jordan11, jordan12, jordan13, jordan14, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, ← Matrix.single_neg] <;> abel

private theorem skew_upper_row_02 :
    ∀ j : Fin 15, (2 : Fin 15) < j →
      skew 2 j = -(comm (jordan 2) (jordan j)) - comm (adj 2) (adj j) := by
  intro j hij
  fin_cases j <;> simp_all [skew, sym, q, comm, adj, jordan, hodge, adj00, adj01, adj02, adj03, adj04, adj05, adj06, adj07, adj08, adj09, adj10, adj11, adj12, adj13, adj14, jordan00, jordan01, jordan02, jordan03, jordan04, jordan05, jordan06, jordan07, jordan08, jordan09, jordan10, jordan11, jordan12, jordan13, jordan14, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, ← Matrix.single_neg] <;> abel

private theorem skew_upper_row_03 :
    ∀ j : Fin 15, (3 : Fin 15) < j →
      skew 3 j = -(comm (jordan 3) (jordan j)) - comm (adj 3) (adj j) := by
  intro j hij
  fin_cases j <;> simp_all [skew, sym, q, comm, adj, jordan, hodge, adj00, adj01, adj02, adj03, adj04, adj05, adj06, adj07, adj08, adj09, adj10, adj11, adj12, adj13, adj14, jordan00, jordan01, jordan02, jordan03, jordan04, jordan05, jordan06, jordan07, jordan08, jordan09, jordan10, jordan11, jordan12, jordan13, jordan14, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, ← Matrix.single_neg] <;> abel

private theorem skew_upper_row_04 :
    ∀ j : Fin 15, (4 : Fin 15) < j →
      skew 4 j = -(comm (jordan 4) (jordan j)) - comm (adj 4) (adj j) := by
  intro j hij
  fin_cases j <;> simp_all [skew, sym, q, comm, adj, jordan, hodge, adj00, adj01, adj02, adj03, adj04, adj05, adj06, adj07, adj08, adj09, adj10, adj11, adj12, adj13, adj14, jordan00, jordan01, jordan02, jordan03, jordan04, jordan05, jordan06, jordan07, jordan08, jordan09, jordan10, jordan11, jordan12, jordan13, jordan14, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, ← Matrix.single_neg] <;> abel

private theorem skew_upper_row_05 :
    ∀ j : Fin 15, (5 : Fin 15) < j →
      skew 5 j = -(comm (jordan 5) (jordan j)) - comm (adj 5) (adj j) := by
  intro j hij
  fin_cases j <;> simp_all [skew, sym, q, comm, adj, jordan, hodge, adj00, adj01, adj02, adj03, adj04, adj05, adj06, adj07, adj08, adj09, adj10, adj11, adj12, adj13, adj14, jordan00, jordan01, jordan02, jordan03, jordan04, jordan05, jordan06, jordan07, jordan08, jordan09, jordan10, jordan11, jordan12, jordan13, jordan14, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, ← Matrix.single_neg] <;> abel

private theorem skew_upper_row_06 :
    ∀ j : Fin 15, (6 : Fin 15) < j →
      skew 6 j = -(comm (jordan 6) (jordan j)) - comm (adj 6) (adj j) := by
  intro j hij
  fin_cases j <;> simp_all [skew, sym, q, comm, adj, jordan, hodge, adj00, adj01, adj02, adj03, adj04, adj05, adj06, adj07, adj08, adj09, adj10, adj11, adj12, adj13, adj14, jordan00, jordan01, jordan02, jordan03, jordan04, jordan05, jordan06, jordan07, jordan08, jordan09, jordan10, jordan11, jordan12, jordan13, jordan14, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, ← Matrix.single_neg] <;> abel

private theorem skew_upper_row_07 :
    ∀ j : Fin 15, (7 : Fin 15) < j →
      skew 7 j = -(comm (jordan 7) (jordan j)) - comm (adj 7) (adj j) := by
  intro j hij
  fin_cases j <;> simp_all [skew, sym, q, comm, adj, jordan, hodge, adj00, adj01, adj02, adj03, adj04, adj05, adj06, adj07, adj08, adj09, adj10, adj11, adj12, adj13, adj14, jordan00, jordan01, jordan02, jordan03, jordan04, jordan05, jordan06, jordan07, jordan08, jordan09, jordan10, jordan11, jordan12, jordan13, jordan14, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, ← Matrix.single_neg] <;> abel

private theorem skew_upper_row_08 :
    ∀ j : Fin 15, (8 : Fin 15) < j →
      skew 8 j = -(comm (jordan 8) (jordan j)) - comm (adj 8) (adj j) := by
  intro j hij
  fin_cases j <;> simp_all [skew, sym, q, comm, adj, jordan, hodge, adj00, adj01, adj02, adj03, adj04, adj05, adj06, adj07, adj08, adj09, adj10, adj11, adj12, adj13, adj14, jordan00, jordan01, jordan02, jordan03, jordan04, jordan05, jordan06, jordan07, jordan08, jordan09, jordan10, jordan11, jordan12, jordan13, jordan14, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, ← Matrix.single_neg] <;> abel

private theorem skew_upper_row_09 :
    ∀ j : Fin 15, (9 : Fin 15) < j →
      skew 9 j = -(comm (jordan 9) (jordan j)) - comm (adj 9) (adj j) := by
  intro j hij
  fin_cases j <;> simp_all [skew, sym, q, comm, adj, jordan, hodge, adj00, adj01, adj02, adj03, adj04, adj05, adj06, adj07, adj08, adj09, adj10, adj11, adj12, adj13, adj14, jordan00, jordan01, jordan02, jordan03, jordan04, jordan05, jordan06, jordan07, jordan08, jordan09, jordan10, jordan11, jordan12, jordan13, jordan14, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, ← Matrix.single_neg] <;> abel

private theorem skew_upper_row_10 :
    ∀ j : Fin 15, (10 : Fin 15) < j →
      skew 10 j = -(comm (jordan 10) (jordan j)) - comm (adj 10) (adj j) := by
  intro j hij
  fin_cases j <;> simp_all [skew, sym, q, comm, adj, jordan, hodge, adj00, adj01, adj02, adj03, adj04, adj05, adj06, adj07, adj08, adj09, adj10, adj11, adj12, adj13, adj14, jordan00, jordan01, jordan02, jordan03, jordan04, jordan05, jordan06, jordan07, jordan08, jordan09, jordan10, jordan11, jordan12, jordan13, jordan14, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, ← Matrix.single_neg] <;> abel

private theorem skew_upper_row_11 :
    ∀ j : Fin 15, (11 : Fin 15) < j →
      skew 11 j = -(comm (jordan 11) (jordan j)) - comm (adj 11) (adj j) := by
  intro j hij
  fin_cases j <;> simp_all [skew, sym, q, comm, adj, jordan, hodge, adj00, adj01, adj02, adj03, adj04, adj05, adj06, adj07, adj08, adj09, adj10, adj11, adj12, adj13, adj14, jordan00, jordan01, jordan02, jordan03, jordan04, jordan05, jordan06, jordan07, jordan08, jordan09, jordan10, jordan11, jordan12, jordan13, jordan14, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, ← Matrix.single_neg] <;> abel

private theorem skew_upper_row_12 :
    ∀ j : Fin 15, (12 : Fin 15) < j →
      skew 12 j = -(comm (jordan 12) (jordan j)) - comm (adj 12) (adj j) := by
  intro j hij
  fin_cases j <;> simp_all [skew, sym, q, comm, adj, jordan, hodge, adj00, adj01, adj02, adj03, adj04, adj05, adj06, adj07, adj08, adj09, adj10, adj11, adj12, adj13, adj14, jordan00, jordan01, jordan02, jordan03, jordan04, jordan05, jordan06, jordan07, jordan08, jordan09, jordan10, jordan11, jordan12, jordan13, jordan14, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, ← Matrix.single_neg] <;> abel

private theorem skew_upper_row_13 :
    ∀ j : Fin 15, (13 : Fin 15) < j →
      skew 13 j = -(comm (jordan 13) (jordan j)) - comm (adj 13) (adj j) := by
  intro j hij
  fin_cases j <;> simp_all [skew, sym, q, comm, adj, jordan, hodge, adj00, adj01, adj02, adj03, adj04, adj05, adj06, adj07, adj08, adj09, adj10, adj11, adj12, adj13, adj14, jordan00, jordan01, jordan02, jordan03, jordan04, jordan05, jordan06, jordan07, jordan08, jordan09, jordan10, jordan11, jordan12, jordan13, jordan14, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, ← Matrix.single_neg] <;> abel

private theorem skew_upper_row_14 :
    ∀ j : Fin 15, (14 : Fin 15) < j →
      skew 14 j = -(comm (jordan 14) (jordan j)) - comm (adj 14) (adj j) := by
  intro j hij
  fin_cases j <;> simp_all [skew, sym, q, comm, adj, jordan, hodge, adj00, adj01, adj02, adj03, adj04, adj05, adj06, adj07, adj08, adj09, adj10, adj11, adj12, adj13, adj14, jordan00, jordan01, jordan02, jordan03, jordan04, jordan05, jordan06, jordan07, jordan08, jordan09, jordan10, jordan11, jordan12, jordan13, jordan14, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, ← Matrix.single_neg] <;> abel

private theorem skew_upper (i j : Fin 15) (h : i < j) :
    skew i j = -(comm (jordan i) (jordan j)) - comm (adj i) (adj j) := by
  fin_cases i
  · exact skew_upper_row_00 j h
  · exact skew_upper_row_01 j h
  · exact skew_upper_row_02 j h
  · exact skew_upper_row_03 j h
  · exact skew_upper_row_04 j h
  · exact skew_upper_row_05 j h
  · exact skew_upper_row_06 j h
  · exact skew_upper_row_07 j h
  · exact skew_upper_row_08 j h
  · exact skew_upper_row_09 j h
  · exact skew_upper_row_10 j h
  · exact skew_upper_row_11 j h
  · exact skew_upper_row_12 j h
  · exact skew_upper_row_13 j h
  · exact skew_upper_row_14 j h

theorem skew_identity (i j : Fin 15) :
    skew i j = -(comm (jordan i) (jordan j)) - comm (adj i) (adj j) := by
  rcases lt_trichotomy i j with h | h | h
  · exact skew_upper i j h
  · subst j
    simp [skew, comm]
  · calc
      skew i j = -skew j i := by simp [skew]
      _ = -(-(comm (jordan j) (jordan i)) - comm (adj j) (adj i)) :=
        congrArg Neg.neg (skew_upper j i h)
      _ = -(comm (jordan i) (jordan j)) - comm (adj i) (adj j) := by
        unfold comm
        abel

theorem extraction_identity : sym 3 9 = comm (skew 3 0) hodge := by
  simp [skew, sym, q, comm, adj, jordan, hodge, adj00, adj01, adj02, adj03, adj04, adj05, adj06, adj07, adj08, adj09, adj10, adj11, adj12, adj13, adj14, jordan00, jordan01, jordan02, jordan03, jordan04, jordan05, jordan06, jordan07, jordan08, jordan09, jordan10, jordan11, jordan12, jordan13, jordan14, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, ← Matrix.single_neg] <;> abel

theorem q_sq (i : Fin 15) : q i * q i = 1 := by
  revert i
  decide +kernel

theorem adj_trace_zero (i : Fin 15) : Matrix.trace (adj i) = 0 := by
  revert i
  decide +kernel

theorem hodge_trace_zero : Matrix.trace hodge = 0 := by
  decide +kernel

#print axioms hodge_eq_neg_jordan14
#print axioms jordan_recipe_03
#print axioms skew_identity
#print axioms extraction_identity
#print axioms adj_trace_zero
#print axioms hodge_trace_zero
end GravityScreening.ResponseClosureCertificate
