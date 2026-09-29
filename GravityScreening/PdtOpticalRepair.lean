module
public import GravityScreening.PerronOpticalRaychaudhuri
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

/-!
# Orthogonal optical realization and finite-cut balance

The null rays below start on a quadratic cut, making their actual label
variations orthogonal to their affine tangents. A separate general real-
analysis theorem derives the finite-cut charge from optical evolution.

The flux uses the evolving screen area and the full shear-minus-expansion
density. None of these declarations identifies that geometric quantity with
the modular Hamiltonian of a physical quantum state, derives an entropy
density, or derives Newton's constant.
-/

namespace GravityScreening.OpticalRepair

noncomputable section

open scoped Matrix Interval
open MeasureTheory

abbrev Screen := Fin 2 → ℝ
abbrev Spacetime := Fin 4 → ℝ

def minkowskiPair (x y : Spacetime) : ℝ :=
  -x 0 * y 1 - x 1 * y 0 + x 2 * y 2 + x 3 * y 3

def jacobi (S : Matrix (Fin 2) (Fin 2) ℝ) (u : ℝ) :=
  (1 : Matrix (Fin 2) (Fin 2) ℝ) + u • S

/-- The quadratic initial v-coordinate is essential to orthogonality. -/
def orthogonalNullRay
    (S : Matrix (Fin 2) (Fin 2) ℝ) (y : Screen) (u : ℝ) : Spacetime :=
  let v := S.mulVec y
  ![u, (dotProduct y v + u * dotProduct v v) / 2,
    y 0 + u * v 0, y 1 + u * v 1]

def nullRayTangent
    (S : Matrix (Fin 2) (Fin 2) ℝ) (y : Screen) : Spacetime :=
  let v := S.mulVec y
  ![1, dotProduct v v / 2, v 0, v 1]

/-- This is the actual label derivative when S is symmetric, as proved below. -/
def screenVariation
    (S : Matrix (Fin 2) (Fin 2) ℝ) (y : Screen) (u : ℝ) (e : Screen) :
    Spacetime :=
  let v := S.mulVec y
  let w := S.mulVec e
  ![0, dotProduct e v + u * dotProduct v w,
    e 0 + u * w 0, e 1 + u * w 1]

theorem nullRayTangent_is_null
    (S : Matrix (Fin 2) (Fin 2) ℝ) (y : Screen) :
    minkowskiPair (nullRayTangent S y) (nullRayTangent S y) = 0 := by
  simp [minkowskiPair, nullRayTangent, dotProduct, Fin.sum_univ_succ]
  ring

theorem orthogonalNullRay_affine
    (S : Matrix (Fin 2) (Fin 2) ℝ) (y : Screen) (u : ℝ) :
    orthogonalNullRay S y u =
      orthogonalNullRay S y 0 + u • nullRayTangent S y := by
  funext i
  fin_cases i <;> simp [orthogonalNullRay, nullRayTangent] <;> ring

/-- The tangent is verified by differentiation, not only named as a vector. -/
theorem orthogonalNullRay_entry_hasDerivAt
    (S : Matrix (Fin 2) (Fin 2) ℝ) (y : Screen) (u : ℝ) (i : Fin 4) :
    HasDerivAt (fun t => orthogonalNullRay S y t i)
      (nullRayTangent S y i) u := by
  have h := (hasDerivAt_const u (orthogonalNullRay S y 0 i)).add
    ((hasDerivAt_id u).mul_const (nullRayTangent S y i))
  convert h using 1 <;>
    first | rfl | (funext t; rw [orthogonalNullRay_affine]; rfl) | simp

private theorem quadratic_hasDerivAt_zero (a b c : ℝ) :
    HasDerivAt (fun t : ℝ => a + b * t + c * t ^ 2) b 0 := by
  have h := ((hasDerivAt_const 0 a).add
    ((hasDerivAt_id 0).const_mul b)).add
      (((hasDerivAt_id 0).pow 2).const_mul c)
  convert h using 1 <;> first | rfl | simp

/-- Directional label derivatives of the repaired ray at every screen label. -/
theorem orthogonalNullRay_label_hasDerivAt
    (S : Matrix (Fin 2) (Fin 2) ℝ) (hsym : S.transpose = S)
    (y e : Screen) (u : ℝ) (i : Fin 4) :
    HasDerivAt (fun t : ℝ => orthogonalNullRay S (y + t • e) u i)
      (screenVariation S y u e i) 0 := by
  have hs : S 1 0 = S 0 1 := by
    simpa [Matrix.transpose_apply] using congrFun (congrFun hsym 0) 1
  let c := (dotProduct e (S.mulVec e) +
    u * dotProduct (S.mulVec e) (S.mulVec e)) / 2
  fin_cases i
  · convert quadratic_hasDerivAt_zero
      (orthogonalNullRay S y u 0) (screenVariation S y u e 0) 0 using 1 <;> try rfl
    funext t
    simp [orthogonalNullRay, screenVariation]
  · convert quadratic_hasDerivAt_zero
      (orthogonalNullRay S y u 1) (screenVariation S y u e 1) c using 1 <;> try rfl
    funext t
    simp [orthogonalNullRay, screenVariation, c, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, hs]
    ring
  · convert quadratic_hasDerivAt_zero
      (orthogonalNullRay S y u 2) (screenVariation S y u e 2) 0 using 1 <;> try rfl
    funext t
    simp [orthogonalNullRay, screenVariation, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]
    ring
  · convert quadratic_hasDerivAt_zero
      (orthogonalNullRay S y u 3) (screenVariation S y u e 3) 0 using 1 <;> try rfl
    funext t
    simp [orthogonalNullRay, screenVariation, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]
    ring

theorem screenVariation_orthogonal_to_tangent
    (S : Matrix (Fin 2) (Fin 2) ℝ) (y e : Screen) (u : ℝ) :
    minkowskiPair (nullRayTangent S y) (screenVariation S y u e) = 0 := by
  simp [minkowskiPair, nullRayTangent, screenVariation, dotProduct,
    Fin.sum_univ_succ]
  ring

/-- Pullback screen pairing is the Euclidean pairing after the Jacobi map. -/
theorem screenVariation_pairing
    (S : Matrix (Fin 2) (Fin 2) ℝ) (y e f : Screen) (u : ℝ) :
    minkowskiPair (screenVariation S y u e) (screenVariation S y u f) =
      dotProduct ((jacobi S u).mulVec e) ((jacobi S u).mulVec f) := by
  simp [minkowskiPair, screenVariation, jacobi, Matrix.add_mulVec,
    Matrix.smul_mulVec, dotProduct, Fin.sum_univ_succ]

/-- Nonsingularity of the Jacobi map makes the screen pairing positive. -/
theorem screenVariation_pairing_pos
    (S : Matrix (Fin 2) (Fin 2) ℝ) (y e : Screen) (u : ℝ)
    (hJ : Function.Injective (jacobi S u).mulVec) (he : e ≠ 0) :
    0 < minkowskiPair (screenVariation S y u e) (screenVariation S y u e) := by
  rw [screenVariation_pairing]
  have hne : (jacobi S u).mulVec e ≠ 0 := by
    intro h
    apply he
    apply hJ
    simpa using h
  have hnonneg : 0 ≤ dotProduct ((jacobi S u).mulVec e) ((jacobi S u).mulVec e) :=
    Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  by_contra hnot
  have hzero := le_antisymm (le_of_not_gt hnot) hnonneg
  exact hne (dotProduct_self_eq_zero.mp hzero)

/-- The repaired ray preserves the published transverse Perron map. -/
theorem perron_repaired_transverse_map (l u : ℝ) (y : Screen) :
    orthogonalNullRay (perronOpticalVelocity l) y u 2 =
        (perronOpticalJacobi l u).mulVec y 0 ∧
      orthogonalNullRay (perronOpticalVelocity l) y u 3 =
        (perronOpticalJacobi l u).mulVec y 1 := by
  constructor <;>
    simp [orthogonalNullRay, perronOpticalVelocity, perronOpticalJacobi,
      constitutiveBlock, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

theorem perron_jacobi_injective (l u : ℝ)
    (hA : perronOpticalAreaRatio l u ≠ 0) :
    Function.Injective (jacobi (perronOpticalVelocity l) u).mulVec := by
  have hJ : jacobi (perronOpticalVelocity l) u = perronOpticalJacobi l u :=
    (perronOpticalJacobi_eq_identity_add l u).symm
  rw [hJ]
  apply Matrix.mulVec_injective_iff_isUnit.mpr
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [isUnit_iff_ne_zero, perronOpticalJacobi_det]
  exact hA

theorem perron_screen_pairing_pos (l u : ℝ) (y e : Screen)
    (hA : perronOpticalAreaRatio l u ≠ 0) (he : e ≠ 0) :
    0 < minkowskiPair (screenVariation (perronOpticalVelocity l) y u e)
      (screenVariation (perronOpticalVelocity l) y u e) :=
  screenVariation_pairing_pos _ y e u (perron_jacobi_injective l u hA) he

/-- The induced metric on the label screen. -/
def perronScreenMetric (l u : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (perronOpticalJacobi l u).transpose * perronOpticalJacobi l u

/-- The published deformation is the mixed second fundamental form of the
repaired screen, as witnessed by the actual derivative of its induced metric. -/
theorem perronScreenMetric_hasDerivAt (l u : ℝ)
    (hA : perronOpticalAreaRatio l u ≠ 0) (i j : Fin 2) :
    HasDerivAt (fun t => perronScreenMetric l t i j)
      (2 * (perronScreenMetric l u * perronOpticalDeformation l u) i j) u := by
  have hJ := perronOpticalJacobi_entry_hasDerivAt l u
  have hraw := ((hJ 0 i).mul (hJ 0 j)).add ((hJ 1 i).mul (hJ 1 j))
  have hfun : (fun t => perronScreenMetric l t i j) =
      (fun t => perronOpticalJacobi l t 0 i * perronOpticalJacobi l t 0 j +
        perronOpticalJacobi l t 1 i * perronOpticalJacobi l t 1 j) := by
    funext t
    simp [perronScreenMetric, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.transpose_apply]
  rw [hfun]
  apply hraw.congr_deriv
  fin_cases i <;> fin_cases j <;>
    simp [perronScreenMetric, perronOpticalJacobi, perronOpticalVelocity,
      perronOpticalDeformation, constitutiveBlock, Matrix.mul_apply,
      Matrix.transpose_apply, Fin.sum_univ_two] <;>
    field_simp [hA] <;> unfold perronOpticalAreaRatio screening <;> ring

/-- Area minus affine parameter times area expansion is the finite-cut charge.
This is a geometric scalar; no physical modular identification is assumed. -/
def opticalBoundaryCharge (A theta : ℝ → ℝ) (u : ℝ) : ℝ :=
  A u - u * A u * theta u

/-- General differential finite-cut balance from the two-dimensional optical
equations. The term called `shearSq` is an input to those equations. -/
theorem opticalBoundaryCharge_hasDerivAt
    (A theta : ℝ → ℝ) (shearSq ricci u : ℝ)
    (hA : HasDerivAt A (theta u * A u) u)
    (htheta : HasDerivAt theta
      (-(theta u) ^ 2 / 2 - shearSq - ricci) u) :
    HasDerivAt (opticalBoundaryCharge A theta)
      (u * A u * (shearSq + ricci - (theta u) ^ 2 / 2)) u := by
  have h := hA.sub (((hasDerivAt_id u).mul hA).mul htheta)
  change HasDerivAt (A - id * A * theta) _ u
  exact h.congr_deriv (by dsimp; ring)

/-- An exact interval balance retains both finite endpoint charges. -/
theorem fullOpticalFlux_eq_boundaryCharge
    (A theta shearSq ricci : ℝ → ℝ) (a b : ℝ)
    (hA : ∀ u ∈ Set.uIcc a b, HasDerivAt A (theta u * A u) u)
    (htheta : ∀ u ∈ Set.uIcc a b, HasDerivAt theta
      (-(theta u) ^ 2 / 2 - shearSq u - ricci u) u)
    (hint : IntervalIntegrable
      (fun u => u * A u * (shearSq u + ricci u - (theta u) ^ 2 / 2))
      volume a b) :
    (∫ u in a..b, u * A u * (shearSq u + ricci u - (theta u) ^ 2 / 2)) =
      opticalBoundaryCharge A theta b - opticalBoundaryCharge A theta a := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u hu => opticalBoundaryCharge_hasDerivAt A theta
      (shearSq u) (ricci u) u (hA u hu) (htheta u hu)) hint

/-- The exact full optical density; the expansion term cannot be discarded. -/
def perronFullOpticalDensity (l u : ℝ) : ℝ :=
  perronOpticalAreaRatio l u *
    (perronOpticalShearSq l u - (perronOpticalExpansion l u) ^ 2 / 2)

theorem perronFullOpticalDensity_eq (l u : ℝ)
    (hA : perronOpticalAreaRatio l u ≠ 0) :
    perronFullOpticalDensity l u = 2 * l ^ 2 := by
  unfold perronFullOpticalDensity perronOpticalShearSq perronOpticalExpansion
  field_simp [hA]
  unfold perronOpticalAreaRatio screening
  ring

theorem perron_boundaryCharge_eq (l u : ℝ)
    (hA : perronOpticalAreaRatio l u ≠ 0) :
    opticalBoundaryCharge (perronOpticalAreaRatio l) (perronOpticalExpansion l) u =
      1 + l ^ 2 * u ^ 2 := by
  unfold opticalBoundaryCharge perronOpticalExpansion
  field_simp [hA]
  unfold perronOpticalAreaRatio screening
  ring

/-- The area-weighted evolving nonlinear flux equals the initial-shear proxy
for this affine model, on any nonsingular interval from zero. -/
theorem perron_fullBoostFlux (l L : ℝ)
    (hA : ∀ u ∈ Set.uIcc 0 L, perronOpticalAreaRatio l u ≠ 0) :
    (∫ u in (0 : ℝ)..L, u * perronFullOpticalDensity l u) = l ^ 2 * L ^ 2 := by
  calc
    (∫ u in (0 : ℝ)..L, u * perronFullOpticalDensity l u) =
        ∫ u in (0 : ℝ)..L, u * (2 * l ^ 2) := by
      apply intervalIntegral.integral_congr
      intro u hu
      change u * perronFullOpticalDensity l u = u * (2 * l ^ 2)
      rw [perronFullOpticalDensity_eq l u (hA u hu)]
    _ = l ^ 2 * L ^ 2 := by
      rw [intervalIntegral.integral_mul_const]
      norm_num
      ring

/-- Explicit finite-cut balance. The endpoint term is present even though
the full flux also equals the area deficit in this quadratic family. -/
theorem perron_fullBoostFlux_finiteCut (l L : ℝ)
    (hA : ∀ u ∈ Set.uIcc 0 L, perronOpticalAreaRatio l u ≠ 0) :
    (∫ u in (0 : ℝ)..L, u * perronFullOpticalDensity l u) =
      perronOpticalAreaRatio l L - perronOpticalAreaRatio l 0 -
        L * perronOpticalAreaRatio l L * perronOpticalExpansion l L := by
  have hAL := hA L (Set.right_mem_uIcc)
  rw [perron_fullBoostFlux l L hA]
  unfold perronOpticalExpansion
  field_simp [hAL]
  unfold perronOpticalAreaRatio screening
  ring

theorem perron_endpointExpansionTerm (l L : ℝ)
    (hA : perronOpticalAreaRatio l L ≠ 0) :
    -L * perronOpticalAreaRatio l L * perronOpticalExpansion l L =
      2 * l ^ 2 * L ^ 2 := by
  unfold perronOpticalExpansion
  field_simp [hA]

#print axioms orthogonalNullRay_label_hasDerivAt
#print axioms screenVariation_pairing_pos
#print axioms perronScreenMetric_hasDerivAt
#print axioms opticalBoundaryCharge_hasDerivAt
#print axioms fullOpticalFlux_eq_boundaryCharge
#print axioms perron_fullBoostFlux_finiteCut

end

end GravityScreening.OpticalRepair
