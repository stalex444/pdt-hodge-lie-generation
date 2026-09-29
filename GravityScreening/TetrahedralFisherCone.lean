module
public import GravityScreening.PerronTetrahedralBridge
public import GravityScreening.InformationArea

@[expose] public section

/-!
# Radial and shape directions of the positive-measure Fisher cone

A positive four-weight vector can be written as a total mass `m` times a
normalized shape `p`.  This file proves that the diagonal Fisher metric splits
orthogonally into a one-dimensional mass term and the Fisher metric of the
normalized shape.  The theorem is stated for any finite number of outcomes;
the quartic tetrahedral distribution is its four-outcome application.
-/

namespace GravityScreening

open scoped BigOperators

/-- An unnormalized positive measure with total scale `m` and normalized
shape `p`. -/
def coneWeight {n : ℕ} (m : ℝ) (p : Fin n → ℝ) : Fin n → ℝ :=
  fun i => m * p i

/-- Its tangent decomposes into a mass variation and a shape variation. -/
def coneTangent {n : ℕ}
    (m dm : ℝ) (p dp : Fin n → ℝ) : Fin n → ℝ :=
  fun i => dm * p i + m * dp i

/-- The Fisher pairing on the cone of positive measures splits into a radial
mass term and a tangential normalized-shape term.  The mixed terms vanish
because shape tangents have zero total mass. -/
theorem fisherCone_pair_decomposition {n : ℕ}
    (m dm dn : ℝ) (p dp ep : Fin n → ℝ)
    (hm : m ≠ 0) (hp : ∀ i, p i ≠ 0)
    (hsum : ∑ i, p i = 1)
    (hdp : ∑ i, dp i = 0) (hep : ∑ i, ep i = 0) :
    diagonalFisherPair (coneWeight m p)
        (coneTangent m dm p dp) (coneTangent m dn p ep) =
      dm * dn / m + m * diagonalFisherPair p dp ep := by
  unfold diagonalFisherPair coneWeight coneTangent
  calc
    ∑ i, (dm * p i + m * dp i) * (dn * p i + m * ep i) /
        (m * p i) =
      ∑ i, ((dm * dn / m) * p i + dm * ep i + dn * dp i +
        m * (dp i * ep i / p i)) := by
          apply Finset.sum_congr rfl
          intro i _hi
          field_simp [hm, hp i]
          ring
    _ = (dm * dn / m) * (∑ i, p i) + dm * (∑ i, ep i) +
        dn * (∑ i, dp i) + m * (∑ i, dp i * ep i / p i) := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = dm * dn / m + m * (∑ i, dp i * ep i / p i) := by
          rw [hsum, hdp, hep]
          ring

/-- On the diagonal, the squared line element is the radial mass term plus
`m` times the Fisher metric of the normalized record. -/
theorem fisherCone_norm_decomposition {n : ℕ}
    (m dm : ℝ) (p dp : Fin n → ℝ)
    (hm : m ≠ 0) (hp : ∀ i, p i ≠ 0)
    (hsum : ∑ i, p i = 1) (hdp : ∑ i, dp i = 0) :
    diagonalFisher (coneWeight m p) (coneTangent m dm p dp) =
      dm ^ 2 / m + m * diagonalFisher p dp := by
  have hpair := fisherCone_pair_decomposition
    m dm dm p dp dp hm hp hsum hdp hdp
  simpa [diagonalFisher, diagonalFisherPair, pow_two] using hpair

/-- Pure changes of total mass and pure changes of normalized shape are
Fisher-orthogonal. -/
theorem fisherCone_radial_shape_orthogonal {n : ℕ}
    (m dm : ℝ) (p dp : Fin n → ℝ)
    (hm : m ≠ 0) (hp : ∀ i, p i ≠ 0)
    (hsum : ∑ i, p i = 1) (hdp : ∑ i, dp i = 0) :
    diagonalFisherPair (coneWeight m p)
        (coneTangent m dm p (fun _ => 0))
        (coneTangent m 0 p dp) = 0 := by
  rw [fisherCone_pair_decomposition m dm 0 p (fun _ => 0) dp
    hm hp hsum (by simp) hdp]
  simp [diagonalFisherPair]

/-- Multiplying a normalized four-outcome shape by a scalar Hilbert amplitude
changes only its radial mass, from one to `a^2`; conditioning preserves the
tetrahedral record. -/
theorem scalarAmplitude_is_purely_radial
    (a : ℝ) (weight : Fin 4 → ℝ) (ha : a ≠ 0) :
    tetraRecord (fun i => scalarOutcomeBranch a weight i / a ^ 2) =
      tetraRecord weight := by
  rw [scalarOutcomeBranch_renormalizes a weight ha]

/-- Every entry of the normalized quartic Perron distribution is nonzero in
the physical range `q > 1`. -/
theorem normalizedQuarticPerron_ne_zero
    (q : ℝ) (hq1 : 1 < q) :
    ∀ i, normalizedQuarticPerron q i ≠ 0 := by
  have hmass : quarticPerronMass q ≠ 0 := by
    unfold quarticPerronMass
    positivity
  intro i
  fin_cases i <;>
    simp [normalizedQuarticPerron, quarticPerronVector, hmass] <;>
    positivity

/-- The `3 + 1` Fisher-cone split specialized to the normalized quartic
Perron shape. -/
theorem quarticPerron_fisherCone_pair_decomposition
    (q m dm dn : ℝ) (dp ep : Fin 4 → ℝ)
    (hq1 : 1 < q) (hm : m ≠ 0)
    (hdp : ∑ i, dp i = 0) (hep : ∑ i, ep i = 0) :
    diagonalFisherPair (coneWeight m (normalizedQuarticPerron q))
        (coneTangent m dm (normalizedQuarticPerron q) dp)
        (coneTangent m dn (normalizedQuarticPerron q) ep) =
      dm * dn / m +
        m * diagonalFisherPair (normalizedQuarticPerron q) dp ep := by
  have hmass : quarticPerronMass q ≠ 0 := by
    unfold quarticPerronMass
    positivity
  exact fisherCone_pair_decomposition m dm dn
    (normalizedQuarticPerron q) dp ep hm
    (normalizedQuarticPerron_ne_zero q hq1)
    (normalizedQuarticPerron_sum q hmass) hdp hep

/-- The same quartic Born mass is positive in the Hermitian reading and
subtracted in both the local intrinsic trace and the global quartic trace
response.  This packages the information-to-Lorentzian sign flip without
identifying either form with physical spacetime. -/
theorem quarticPerron_information_trace_bridge
    (q : ℝ) (hq : q ^ 4 = q + 1) (hq1 : 1 < q) :
    let hiddenMass := ∑ i, scalarOutcomeBranch (lambda4 q)
      (normalizedQuarticPerron q) i
    hiddenMass = lambda4 q ^ 2 ∧
      normalizedHermitianTrace (affineComplexResponse (lambda4 q)) =
        1 + hiddenMass ∧
      normalizedIntrinsicTrace (affineComplexResponse (lambda4 q)) =
        1 - hiddenMass ∧
      quarticTracePair (quarticTraceResponse (lambda4 q))
          (quarticTraceResponse (lambda4 q)) = 1 - hiddenMass := by
  dsimp
  have hsplit := quarticPerron_BornBranch_split q hq hq1
  constructor
  · exact hsplit.1
  constructor
  · rw [normalizedHermitianTrace_affine, hsplit.1]
  constructor
  · rw [normalizedIntrinsicTrace_affine, hsplit.1]
    rfl
  · rw [quarticTraceResponse_sq, hsplit.1]
    rfl

#print axioms GravityScreening.fisherCone_pair_decomposition
#print axioms GravityScreening.fisherCone_norm_decomposition
#print axioms GravityScreening.fisherCone_radial_shape_orthogonal
#print axioms GravityScreening.scalarAmplitude_is_purely_radial
#print axioms GravityScreening.normalizedQuarticPerron_ne_zero
#print axioms GravityScreening.quarticPerron_fisherCone_pair_decomposition
#print axioms GravityScreening.quarticPerron_information_trace_bridge

end GravityScreening
