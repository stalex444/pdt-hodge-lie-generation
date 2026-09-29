module
public import GravityScreening.TTGeneralizedCurl

@[expose] public section

/-!
# Symplectic and kinetic structure of the full erasure dilation

A complex one-particle Hilbert space carries the real symplectic form given by
the imaginary part of its Hermitian pairing.  This file strengthens the norm
receipt for the finite erasure dilation to an exact pairing receipt.  The full
visible-plus-hidden map preserves both the Hermitian and symplectic pairings;
the exterior and hidden branches carry the complementary conformal factors.

For the two-state TT code, the dilation also intertwines the generalized-curl
symbol branch by branch.  These are kinematic compatibility theorems.  They
do not identify this Hilbert symplectic form with the full constrained ADM or
prepotential symplectic form of gravity.
-/

namespace GravityScreening

open scoped BigOperators

/-- Hermitian pairing on a finite complex amplitude space, antilinear in the
first entry. -/
noncomputable def finiteHermitianPairing {n : ℕ}
    (psi phi : Fin n → ℂ) : ℂ :=
  ∑ i, star (psi i) * phi i

/-- Hermitian pairing on the full visible-hidden output space. -/
noncomputable def bipartiteHermitianPairing {B E : Type*}
    [Fintype B] [Fintype E] (Psi Phi : B × E → ℂ) : ℂ :=
  ∑ b, ∑ e, star (Psi (b, e)) * Phi (b, e)

/-- Contribution to the output pairing from retained exterior data. -/
noncomputable def exteriorDataHermitianPairing {n : ℕ}
    (Psi Phi : Option (Fin n) × Option (Fin n) → ℂ) : ℂ :=
  ∑ i, star (Psi (some i, none)) * Phi (some i, none)

/-- Contribution to the output pairing from data transferred to the hidden
branch. -/
noncomputable def hiddenDataHermitianPairing {n : ℕ}
    (Psi Phi : Option (Fin n) × Option (Fin n) → ℂ) : ℂ :=
  ∑ i, star (Psi (none, some i)) * Phi (none, some i)

/-- The exterior branch scales every Hermitian pairing by `s`. -/
theorem erasureDilation_exterior_hermitian {n : ℕ}
    (s : ℝ) (psi phi : Fin n → ℂ) (hs0 : 0 ≤ s) :
    exteriorDataHermitianPairing
        (erasureDilation s psi) (erasureDilation s phi) =
      (s : ℂ) * finiteHermitianPairing psi phi := by
  have hstar : star ((Real.sqrt s : ℂ)) = (Real.sqrt s : ℂ) := by
    change (starRingEnd ℂ) ((Real.sqrt s : ℝ) : ℂ) = _
    exact Complex.conj_ofReal _
  have hsqrt : ((Real.sqrt s : ℂ) ^ 2) = (s : ℂ) := by
    exact_mod_cast Real.sq_sqrt hs0
  unfold exteriorDataHermitianPairing finiteHermitianPairing
  calc
    (∑ i, star (erasureDilation s psi (some i, none)) *
        erasureDilation s phi (some i, none)) =
        ∑ i, (s : ℂ) * (star (psi i) * phi i) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [erasureDilation, star_mul, hstar]
      calc
        (starRingEnd ℂ) (psi i) * (Real.sqrt s : ℂ) *
              ((Real.sqrt s : ℂ) * phi i) =
            (Real.sqrt s : ℂ) ^ 2 *
              ((starRingEnd ℂ) (psi i) * phi i) := by ring
        _ = (s : ℂ) * ((starRingEnd ℂ) (psi i) * phi i) := by
          rw [hsqrt]
    _ = (s : ℂ) * ∑ i, star (psi i) * phi i := by
      rw [Finset.mul_sum]

/-- The hidden branch carries the complementary Hermitian factor `1-s`. -/
theorem erasureDilation_hidden_hermitian {n : ℕ}
    (s : ℝ) (psi phi : Fin n → ℂ) (hs1 : s ≤ 1) :
    hiddenDataHermitianPairing
        (erasureDilation s psi) (erasureDilation s phi) =
      ((1 - s : ℝ) : ℂ) * finiteHermitianPairing psi phi := by
  have hcomp : 0 ≤ 1 - s := sub_nonneg.mpr hs1
  have hstar : star ((Real.sqrt (1 - s) : ℂ)) =
      (Real.sqrt (1 - s) : ℂ) := by
    change (starRingEnd ℂ) ((Real.sqrt (1 - s) : ℝ) : ℂ) = _
    exact Complex.conj_ofReal _
  have hsqrt : ((Real.sqrt (1 - s) : ℂ) ^ 2) =
      ((1 - s : ℝ) : ℂ) := by
    exact_mod_cast Real.sq_sqrt hcomp
  unfold hiddenDataHermitianPairing finiteHermitianPairing
  calc
    (∑ i, star (erasureDilation s psi (none, some i)) *
        erasureDilation s phi (none, some i)) =
        ∑ i, ((1 - s : ℝ) : ℂ) * (star (psi i) * phi i) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [erasureDilation, star_mul, hstar]
      calc
        (starRingEnd ℂ) (psi i) * (Real.sqrt (1 - s) : ℂ) *
              ((Real.sqrt (1 - s) : ℂ) * phi i) =
            (Real.sqrt (1 - s) : ℂ) ^ 2 *
              ((starRingEnd ℂ) (psi i) * phi i) := by ring
        _ = ((1 - s : ℝ) : ℂ) *
              ((starRingEnd ℂ) (psi i) * phi i) := by
          rw [hsqrt]
    _ = ((1 - s : ℝ) : ℂ) * ∑ i, star (psi i) * phi i := by
      rw [Finset.mul_sum]

/-- Only the retained and transferred data branches contribute to the full
output pairing. -/
theorem erasureDilation_bipartite_hermitian_eq_branches {n : ℕ}
    (s : ℝ) (psi phi : Fin n → ℂ) :
    bipartiteHermitianPairing
        (erasureDilation s psi) (erasureDilation s phi) =
      exteriorDataHermitianPairing
          (erasureDilation s psi) (erasureDilation s phi) +
        hiddenDataHermitianPairing
          (erasureDilation s psi) (erasureDilation s phi) := by
  unfold bipartiteHermitianPairing exteriorDataHermitianPairing
    hiddenDataHermitianPairing
  simp_rw [Fintype.sum_option]
  simp [erasureDilation]
  ring

/-- The full Stinespring dilation preserves every Hermitian pairing, not only
the norm of one vector. -/
theorem erasureDilation_preserves_hermitian {n : ℕ}
    (s : ℝ) (psi phi : Fin n → ℂ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    bipartiteHermitianPairing
        (erasureDilation s psi) (erasureDilation s phi) =
      finiteHermitianPairing psi phi := by
  rw [erasureDilation_bipartite_hermitian_eq_branches,
    erasureDilation_exterior_hermitian s psi phi hs0,
    erasureDilation_hidden_hermitian s psi phi hs1]
  push_cast
  ring

/-- Real symplectic form carried by a finite complex one-particle space. -/
noncomputable def finiteSymplecticPairing {n : ℕ}
    (psi phi : Fin n → ℂ) : ℝ :=
  (finiteHermitianPairing psi phi).im

/-- Exterior contribution to the underlying real symplectic pairing. -/
noncomputable def exteriorDataSymplecticPairing {n : ℕ}
    (Psi Phi : Option (Fin n) × Option (Fin n) → ℂ) : ℝ :=
  (exteriorDataHermitianPairing Psi Phi).im

/-- Hidden contribution to the underlying real symplectic pairing. -/
noncomputable def hiddenDataSymplecticPairing {n : ℕ}
    (Psi Phi : Option (Fin n) × Option (Fin n) → ℂ) : ℝ :=
  (hiddenDataHermitianPairing Psi Phi).im

/-- Symplectic form on the full dilation output. -/
noncomputable def bipartiteSymplecticPairing {B E : Type*}
    [Fintype B] [Fintype E] (Psi Phi : B × E → ℂ) : ℝ :=
  (bipartiteHermitianPairing Psi Phi).im

/-- The exterior restriction is conformally symplectic with multiplier `s`.
The missing pairing is carried by the hidden data branch. -/
theorem erasureDilation_exterior_symplectic {n : ℕ}
    (s : ℝ) (psi phi : Fin n → ℂ) (hs0 : 0 ≤ s) :
    exteriorDataSymplecticPairing
        (erasureDilation s psi) (erasureDilation s phi) =
      s * finiteSymplecticPairing psi phi := by
  unfold exteriorDataSymplecticPairing finiteSymplecticPairing
  rw [erasureDilation_exterior_hermitian s psi phi hs0]
  simp

/-- The hidden restriction is conformally symplectic with the complementary
multiplier `1-s`. -/
theorem erasureDilation_hidden_symplectic {n : ℕ}
    (s : ℝ) (psi phi : Fin n → ℂ) (hs1 : s ≤ 1) :
    hiddenDataSymplecticPairing
        (erasureDilation s psi) (erasureDilation s phi) =
      (1 - s) * finiteSymplecticPairing psi phi := by
  unfold hiddenDataSymplecticPairing finiteSymplecticPairing
  rw [erasureDilation_hidden_hermitian s psi phi hs1]
  simp

/-- The full dilation is symplectic on the underlying real one-particle phase
space. -/
theorem erasureDilation_preserves_symplectic {n : ℕ}
    (s : ℝ) (psi phi : Fin n → ℂ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    bipartiteSymplecticPairing
        (erasureDilation s psi) (erasureDilation s phi) =
      finiteSymplecticPairing psi phi := by
  unfold bipartiteSymplecticPairing finiteSymplecticPairing
  rw [erasureDilation_preserves_hermitian s psi phi hs0 hs1]

/-- Quartic exterior symplectic weight in its explicit algebraic form. -/
theorem quarticErasureDilation_exterior_symplectic {n : ℕ}
    (q : ℝ) (psi phi : Fin n → ℂ) (hq : 1 < q) :
    exteriorDataSymplecticPairing
        (quarticErasureDilation q psi) (quarticErasureDilation q phi) =
      ((2 * q - 1) / q ^ 2) * finiteSymplecticPairing psi phi := by
  have hq0 : q ≠ 0 := ne_of_gt (lt_trans (by norm_num) hq)
  unfold quarticErasureDilation
  rw [erasureDilation_exterior_symplectic
    (screening (lambda4 q)) psi phi
      (quarticScreening_bounds q hq).1]
  rw [quartic_screening_identity q hq0]

/-- The hidden branch carries the complementary quartic symplectic weight
`lambda4^2`. -/
theorem quarticErasureDilation_hidden_symplectic {n : ℕ}
    (q : ℝ) (psi phi : Fin n → ℂ) (hq : 1 < q) :
    hiddenDataSymplecticPairing
        (quarticErasureDilation q psi) (quarticErasureDilation q phi) =
      lambda4 q ^ 2 * finiteSymplecticPairing psi phi := by
  unfold quarticErasureDilation
  rw [erasureDilation_hidden_symplectic
    (screening (lambda4 q)) psi phi
      (quarticScreening_bounds q hq).2]
  unfold screening
  ring

/-- The fixed-momentum generalized curl is Hermitian on the two-polarization
one-particle space.  This is the spatial self-adjointness needed for its use
as a quadratic kinetic operator. -/
theorem complexTTCurlCoordinates_hermitian_selfAdjoint
    (k : ℝ) (x y : ComplexTTCoordinates) :
    finiteHermitianPairing x (complexTTCurlCoordinates k y) =
      finiteHermitianPairing (complexTTCurlCoordinates k x) y := by
  simp [finiteHermitianPairing, complexTTCurlCoordinates,
    Fin.sum_univ_succ, Complex.conj_I]
  ring

/-- Branchwise lift of the TT generalized-curl coordinate operator to the
two nonzero data ports of the dilation. -/
noncomputable def branchwiseTTCurlZ (k : ℝ)
    (Psi : Option (Fin 2) × Option (Fin 2) → ℂ) :
    Option (Fin 2) × Option (Fin 2) → ℂ
  | (some i, none) =>
      complexTTCurlCoordinates k (fun j => Psi (some j, none)) i
  | (none, some i) =>
      complexTTCurlCoordinates k (fun j => Psi (none, some j)) i
  | _ => 0

/-- The full visible-hidden dilation intertwines the local TT
generalized-curl symbol on both of its data branches. -/
theorem branchwiseTTCurlZ_erasureDilation
    (s k : ℝ) (x : ComplexTTCoordinates) :
    branchwiseTTCurlZ k (erasureDilation s x) =
      erasureDilation s (complexTTCurlCoordinates k x) := by
  funext y
  rcases y with ⟨b, e⟩
  cases b with
  | none =>
      cases e with
      | none => simp [branchwiseTTCurlZ, erasureDilation]
      | some i =>
          fin_cases i <;>
            simp [branchwiseTTCurlZ, erasureDilation,
              complexTTCurlCoordinates] <;> ring
  | some i =>
      cases e with
      | none =>
          fin_cases i <;>
            simp [branchwiseTTCurlZ, erasureDilation,
              complexTTCurlCoordinates] <;> ring
      | some j => simp [branchwiseTTCurlZ, erasureDilation]

/-- Quartic capstone: the complete horizon-code dilation simultaneously
preserves the one-particle symplectic pairing and intertwines the TT spatial
kinetic symbol. -/
theorem quarticErasureDilation_symplectic_and_curl
    (q k : ℝ) (psi phi : ComplexTTCoordinates) (hq : 1 < q) :
    (bipartiteSymplecticPairing
        (quarticErasureDilation q psi) (quarticErasureDilation q phi) =
      finiteSymplecticPairing psi phi) ∧
    (branchwiseTTCurlZ k (quarticErasureDilation q psi) =
      quarticErasureDilation q (complexTTCurlCoordinates k psi)) := by
  constructor
  · unfold quarticErasureDilation
    exact erasureDilation_preserves_symplectic
      (screening (lambda4 q)) psi phi
        (quarticScreening_bounds q hq).1
        (quarticScreening_bounds q hq).2
  · unfold quarticErasureDilation
    exact branchwiseTTCurlZ_erasureDilation
      (screening (lambda4 q)) k psi

#print axioms GravityScreening.erasureDilation_exterior_hermitian
#print axioms GravityScreening.erasureDilation_hidden_hermitian
#print axioms GravityScreening.erasureDilation_bipartite_hermitian_eq_branches
#print axioms GravityScreening.erasureDilation_preserves_hermitian
#print axioms GravityScreening.erasureDilation_exterior_symplectic
#print axioms GravityScreening.erasureDilation_hidden_symplectic
#print axioms GravityScreening.erasureDilation_preserves_symplectic
#print axioms GravityScreening.quarticErasureDilation_exterior_symplectic
#print axioms GravityScreening.quarticErasureDilation_hidden_symplectic
#print axioms GravityScreening.complexTTCurlCoordinates_hermitian_selfAdjoint
#print axioms GravityScreening.branchwiseTTCurlZ_erasureDilation
#print axioms GravityScreening.quarticErasureDilation_symplectic_and_curl

end GravityScreening
