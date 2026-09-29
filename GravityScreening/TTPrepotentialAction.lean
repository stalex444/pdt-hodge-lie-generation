module
public import GravityScreening.ErasureSymplectic

@[expose] public section

/-!
# The full quartic dilation on the TT prepotential action

On the constrained transverse-traceless sector of the Barnich--Troessaert
duality-symmetric spin-two action, the canonical term can be written

`-2 Delta <O H^2, d_t H^1>`,

while the Hamiltonian is the sum over the two prepotentials of
`<H^a, Delta^2 H^a>`.  For a Fourier mode with momentum along the third axis,
`Delta = -k^2`.  This file writes those exact fixed-mode forms on the
canonically normalized two-polarization code.

The full visible-plus-hidden erasure dilation preserves both terms.  Its
exterior and hidden restrictions multiply the complete action by the
complementary weights `s` and `1-s`.  The branch index introduced by the
dilation remains separate from the two-valued gravitational prepotential
index.
-/

namespace GravityScreening

/-- Two duality-related gravitational prepotentials, each carrying the two
complex TT polarization amplitudes. -/
abbrev TTPrepotentialMode := Fin 2 → ComplexTTCoordinates

/-- The same prepotential doublet after adjoining visible and hidden output
ports. -/
abbrev DilatedTTPrepotentialMode :=
  Fin 2 → Option (Fin 2) × Option (Fin 2) → ℂ

/-- Apply the horizon dilation to the polarization data of each
prepotential, without identifying the branch and prepotential indices. -/
noncomputable def dilateTTPrepotentialMode
    (s : ℝ) (H : TTPrepotentialMode) : DilatedTTPrepotentialMode :=
  fun a => erasureDilation s (H a)

/-- Fixed-momentum TT canonical term
`-2 Delta <O H^2, d_t H^1> = 2 k^2 <O H^2, d_t H^1>`.
The real part gives the real Fourier-paired action density. -/
noncomputable def ttPrepotentialKineticTerm
    (k : ℝ) (H Hdot : TTPrepotentialMode) : ℝ :=
  (2 * ((k ^ 2 : ℝ) : ℂ) *
    finiteHermitianPairing
      (complexTTCurlCoordinates k (H 1)) (Hdot 0)).re

/-- Fixed-momentum TT Hamiltonian
`sum_a <H^a, Delta^2 H^a>` with `Delta^2 = k^4`. -/
noncomputable def ttPrepotentialHamiltonian
    (k : ℝ) (H : TTPrepotentialMode) : ℝ :=
  (((k ^ 4 : ℝ) : ℂ) *
    (finiteHermitianPairing (H 0) (H 0) +
      finiteHermitianPairing (H 1) (H 1))).re

/-- Fixed-mode TT prepotential Lagrangian density. -/
noncomputable def ttPrepotentialLagrangian
    (k : ℝ) (H Hdot : TTPrepotentialMode) : ℝ :=
  ttPrepotentialKineticTerm k H Hdot -
    ttPrepotentialHamiltonian k H

/-- Canonical term on the complete visible-hidden output. -/
noncomputable def dilatedTTPrepotentialKineticTerm
    (k : ℝ) (H Hdot : DilatedTTPrepotentialMode) : ℝ :=
  (2 * ((k ^ 2 : ℝ) : ℂ) *
    bipartiteHermitianPairing
      (branchwiseTTCurlZ k (H 1)) (Hdot 0)).re

/-- Hamiltonian on the complete visible-hidden output. -/
noncomputable def dilatedTTPrepotentialHamiltonian
    (k : ℝ) (H : DilatedTTPrepotentialMode) : ℝ :=
  (((k ^ 4 : ℝ) : ℂ) *
    (bipartiteHermitianPairing (H 0) (H 0) +
      bipartiteHermitianPairing (H 1) (H 1))).re

/-- Full output fixed-mode Lagrangian. -/
noncomputable def dilatedTTPrepotentialLagrangian
    (k : ℝ) (H Hdot : DilatedTTPrepotentialMode) : ℝ :=
  dilatedTTPrepotentialKineticTerm k H Hdot -
    dilatedTTPrepotentialHamiltonian k H

/-- The complete dilation preserves the canonical prepotential term. -/
theorem dilateTTPrepotentialMode_preserves_kinetic
    (s k : ℝ) (H Hdot : TTPrepotentialMode)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    dilatedTTPrepotentialKineticTerm k
        (dilateTTPrepotentialMode s H)
        (dilateTTPrepotentialMode s Hdot) =
      ttPrepotentialKineticTerm k H Hdot := by
  unfold dilatedTTPrepotentialKineticTerm
    dilateTTPrepotentialMode ttPrepotentialKineticTerm
  rw [branchwiseTTCurlZ_erasureDilation]
  rw [erasureDilation_preserves_hermitian _ _ _ hs0 hs1]

/-- The complete dilation preserves the TT prepotential Hamiltonian. -/
theorem dilateTTPrepotentialMode_preserves_hamiltonian
    (s k : ℝ) (H : TTPrepotentialMode)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    dilatedTTPrepotentialHamiltonian k
        (dilateTTPrepotentialMode s H) =
      ttPrepotentialHamiltonian k H := by
  unfold dilatedTTPrepotentialHamiltonian
    dilateTTPrepotentialMode ttPrepotentialHamiltonian
  rw [erasureDilation_preserves_hermitian s (H 0) (H 0) hs0 hs1]
  rw [erasureDilation_preserves_hermitian s (H 1) (H 1) hs0 hs1]

/-- Therefore the full visible-hidden map preserves the complete
time-dependent TT prepotential Lagrangian mode by mode. -/
theorem dilateTTPrepotentialMode_preserves_lagrangian
    (s k : ℝ) (H Hdot : TTPrepotentialMode)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    dilatedTTPrepotentialLagrangian k
        (dilateTTPrepotentialMode s H)
        (dilateTTPrepotentialMode s Hdot) =
      ttPrepotentialLagrangian k H Hdot := by
  unfold dilatedTTPrepotentialLagrangian ttPrepotentialLagrangian
  rw [dilateTTPrepotentialMode_preserves_kinetic s k H Hdot hs0 hs1]
  rw [dilateTTPrepotentialMode_preserves_hamiltonian s k H hs0 hs1]

/-- Exterior contribution to the canonical prepotential term. -/
noncomputable def exteriorTTPrepotentialKineticTerm
    (k : ℝ) (H Hdot : DilatedTTPrepotentialMode) : ℝ :=
  (2 * ((k ^ 2 : ℝ) : ℂ) *
    exteriorDataHermitianPairing
      (branchwiseTTCurlZ k (H 1)) (Hdot 0)).re

/-- Exterior contribution to the prepotential Hamiltonian. -/
noncomputable def exteriorTTPrepotentialHamiltonian
    (k : ℝ) (H : DilatedTTPrepotentialMode) : ℝ :=
  (((k ^ 4 : ℝ) : ℂ) *
    (exteriorDataHermitianPairing (H 0) (H 0) +
      exteriorDataHermitianPairing (H 1) (H 1))).re

/-- Exterior fixed-mode Lagrangian. -/
noncomputable def exteriorTTPrepotentialLagrangian
    (k : ℝ) (H Hdot : DilatedTTPrepotentialMode) : ℝ :=
  exteriorTTPrepotentialKineticTerm k H Hdot -
    exteriorTTPrepotentialHamiltonian k H

/-- Hidden contribution to the canonical prepotential term. -/
noncomputable def hiddenTTPrepotentialKineticTerm
    (k : ℝ) (H Hdot : DilatedTTPrepotentialMode) : ℝ :=
  (2 * ((k ^ 2 : ℝ) : ℂ) *
    hiddenDataHermitianPairing
      (branchwiseTTCurlZ k (H 1)) (Hdot 0)).re

/-- Hidden contribution to the prepotential Hamiltonian. -/
noncomputable def hiddenTTPrepotentialHamiltonian
    (k : ℝ) (H : DilatedTTPrepotentialMode) : ℝ :=
  (((k ^ 4 : ℝ) : ℂ) *
    (hiddenDataHermitianPairing (H 0) (H 0) +
      hiddenDataHermitianPairing (H 1) (H 1))).re

/-- Hidden fixed-mode Lagrangian. -/
noncomputable def hiddenTTPrepotentialLagrangian
    (k : ℝ) (H Hdot : DilatedTTPrepotentialMode) : ℝ :=
  hiddenTTPrepotentialKineticTerm k H Hdot -
    hiddenTTPrepotentialHamiltonian k H

/-- The exterior canonical term carries the common retention weight `s`. -/
theorem dilateTTPrepotentialMode_exterior_kinetic
    (s k : ℝ) (H Hdot : TTPrepotentialMode) (hs0 : 0 ≤ s) :
    exteriorTTPrepotentialKineticTerm k
        (dilateTTPrepotentialMode s H)
        (dilateTTPrepotentialMode s Hdot) =
      s * ttPrepotentialKineticTerm k H Hdot := by
  unfold exteriorTTPrepotentialKineticTerm
    dilateTTPrepotentialMode ttPrepotentialKineticTerm
  rw [branchwiseTTCurlZ_erasureDilation]
  rw [erasureDilation_exterior_hermitian _ _ _ hs0]
  simp
  ring

/-- The exterior Hamiltonian carries the same retention weight `s`. -/
theorem dilateTTPrepotentialMode_exterior_hamiltonian
    (s k : ℝ) (H : TTPrepotentialMode) (hs0 : 0 ≤ s) :
    exteriorTTPrepotentialHamiltonian k
        (dilateTTPrepotentialMode s H) =
      s * ttPrepotentialHamiltonian k H := by
  unfold exteriorTTPrepotentialHamiltonian
    dilateTTPrepotentialMode ttPrepotentialHamiltonian
  rw [erasureDilation_exterior_hermitian s (H 0) (H 0) hs0]
  rw [erasureDilation_exterior_hermitian s (H 1) (H 1) hs0]
  simp
  ring

/-- The complete exterior prepotential action is uniformly scaled by `s`.
Its source-free field equations are therefore unchanged when `s>0`, while a
separately normalized source sees the inverse response. -/
theorem dilateTTPrepotentialMode_exterior_lagrangian
    (s k : ℝ) (H Hdot : TTPrepotentialMode) (hs0 : 0 ≤ s) :
    exteriorTTPrepotentialLagrangian k
        (dilateTTPrepotentialMode s H)
        (dilateTTPrepotentialMode s Hdot) =
      s * ttPrepotentialLagrangian k H Hdot := by
  unfold exteriorTTPrepotentialLagrangian ttPrepotentialLagrangian
  rw [dilateTTPrepotentialMode_exterior_kinetic s k H Hdot hs0]
  rw [dilateTTPrepotentialMode_exterior_hamiltonian s k H hs0]
  ring

/-- The hidden canonical term carries the complementary weight `1-s`. -/
theorem dilateTTPrepotentialMode_hidden_kinetic
    (s k : ℝ) (H Hdot : TTPrepotentialMode) (hs1 : s ≤ 1) :
    hiddenTTPrepotentialKineticTerm k
        (dilateTTPrepotentialMode s H)
        (dilateTTPrepotentialMode s Hdot) =
      (1 - s) * ttPrepotentialKineticTerm k H Hdot := by
  unfold hiddenTTPrepotentialKineticTerm
    dilateTTPrepotentialMode ttPrepotentialKineticTerm
  rw [branchwiseTTCurlZ_erasureDilation]
  rw [erasureDilation_hidden_hermitian _ _ _ hs1]
  simp
  ring

/-- The hidden Hamiltonian carries the same complementary weight. -/
theorem dilateTTPrepotentialMode_hidden_hamiltonian
    (s k : ℝ) (H : TTPrepotentialMode) (hs1 : s ≤ 1) :
    hiddenTTPrepotentialHamiltonian k
        (dilateTTPrepotentialMode s H) =
      (1 - s) * ttPrepotentialHamiltonian k H := by
  unfold hiddenTTPrepotentialHamiltonian
    dilateTTPrepotentialMode ttPrepotentialHamiltonian
  rw [erasureDilation_hidden_hermitian s (H 0) (H 0) hs1]
  rw [erasureDilation_hidden_hermitian s (H 1) (H 1) hs1]
  simp
  ring

/-- The hidden prepotential action is uniformly scaled by `1-s`. -/
theorem dilateTTPrepotentialMode_hidden_lagrangian
    (s k : ℝ) (H Hdot : TTPrepotentialMode) (hs1 : s ≤ 1) :
    hiddenTTPrepotentialLagrangian k
        (dilateTTPrepotentialMode s H)
        (dilateTTPrepotentialMode s Hdot) =
      (1 - s) * ttPrepotentialLagrangian k H Hdot := by
  unfold hiddenTTPrepotentialLagrangian ttPrepotentialLagrangian
  rw [dilateTTPrepotentialMode_hidden_kinetic s k H Hdot hs1]
  rw [dilateTTPrepotentialMode_hidden_hamiltonian s k H hs1]
  ring

/-- Quartic specialization of the time-dependent action theorem. -/
theorem quarticDilatedTTPrepotential_exterior_lagrangian
    (q k : ℝ) (H Hdot : TTPrepotentialMode) (hq : 1 < q) :
    exteriorTTPrepotentialLagrangian k
        (dilateTTPrepotentialMode (screening (lambda4 q)) H)
        (dilateTTPrepotentialMode (screening (lambda4 q)) Hdot) =
      ((2 * q - 1) / q ^ 2) *
        ttPrepotentialLagrangian k H Hdot := by
  have hq0 : q ≠ 0 := ne_of_gt (lt_trans (by norm_num) hq)
  rw [dilateTTPrepotentialMode_exterior_lagrangian
    (screening (lambda4 q)) k H Hdot
      (quarticScreening_bounds q hq).1]
  rw [quartic_screening_identity q hq0]

/-- The hidden time-dependent action carries the exact complementary
quartic weight `lambda4^2`. -/
theorem quarticDilatedTTPrepotential_hidden_lagrangian
    (q k : ℝ) (H Hdot : TTPrepotentialMode) (hq : 1 < q) :
    hiddenTTPrepotentialLagrangian k
        (dilateTTPrepotentialMode (screening (lambda4 q)) H)
        (dilateTTPrepotentialMode (screening (lambda4 q)) Hdot) =
      lambda4 q ^ 2 * ttPrepotentialLagrangian k H Hdot := by
  rw [dilateTTPrepotentialMode_hidden_lagrangian
    (screening (lambda4 q)) k H Hdot
      (quarticScreening_bounds q hq).2]
  unfold screening
  ring

/-- Quartic global capstone: the complete dilation preserves the fixed-mode
TT prepotential action while its exterior restriction carries exactly the
PDT screening coefficient. -/
theorem quarticDilatedTTPrepotential_global_and_exterior
    (q k : ℝ) (H Hdot : TTPrepotentialMode) (hq : 1 < q) :
    (dilatedTTPrepotentialLagrangian k
        (dilateTTPrepotentialMode (screening (lambda4 q)) H)
        (dilateTTPrepotentialMode (screening (lambda4 q)) Hdot) =
      ttPrepotentialLagrangian k H Hdot) ∧
    (exteriorTTPrepotentialLagrangian k
        (dilateTTPrepotentialMode (screening (lambda4 q)) H)
        (dilateTTPrepotentialMode (screening (lambda4 q)) Hdot) =
      ((2 * q - 1) / q ^ 2) *
        ttPrepotentialLagrangian k H Hdot) := by
  constructor
  · exact dilateTTPrepotentialMode_preserves_lagrangian
      (screening (lambda4 q)) k H Hdot
        (quarticScreening_bounds q hq).1
        (quarticScreening_bounds q hq).2
  · exact quarticDilatedTTPrepotential_exterior_lagrangian
      q k H Hdot hq

#print axioms GravityScreening.dilateTTPrepotentialMode_preserves_kinetic
#print axioms GravityScreening.dilateTTPrepotentialMode_preserves_hamiltonian
#print axioms GravityScreening.dilateTTPrepotentialMode_preserves_lagrangian
#print axioms GravityScreening.dilateTTPrepotentialMode_exterior_kinetic
#print axioms GravityScreening.dilateTTPrepotentialMode_exterior_hamiltonian
#print axioms GravityScreening.dilateTTPrepotentialMode_exterior_lagrangian
#print axioms GravityScreening.dilateTTPrepotentialMode_hidden_kinetic
#print axioms GravityScreening.dilateTTPrepotentialMode_hidden_hamiltonian
#print axioms GravityScreening.dilateTTPrepotentialMode_hidden_lagrangian
#print axioms GravityScreening.quarticDilatedTTPrepotential_exterior_lagrangian
#print axioms GravityScreening.quarticDilatedTTPrepotential_hidden_lagrangian
#print axioms GravityScreening.quarticDilatedTTPrepotential_global_and_exterior

end GravityScreening
