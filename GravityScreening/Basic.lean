module
public import Mathlib

@[expose] public section

/-!
# A minimal algebraic model of the PDT gravity-screening coefficient

This file proves only the exact algebra used by the exploratory mechanism.
The identification of `lambda4` with a physical kinetic or curvature mixing
coefficient is not a theorem in this file.
-/

namespace GravityScreening

/-- The quartic-sector self-coupling as a function of a nonzero real `q`. -/
noncomputable def lambda4 (q : ℝ) : ℝ := 1 - 1 / q

/-- The proposed surviving response fraction. -/
def screening (l : ℝ) : ℝ := 1 - l ^ 2

/-- A general real quadratic scalar on a background/time plane. -/
def quadraticSpacetimeScalar (a b c x t : ℝ) : ℝ :=
  a * x ^ 2 + 2 * b * x * t + c * t ^ 2

/-- A quadratic scalar normalized on the background, even under reversal of
the time coordinate, and zero on the unit null direction is forced to be the
Lorentzian difference of squares on the normalized-background slice. -/
theorem normalized_even_null_quadratic_forced
    (a b c l : ℝ)
    (hbase : quadraticSpacetimeScalar a b c 1 0 = 1)
    (heven : ∀ t : ℝ,
      quadraticSpacetimeScalar a b c 1 t =
        quadraticSpacetimeScalar a b c 1 (-t))
    (hnull : quadraticSpacetimeScalar a b c 1 1 = 0) :
    quadraticSpacetimeScalar a b c 1 l = screening l := by
  have ha : a = 1 := by
    simpa [quadraticSpacetimeScalar] using hbase
  have hb : b = 0 := by
    have h := heven 1
    norm_num [quadraticSpacetimeScalar] at h
    linarith
  have hc : c = -1 := by
    simp [quadraticSpacetimeScalar, ha, hb] at hnull
    linarith
  simp [quadraticSpacetimeScalar, screening, ha, hb, hc]
  ring

/-- A normalized two-channel quadratic response. -/
def response (l x y : ℝ) : ℝ := x ^ 2 + y ^ 2 - 2 * l * x * y

/-- Completing the square exposes the Schur-complement coefficient. -/
theorem response_completed_square (l x y : ℝ) :
    response l x y = (y - l * x) ^ 2 + screening l * x ^ 2 := by
  simp [response, screening]
  ring

/-- Eliminating the second channel at its stationary value leaves the
screening coefficient. -/
theorem response_at_stationary (l x : ℝ) :
    response l x (l * x) = screening l * x ^ 2 := by
  rw [response_completed_square]
  ring

/-- The determinant of the normalized two-channel block. -/
def det2 (a b c d : ℝ) : ℝ := a * d - b * c

theorem normalized_block_det (l : ℝ) :
    det2 1 (-l) (-l) 1 = screening l := by
  simp [det2, screening]
  ring

/-! ## Symplectic normalization of the two-channel block

The raw response block has determinant `1-l^2`.  A twisted-self-duality
operator should square to minus the identity, which requires separating this
determinant from the unimodular shape of the block.  The statements below are
only two-dimensional linear algebra; their use as a gravitational
constitutive law remains an additional physical premise.
-/

/-- The symmetric two-channel constitutive block. -/
def constitutiveBlock (l : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, -l; -l, 1]

/-- The canonical symplectic matrix on the doubled pair. -/
def symplecticBlock : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, -1; 1, 0]

/-- Divide the constitutive block by a positive square root `d` of its
determinant. -/
noncomputable def unimodularConstitutive
    (l d : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (1 / d) • constitutiveBlock l

/-- Two normalized channel vectors assembled as columns: the reference
channel `(1,0)` and a channel with overlap `-l` and positive defect coordinate
`d`. -/
def channelEmbedding (l d : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, -l; 0, d]

/-- The oriented area of the two-channel embedding is the defect amplitude. -/
theorem channelEmbedding_det (l d : ℝ) :
    Matrix.det (channelEmbedding l d) = d := by
  simp [channelEmbedding, Matrix.det_fin_two]

/-- Norm preservation forces the Gram matrix of the reference and residual
channels to be exactly the raw constitutive block. -/
theorem channelEmbedding_gram
    (l d : ℝ) (hd : d ^ 2 = screening l) :
    (channelEmbedding l d).transpose * channelEmbedding l d =
      constitutiveBlock l := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [channelEmbedding, constitutiveBlock, Matrix.transpose_apply,
      Matrix.mul_apply, Fin.sum_univ_succ, screening] at hd ⊢
  all_goals nlinarith

/-- Squared norm of the reference channel after orthogonally removing its
component along the normalized residual channel `(-l,d)`.  In coordinates the
residual is `(1-l^2,l*d)`. -/
def projectionResidualNormSq (l d : ℝ) : ℝ :=
  (1 - l ^ 2) ^ 2 + (l * d) ^ 2

/-- Projection away from a normalized channel of overlap `l` leaves exactly
the screening norm `1-l^2`. -/
theorem projectionResidual_normSq
    (l d : ℝ) (hd : d ^ 2 = screening l) :
    projectionResidualNormSq l d = screening l := by
  unfold projectionResidualNormSq
  rw [mul_pow, hd]
  unfold screening
  ring

/-! ## The complex-place trace-form realization

The completed complex place carries both the untwisted trace form
`Tr(z*w)` and its conjugation-twisted positive form `Tr(z*conj w)`.  On the
affine response `1+i*l`, these give the difference and sum of squares.  The
identification of the first with a physical curvature response is not made by
the theorems below.
-/

/-- The affine complex-place response with real residual coefficient `l`. -/
noncomputable def affineComplexResponse (l : ℝ) : ℂ :=
  1 + (l : ℂ) * Complex.I

/-- The normalized untwisted local trace form. -/
noncomputable def normalizedIntrinsicTrace (z : ℂ) : ℝ :=
  Algebra.traceForm ℝ ℂ z z / Algebra.traceForm ℝ ℂ 1 1

/-- The normalized conjugation-twisted local trace form. -/
noncomputable def normalizedHermitianTrace (z : ℂ) : ℝ :=
  Algebra.traceForm ℝ ℂ z (starRingEnd ℂ z) /
    Algebra.traceForm ℝ ℂ 1 1

/-- On `1+i*l`, the intrinsic complex-place trace form is the screening
difference of squares. -/
theorem normalizedIntrinsicTrace_affine (l : ℝ) :
    normalizedIntrinsicTrace (affineComplexResponse l) = screening l := by
  simp [normalizedIntrinsicTrace, affineComplexResponse,
    Algebra.traceForm_apply, Algebra.trace_complex_apply, screening,
    Complex.mul_re, Complex.mul_im]
  ring

/-- Conjugating the second argument changes the same local response into the
positive Hermitian sum of squares. -/
theorem normalizedHermitianTrace_affine (l : ℝ) :
    normalizedHermitianTrace (affineComplexResponse l) = 1 + l ^ 2 := by
  simp [normalizedHermitianTrace, affineComplexResponse,
    Algebra.traceForm_apply, Algebra.trace_complex_apply,
    Complex.mul_re, Complex.mul_im]
  ring

/-- Reverse uniqueness: within the affine family `1+i*c`, reproducing the
screening factor fixes the magnitude of the timelike coefficient. -/
theorem intrinsicTrace_eq_screening_iff (c l : ℝ) :
    normalizedIntrinsicTrace (affineComplexResponse c) = screening l ↔
      c ^ 2 = l ^ 2 := by
  rw [normalizedIntrinsicTrace_affine]
  unfold screening
  constructor <;> intro h <;> linarith

/-! ## The same realization in the global quartic power basis

The matrix below is the genuine quartic trace-form matrix whose identification
with `Tr(x*y)` and signature `(3,1)` are proved in the PDT canon.  Here it is
used only as an explicit real matrix.  Its standard rational diagonalization
contains the normalized axes declared below.
-/

/-- Quartic trace-form matrix in the power basis `1,Q,Q^2,Q^3`. -/
def quarticTraceMatrix : Matrix (Fin 4) (Fin 4) ℝ :=
  !![4, 0, 0, 3;
     0, 0, 3, 4;
     0, 3, 4, 0;
     3, 4, 0, 3]

/-- Coordinates in the quartic power basis `1,Q,Q^2,Q^3`. -/
structure QuarticTraceCoords where
  c0 : ℝ
  c1 : ℝ
  c2 : ℝ
  c3 : ℝ

@[ext] theorem quarticTraceCoords_ext {x y : QuarticTraceCoords}
    (h0 : x.c0 = y.c0) (h1 : x.c1 = y.c1)
    (h2 : x.c2 = y.c2) (h3 : x.c3 = y.c3) : x = y := by
  cases x
  cases y
  simp_all

/-- The bilinear pairing represented by the quartic trace matrix. -/
def quarticTracePair (x y : QuarticTraceCoords) : ℝ :=
  4 * x.c0 * y.c0 + 3 * x.c0 * y.c3 +
  3 * x.c1 * y.c2 + 4 * x.c1 * y.c3 +
  3 * x.c2 * y.c1 + 4 * x.c2 * y.c2 +
  3 * x.c3 * y.c0 + 4 * x.c3 * y.c1 + 3 * x.c3 * y.c3

/-- Normalized identity direction `1/2`. -/
noncomputable def quarticSpaceUnit : QuarticTraceCoords :=
  ⟨1 / 2, 0, 0, 0⟩

/-- Normalized negative direction `(4Q-3Q^2)/6`. -/
noncomputable def quarticTimeUnit : QuarticTraceCoords :=
  ⟨0, 2 / 3, -1 / 2, 0⟩

/-- The timelike observer `u = 4Q-3Q^2` used in the quartic time geometry. -/
noncomputable def quarticTimeObserver : QuarticTraceCoords :=
  ⟨0, 4, -3, 0⟩

/-- Coordinatewise scalar multiplication. -/
noncomputable def quarticCoordsScale (a : ℝ) (x : QuarticTraceCoords) :
    QuarticTraceCoords :=
  ⟨a * x.c0, a * x.c1, a * x.c2, a * x.c3⟩

/-- Coordinatewise addition. -/
noncomputable def quarticCoordsAdd (x y : QuarticTraceCoords) :
    QuarticTraceCoords :=
  ⟨x.c0 + y.c0, x.c1 + y.c1, x.c2 + y.c2, x.c3 + y.c3⟩

/-- The identity direction has trace square `+1`. -/
theorem quarticSpaceUnit_sq :
    quarticTracePair quarticSpaceUnit quarticSpaceUnit = 1 := by
  norm_num [quarticTracePair, quarticSpaceUnit]

/-- The distinguished negative direction has trace square `-1`. -/
theorem quarticTimeUnit_sq :
    quarticTracePair quarticTimeUnit quarticTimeUnit = -1 := by
  norm_num [quarticTracePair, quarticTimeUnit]

/-- The time observer has the established trace square `-36`. -/
theorem quarticTimeObserver_sq :
    quarticTracePair quarticTimeObserver quarticTimeObserver = -36 := by
  norm_num [quarticTracePair, quarticTimeObserver]

/-- Dividing the established observer by six gives the normalized negative
axis used in the screening identity. -/
theorem quarticTimeUnit_eq_normalized_observer :
    quarticCoordsScale (1 / 6) quarticTimeObserver = quarticTimeUnit := by
  ext <;>
    norm_num [quarticCoordsScale, quarticTimeObserver, quarticTimeUnit]

/-- The normalized identity and timelike axes are trace-orthogonal. -/
theorem quarticSpaceTime_orthogonal :
    quarticTracePair quarticSpaceUnit quarticTimeUnit = 0 := by
  norm_num [quarticTracePair, quarticSpaceUnit, quarticTimeUnit]

/-- The affine field-space response along the normalized timelike axis. -/
noncomputable def quarticTraceResponse (l : ℝ) : QuarticTraceCoords :=
  ⟨1 / 2, 2 * l / 3, -l / 2, 0⟩

/-- The same response written directly as unit background plus `l/6` times
the timelike observer used in the time construction. -/
noncomputable def quarticTimeObserverResponse (l : ℝ) : QuarticTraceCoords :=
  quarticCoordsAdd quarticSpaceUnit
    (quarticCoordsScale (l / 6) quarticTimeObserver)

/-- The time-observer and diagonal-axis presentations are exactly equal. -/
theorem quarticTimeObserverResponse_eq (l : ℝ) :
    quarticTimeObserverResponse l = quarticTraceResponse l := by
  ext <;>
    norm_num [quarticTimeObserverResponse, quarticCoordsAdd,
      quarticCoordsScale, quarticSpaceUnit, quarticTimeObserver,
      quarticTraceResponse] <;>
    ring

/-- The genuine quartic trace matrix evaluates the affine response to the
screening difference of squares. -/
theorem quarticTraceResponse_sq (l : ℝ) :
    quarticTracePair (quarticTraceResponse l) (quarticTraceResponse l) =
      screening l := by
  norm_num [quarticTracePair, quarticTraceResponse, quarticSpaceUnit,
    quarticTimeUnit, screening]
  ring

/-- The time observer itself therefore gives the screening norm. -/
theorem quarticTimeObserverResponse_sq (l : ℝ) :
    quarticTracePair (quarticTimeObserverResponse l)
      (quarticTimeObserverResponse l) = screening l := by
  rw [quarticTimeObserverResponse_eq]
  exact quarticTraceResponse_sq l

/-! ## Minimal induced-gravity coefficient

The quartic trace form is used here as an internal scalar prefactor for a
separate dynamical spacetime metric.  No curvature is attributed to the
constant trace matrix itself.
-/

/-- Quadratic weight of a background/time pair, expressed only through its
three pairings. -/
def lorentzPairWeight
    (backgroundSq timeSq backgroundTime l : ℝ) : ℝ :=
  backgroundSq + 2 * l * backgroundTime + l ^ 2 * timeSq

/-- Every normalized orthogonal unit-timelike direction gives the same
screening weight.  The coefficient is therefore independent of the particular
observer representative once these invariant pairings are fixed. -/
theorem normalizedLorentzPair_weight
    (backgroundSq timeSq backgroundTime l : ℝ)
    (hbackground : backgroundSq = 1)
    (htime : timeSq = -1)
    (horthogonal : backgroundTime = 0) :
    lorentzPairWeight backgroundSq timeSq backgroundTime l = screening l := by
  simp [lorentzPairWeight, screening, hbackground, htime, horthogonal]
  ring

/-- The unscreened non-reduced Planck-square coefficient of the existing
induced-gravity term `(xi/2) phi^2 R`. -/
noncomputable def inducedPlanckSq (xi phi : ℝ) : ℝ :=
  8 * Real.pi * xi * phi ^ 2

/-- At conformal coupling `xi=1/6`, the filed induced-gravity normalization is
exactly `(4*pi/3) phi^2`. -/
theorem inducedPlanckSq_conformal (phi : ℝ) :
    inducedPlanckSq (1 / 6) phi = (4 * Real.pi / 3) * phi ^ 2 := by
  unfold inducedPlanckSq
  ring

/-- Minimal quartic trace completion of the induced Planck-square coefficient. -/
noncomputable def traceInducedPlanckSq (xi phi l : ℝ) : ℝ :=
  inducedPlanckSq xi phi *
    quarticTracePair (quarticTimeObserverResponse l)
      (quarticTimeObserverResponse l)

/-- The completed induced Planck square is multiplied by the screening
coefficient. -/
theorem traceInducedPlanckSq_eq (xi phi l : ℝ) :
    traceInducedPlanckSq xi phi l = screening l * inducedPlanckSq xi phi := by
  rw [traceInducedPlanckSq, quarticTimeObserverResponse_sq]
  ring

/-- The conformally coupled trace completion has the displayed screened
Planck-square normalization. -/
theorem traceInducedPlanckSq_conformal (phi l : ℝ) :
    traceInducedPlanckSq (1 / 6) phi l =
      (4 * Real.pi / 3) * phi ^ 2 * screening l := by
  rw [traceInducedPlanckSq_eq, inducedPlanckSq_conformal]
  ring

/-- Newton's coupling corresponding to a nonzero Planck-square coefficient. -/
noncomputable def newtonFromPlanckSq (mSq : ℝ) : ℝ :=
  1 / mSq

/-- For nonzero baseline and screening coefficients, the trace completion
divides Newton's coupling by the same screening factor. -/
theorem traceInducedNewton_eq
    (xi phi l : ℝ)
    (hbase : inducedPlanckSq xi phi ≠ 0)
    (hscreen : screening l ≠ 0) :
    newtonFromPlanckSq (traceInducedPlanckSq xi phi l) =
      newtonFromPlanckSq (inducedPlanckSq xi phi) / screening l := by
  rw [traceInducedPlanckSq_eq]
  unfold newtonFromPlanckSq
  field_simp [hbase, hscreen]

/-! ## Conditional closure of the deposited Planck chain -/

/-- The unscreened Planck scale written in the deposited gravity paper.  This
definition records the formula; it does not assert its physical derivation. -/
noncomputable def depositedBaselinePlanck (me rho q : ℝ) : ℝ :=
  me * (rho * q) ^ 112 / Real.pi ^ 2

/-- If the conformal condensate is normalized to the deposited unscreened
scale, the trace-completed induced action has exactly the screened baseline
Planck square. -/
theorem conditional_pdt_planck_chain
    (me rho q phi l : ℝ)
    (hphi : (4 * Real.pi / 3) * phi ^ 2 =
      depositedBaselinePlanck me rho q ^ 2) :
    traceInducedPlanckSq (1 / 6) phi l =
      screening l * depositedBaselinePlanck me rho q ^ 2 := by
  rw [traceInducedPlanckSq_conformal, hphi]
  ring

/-- Specializing the response to `lambda4(q)` gives the rational quartic
screening coefficient used in the gravity formula. -/
theorem conditional_pdt_quartic_planck_chain
    (me rho q phi : ℝ)
    (hq : q ≠ 0)
    (hphi : (4 * Real.pi / 3) * phi ^ 2 =
      depositedBaselinePlanck me rho q ^ 2) :
    traceInducedPlanckSq (1 / 6) phi (lambda4 q) =
      ((2 * q - 1) / q ^ 2) * depositedBaselinePlanck me rho q ^ 2 := by
  rw [conditional_pdt_planck_chain me rho q phi (lambda4 q) hphi]
  unfold screening lambda4
  field_simp [hq]
  ring

/-- A general quadratic internal response in the induced Einstein coefficient
is forced to the same screening law by background normalization, time reversal
and the unit-null boundary. -/
noncomputable def quadraticInducedPlanckSq
    (xi phi a b c l : ℝ) : ℝ :=
  inducedPlanckSq xi phi * quadraticSpacetimeScalar a b c 1 l

theorem quadraticInducedPlanckSq_forced
    (xi phi a b c l : ℝ)
    (hbase : quadraticSpacetimeScalar a b c 1 0 = 1)
    (heven : ∀ t : ℝ,
      quadraticSpacetimeScalar a b c 1 t =
        quadraticSpacetimeScalar a b c 1 (-t))
    (hnull : quadraticSpacetimeScalar a b c 1 1 = 0) :
    quadraticInducedPlanckSq xi phi a b c l =
      screening l * inducedPlanckSq xi phi := by
  unfold quadraticInducedPlanckSq
  rw [normalized_even_null_quadratic_forced a b c l hbase heven hnull]
  ring

/-- Curvature weight obtained by subtracting a residue compensator of relative
amplitude `l` from a scalar amplitude `phi`. -/
def residueCompensatedCurvatureWeight (phi l : ℝ) : ℝ :=
  phi ^ 2 - (l * phi) ^ 2

theorem residueCompensatedCurvatureWeight_eq (phi l : ℝ) :
    residueCompensatedCurvatureWeight phi l = screening l * phi ^ 2 := by
  simp [residueCompensatedCurvatureWeight, screening]
  ring

/-- After canonical normalization, only the ratio of a curvature weight to a
kinetic weight is invariant under a constant scalar-field rescaling. -/
noncomputable def canonicalRelativeCurvatureWeight
    (kineticWeight curvatureWeight : ℝ) : ℝ :=
  curvatureWeight / kineticWeight

/-- A uniform nonzero trace factor on both kinetic and curvature terms is a
field-normalization effect and leaves unit relative curvature weight. -/
theorem commonWeight_cancels (s : ℝ) (hs : s ≠ 0) :
    canonicalRelativeCurvatureWeight s s = 1 := by
  simp [canonicalRelativeCurvatureWeight, hs]

/-- A trace factor survives when it weights curvature relative to an already
canonical scalar kinetic term. -/
theorem curvatureOnlyWeight_survives (s : ℝ) :
    canonicalRelativeCurvatureWeight 1 s = s := by
  simp [canonicalRelativeCurvatureWeight]

/-- There is only one nonnegative defect coordinate with the required norm. -/
theorem nonnegative_defect_unique
    (l d e : ℝ)
    (hd : d ^ 2 = screening l) (he : e ^ 2 = screening l)
    (hd0 : 0 ≤ d) (he0 : 0 ≤ e) :
    d = e := by
  nlinarith

theorem constitutiveBlock_det (l : ℝ) :
    Matrix.det (constitutiveBlock l) = screening l := by
  simp [constitutiveBlock, Matrix.det_fin_two, screening]
  ring

/-- Before normalization the associated twist squares to
`-(1-l^2) I`, not to `-I`. -/
theorem raw_constitutive_twist_sq (l : ℝ) :
    (symplecticBlock * constitutiveBlock l) *
        (symplecticBlock * constitutiveBlock l) =
      (-screening l) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [symplecticBlock, constitutiveBlock, Matrix.mul_apply,
      Fin.sum_univ_succ, screening] <;>
    ring

/-- The raw constitutive block is conformally symplectic, with multiplier
`1-l^2`. -/
theorem raw_constitutive_conformal_symplectic (l : ℝ) :
    (constitutiveBlock l).transpose * symplecticBlock * constitutiveBlock l =
      screening l • symplecticBlock := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [symplecticBlock, constitutiveBlock, Matrix.transpose_apply,
      Matrix.mul_apply, Fin.sum_univ_succ, screening] <;>
    ring

/-- If `d^2=1-l^2`, the normalized block has determinant one. -/
theorem unimodularConstitutive_det
    (l d : ℝ) (hd : d ^ 2 = screening l) (hd0 : d ≠ 0) :
    Matrix.det (unimodularConstitutive l d) = 1 := by
  simp [unimodularConstitutive, constitutiveBlock, Matrix.det_fin_two]
  unfold screening at hd
  field_simp [hd0]
  nlinarith

/-- The normalized constitutive shape defines a genuine complex structure
when composed with the symplectic form. -/
theorem unimodular_constitutive_twist_sq
    (l d : ℝ) (hd : d ^ 2 = screening l) (hd0 : d ≠ 0) :
    (symplecticBlock * unimodularConstitutive l d) *
        (symplecticBlock * unimodularConstitutive l d) =
      -(1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [symplecticBlock, unimodularConstitutive, constitutiveBlock,
      Matrix.mul_apply, Fin.sum_univ_succ] <;>
    unfold screening at hd <;>
    field_simp [hd0] <;>
    nlinarith

/-- The determinant-one constitutive shape preserves the canonical
symplectic form exactly. -/
theorem unimodularConstitutive_symplectic
    (l d : ℝ) (hd : d ^ 2 = screening l) (hd0 : d ≠ 0) :
    (unimodularConstitutive l d).transpose * symplecticBlock *
        unimodularConstitutive l d = symplecticBlock := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [symplecticBlock, unimodularConstitutive, constitutiveBlock,
      Matrix.transpose_apply, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    unfold screening at hd <;>
    field_simp [hd0] <;>
    nlinarith

/-- The raw block is the product of the scalar scale `d` and its determinant-
one constitutive shape. -/
theorem constitutiveBlock_scale_shape
    (l d : ℝ) (hd0 : d ≠ 0) :
    constitutiveBlock l = d • unimodularConstitutive l d := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [constitutiveBlock, unimodularConstitutive, hd0]

/-- Eliminating the second channel from the determinant-one shape leaves the
single square-root stiffness `d`. -/
theorem unimodularConstitutive_schur
    (l d : ℝ) (hd : d ^ 2 = screening l) (hd0 : d ≠ 0) :
    1 / d - (-l / d) ^ 2 / (1 / d) = d := by
  unfold screening at hd
  field_simp [hd0]
  nlinarith

/-- Multiplying the determinant-one shape by its scalar scale supplies the
second factor of `d`, so the full Schur complement is `d^2=1-l^2`. -/
theorem scale_times_unimodular_schur
    (l d : ℝ) (hd : d ^ 2 = screening l) :
    d * d = screening l := by
  nlinarith

/-! ## A first-order mode check

This finite oscillator is the internal algebra of a doubled canonical mode.
It shows why the common action scale and the determinant-one constitutive
shape multiply in the second-order response.  It is not by itself a
gravitational field action.
-/

/-- A first-order doubled mode with overall scale `a` and symmetric
Hamiltonian block `[[c,-s],[-s,c]]`. -/
noncomputable def firstOrderMode
    (a c s position velocity momentum : ℝ) : ℝ :=
  a * (momentum * velocity -
    (c * position ^ 2 - 2 * s * position * momentum +
      c * momentum ^ 2) / 2)

/-- Eliminating the canonical partner leaves a second-order mode with overall
coefficient `a/c`; the mixed term is a total derivative when `s` is constant. -/
theorem firstOrderMode_at_momentum_stationary
    (a c s position velocity : ℝ)
    (hc : c ≠ 0) (hcs : c ^ 2 - s ^ 2 = 1) :
    firstOrderMode a c s position velocity
        ((velocity + s * position) / c) =
      a / (2 * c) *
        (velocity ^ 2 - position ^ 2 +
          2 * s * position * velocity) := by
  have hc2 : c ^ 2 = 1 + s ^ 2 := by linarith
  unfold firstOrderMode
  field_simp [hc]
  rw [hc2]
  ring

/-- With `c=1/d`, `s=l/d`, and the common action scale `a=d`, the even
second-order kinetic/potential coefficient is exactly `(1-l^2)/2`. -/
theorem quarticScale_firstOrderMode_reduction
    (l d position velocity : ℝ)
    (hd : d ^ 2 = screening l) (hd0 : d ≠ 0) :
    firstOrderMode d (1 / d) (l / d) position velocity
        ((velocity + (l / d) * position) / (1 / d)) =
      screening l / 2 *
        (velocity ^ 2 - position ^ 2 +
          2 * (l / d) * position * velocity) := by
  have hc : (1 / d : ℝ) ≠ 0 := one_div_ne_zero hd0
  have hcs : (1 / d : ℝ) ^ 2 - (l / d) ^ 2 = 1 := by
    unfold screening at hd
    field_simp [hd0]
    nlinarith
  rw [firstOrderMode_at_momentum_stationary d (1 / d) (l / d)
    position velocity hc hcs]
  rw [← hd]
  field_simp [hd0]

/-- A source coupled to one selected member of the doubled pair sees the full
inverse screening response when the common scale and constitutive shape both
use the same defect `d`. -/
theorem scaledUnimodular_source_solution
    (l d source : ℝ)
    (hd0 : d ≠ 0)
    (hs : screening l ≠ 0) :
    let position := source / screening l
    let momentum := l * position
    d * ((1 / d) * position - (l / d) * momentum) = source ∧
    d * ((1 / d) * momentum - (l / d) * position) = 0 := by
  dsimp
  constructor
  · field_simp [hd0, hs]
    simp [screening]
  · field_simp [hd0]
    ring

/-- The surviving coefficient after eliminating the second coordinate of a
general symmetric two-channel quadratic block, expressed relative to the first
diagonal coefficient. -/
noncomputable def relativeSchur (a b c : ℝ) : ℝ :=
  (a - b ^ 2 / c) / a

/-- Running the screening formula backward: for nonzero diagonal entries, a
general two-channel block has relative Schur coefficient `1-l^2` exactly when
its normalization-invariant squared overlap is `l^2`. -/
theorem relativeSchur_eq_screening_iff
    (a b c l : ℝ) (ha : a ≠ 0) (hc : c ≠ 0) :
    relativeSchur a b c = screening l ↔ b ^ 2 = l ^ 2 * a * c := by
  unfold relativeSchur screening
  constructor <;> intro h
  · field_simp [ha, hc] at h
    nlinarith
  · field_simp [ha, hc]
    nlinarith

/-- A two-parameter statistical family that depends on only one scalar
combination has a rank-one Fisher matrix.  Eliminating either identifiable
coordinate leaves zero relative partial information.  Here `u,w` are the two
components of the gradient of that scalar combination and `variance` is its
one-dimensional Fisher information. -/
theorem oneStatistic_twoParameterFisher_relativeSchur_zero
    (variance u w : ℝ)
    (hvariance : variance ≠ 0) (hu : u ≠ 0) (hw : w ≠ 0) :
    relativeSchur (variance * u ^ 2) (variance * u * w)
      (variance * w ^ 2) = 0 := by
  unfold relativeSchur
  field_simp [hvariance, hu, hw]
  ring

/-- Independent normalized score directions have zero cross-information, so
eliminating the second direction leaves all of the first direction's Fisher
information. -/
theorem independentFisher_relativeSchur_one
    (a c : ℝ) (ha : a ≠ 0) :
    relativeSchur a 0 c = 1 := by
  simp [relativeSchur, ha]

/-- Opposite affine responses have the same difference-of-squares factor. -/
theorem paired_response (l : ℝ) :
    (1 - l) * (1 + l) = screening l := by
  simp [screening]
  ring

/-- The response is positive in the correlation range `-1 < l < 1`. -/
theorem screening_pos {l : ℝ} (h : -1 < l ∧ l < 1) :
    0 < screening l := by
  have hleft : 0 < 1 - l := sub_pos.mpr h.2
  have hright : 0 < 1 + l := by linarith [h.1]
  rw [← paired_response l]
  exact mul_pos hleft hright

/-- The exact quartic identity used in the gravity formula. -/
theorem quartic_screening_identity (q : ℝ) (hq : q ≠ 0) :
    screening (lambda4 q) = (2 * q - 1) / q ^ 2 := by
  unfold screening lambda4
  field_simp [hq]
  ring

/-- `lambda4` is the relative increment of a dilation by `q`: the part of a
unit interval lying above the inverse-image cutoff `1/q`. -/
theorem lambda4_eq_relative_increment (q : ℝ) (hq : q ≠ 0) :
    lambda4 q = (q - 1) / q := by
  unfold lambda4
  field_simp [hq]

/-- The hyperbolic squeeze ratio of the quartic residue simplifies to
`2q-1`.  If `lambda4=tanh theta`, this ratio is `exp(2 theta)`. -/
theorem quartic_squeeze_ratio (q : ℝ) (hq : q ≠ 0) :
    (1 + lambda4 q) / (1 - lambda4 q) = 2 * q - 1 := by
  unfold lambda4
  field_simp [hq]
  ring

/-! ## The residue amplitude from the quartic companion operator -/

/-- The nonnegative incidence/companion matrix of the substitution
`1 -> 2, 2 -> 3, 3 -> 4, 4 -> 12`. -/
def quarticCompanion : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0,0,0,1; 1,0,0,1; 0,1,0,0; 0,0,1,0]

/-- The integral inverse of `quarticCompanion`. -/
def quarticCompanionInv : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-1,1,0,0; 0,0,1,0; 0,0,0,1; 1,0,0,0]

theorem quarticCompanion_mul_inv :
    quarticCompanion * quarticCompanionInv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [quarticCompanion, quarticCompanionInv, Matrix.mul_apply,
      Fin.sum_univ_succ]

theorem quarticCompanion_inv_mul :
    quarticCompanionInv * quarticCompanion = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [quarticCompanion, quarticCompanionInv, Matrix.mul_apply,
      Fin.sum_univ_succ]

/-- The positive-root eigenvector in the substitution's natural basis. -/
noncomputable def quarticPerronVector (q : ℝ) : Fin 4 → ℝ :=
  ![1, q ^ 3, q ^ 2, q]

theorem quarticCompanion_perron (q : ℝ) (hq : q ^ 4 = q + 1) :
    quarticCompanion.mulVec (quarticPerronVector q) =
      fun i => q * quarticPerronVector q i := by
  funext i
  fin_cases i <;>
    simp [quarticCompanion, quarticPerronVector, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] <;>
    nlinarith [hq]

/-- The total mass of the Perron frequency vector. -/
def quarticPerronMass (q : ℝ) : ℝ := 1 + q + q ^ 2 + q ^ 3

/-- After normalizing the positive Perron vector by total letter count, the
frequency of the renewal letter `1` is exactly `lambda4`. Standard primitive-
substitution theory identifies this normalized Perron coordinate with the
unique invariant letter frequency. -/
theorem quarticRenewalFrequency (q : ℝ) (hq : q ^ 4 = q + 1) (hq1 : 1 < q) :
    1 / quarticPerronMass q = lambda4 q := by
  have hq0 : q ≠ 0 := by linarith
  have hs : quarticPerronMass q ≠ 0 := by
    unfold quarticPerronMass
    positivity
  unfold quarticPerronMass lambda4 at *
  field_simp [hq0, hs]
  nlinarith [hq]

/-- Current state minus one inverse companion step. -/
def quarticResidual : Matrix (Fin 4) (Fin 4) ℝ :=
  !![2,-1,0,0; 0,1,-1,0; 0,0,1,-1; -1,0,0,1]

theorem quarticResidual_eq_one_sub_inv :
    quarticResidual = 1 - quarticCompanionInv := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [quarticResidual, quarticCompanionInv]

/-- On the distinguished positive eigenline, the inverse-step residue has
exact eigen-amplitude `lambda4`. -/
theorem quarticResidual_perron (q : ℝ) (hq : q ^ 4 = q + 1) (hq0 : q ≠ 0) :
    quarticResidual.mulVec (quarticPerronVector q) =
      fun i => lambda4 q * quarticPerronVector q i := by
  have hl := lambda4_eq_relative_increment q hq0
  funext i
  fin_cases i <;>
    simp [quarticResidual, quarticPerronVector,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
    rw [hl] <;>
    field_simp [hq0] <;>
    nlinarith [hq]

/-- The quartic residual is non-normal in the standard Euclidean coordinates.
This prevents silently treating its Perron eigenvalue as a singular value of a
one-field symmetric kinetic form. -/
theorem quarticResidual_not_normal :
    quarticResidual.transpose * quarticResidual ≠
      quarticResidual * quarticResidual.transpose := by
  intro h
  have hij := congrArg (fun M => M 0 1) h
  norm_num [quarticResidual, Matrix.mul_apply, Matrix.transpose_apply,
    Fin.sum_univ_succ] at hij

/-- A general diagonal weight on the four quartic coordinates. -/
def diagonalWeight4 (w₀ w₁ w₂ w₃ : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![w₀,0,0,0; 0,w₁,0,0; 0,0,w₂,0; 0,0,0,w₃]

/-- No nondegenerate positive diagonal information metric can make the full
quartic residual self-adjoint. The one-way `0 -> 1` matrix entry already
forces the first diagonal weight to vanish. -/
theorem quarticResidual_no_diagonal_symmetrizer
    (w₀ w₁ w₂ w₃ : ℝ) (hw₀ : w₀ ≠ 0) :
    diagonalWeight4 w₀ w₁ w₂ w₃ * quarticResidual ≠
      quarticResidual.transpose * diagonalWeight4 w₀ w₁ w₂ w₃ := by
  intro h
  have hij := congrArg (fun M => M 0 1) h
  norm_num [diagonalWeight4, quarticResidual, Matrix.mul_apply,
    Matrix.transpose_apply, Fin.sum_univ_succ] at hij
  exact hw₀ hij

/-- The left Perron mode of the quartic residual. Its coordinates are the
reverse of the right Perron vector. -/
noncomputable def quarticLeftPerronVector (q : ℝ) : Fin 4 → ℝ :=
  ![1, q, q ^ 2, q ^ 3]

theorem quarticResidual_left_perron
    (q : ℝ) (hq : q ^ 4 = q + 1) (hq0 : q ≠ 0) :
    quarticResidual.transpose.mulVec (quarticLeftPerronVector q) =
      fun i => lambda4 q * quarticLeftPerronVector q i := by
  have hl := lambda4_eq_relative_increment q hq0
  funext i
  fin_cases i <;>
    simp [quarticResidual, quarticLeftPerronVector, Matrix.transpose_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
    rw [hl] <;>
    field_simp [hq0] <;>
    nlinarith [hq]

/-- The scale-independent left/right Perron pairing. -/
theorem quarticPerron_pairing (q : ℝ) (hq : q ^ 4 = q + 1) :
    dotProduct (quarticLeftPerronVector q) (quarticPerronVector q) =
      3 * q + 4 := by
  simp [quarticLeftPerronVector, quarticPerronVector, dotProduct,
    Fin.sum_univ_succ]
  nlinarith [hq]

/-- The biorthogonally normalized residual coefficient. -/
noncomputable def quarticBiResidualCoefficient (q : ℝ) : ℝ :=
  dotProduct (quarticLeftPerronVector q)
      (quarticResidual.mulVec (quarticPerronVector q)) /
    dotProduct (quarticLeftPerronVector q) (quarticPerronVector q)

/-- On the positive quartic Perron mode, the non-normal residual contributes
exactly `lambda4` when paired with its left mode. -/
theorem quarticBiResidualCoefficient_eq_lambda4
    (q : ℝ) (hq : q ^ 4 = q + 1) (hq1 : 1 < q) :
    quarticBiResidualCoefficient q = lambda4 q := by
  have hq0 : q ≠ 0 := by linarith
  have hden :
      dotProduct (quarticLeftPerronVector q) (quarticPerronVector q) ≠ 0 := by
    rw [quarticPerron_pairing q hq]
    nlinarith
  unfold quarticBiResidualCoefficient
  rw [quarticResidual_perron q hq hq0]
  have hdot :
      dotProduct (quarticLeftPerronVector q)
          (fun i => lambda4 q * quarticPerronVector q i) =
        lambda4 q *
          dotProduct (quarticLeftPerronVector q) (quarticPerronVector q) := by
    simp [dotProduct, Fin.sum_univ_succ]
    ring
  rw [hdot]
  field_simp [hden]

/-- The normalized Perron inverse-step residue, used as a nondynamical
curvature compensator, gives the exact rational quartic screening weight. -/
theorem quarticPerron_compensator_curvature
    (q phi : ℝ) (hq : q ^ 4 = q + 1) (hq1 : 1 < q) :
    residueCompensatedCurvatureWeight phi
        (quarticBiResidualCoefficient q) =
      ((2 * q - 1) / q ^ 2) * phi ^ 2 := by
  have hq0 : q ≠ 0 := by linarith
  rw [quarticBiResidualCoefficient_eq_lambda4 q hq hq1]
  rw [residueCompensatedCurvatureWeight_eq]
  rw [quartic_screening_identity q hq0]

/-! ## Minimal unitary completion of the residue contraction -/

/-- Once a real contraction coefficient `l` is fixed, conservation of squared
norm forces the squared complementary coefficient to be `1-l^2`. -/
theorem defect_sq_forced (l d : ℝ) (hcomplete : l ^ 2 + d ^ 2 = 1) :
    d ^ 2 = screening l := by
  unfold screening
  linarith

/-- The positive defect amplitude has the required square whenever the
screening coefficient is nonnegative. -/
theorem defect_sqrt_sq (l : ℝ) (h : 0 ≤ screening l) :
    (Real.sqrt (screening l)) ^ 2 = screening l := by
  exact Real.sq_sqrt h

/-- Either row of the scalar Julia dilation has unit norm when the defect
coefficient has the forced square. -/
theorem julia_row_norm (l d : ℝ) (hdefect : d ^ 2 = screening l) :
    l ^ 2 + d ^ 2 = 1 := by
  rw [hdefect]
  simp [screening]

/-- The two rows of the scalar Julia dilation `[[l,d],[d,-l]]` are orthogonal. -/
theorem julia_rows_orthogonal (l d : ℝ) :
    l * d + d * (-l) = 0 := by
  ring

/-- The scalar Julia block is an involution. This is the algebraic reason it
can be read both as a Hermitian two-channel observable and as a one-tick
unitary evolution. -/
def juliaBlock (l d : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![l,d; d,-l]

theorem juliaBlock_sq (l d : ℝ) (hdefect : d ^ 2 = screening l) :
    juliaBlock l d * juliaBlock l d = 1 := by
  have hsum : l * l + d * d = 1 := by
    simp [screening] at hdefect
    nlinarith [hdefect]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [juliaBlock, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    nlinarith [hsum]

/-! ## Lorentzian Hodge-pair realization

On the complexified span of a bivector and its dual, Lorentzian Hodge duality
has eigenvalues `+i` and `-i`. Multiplication by `i` converts it to an
involution. The non-scalar response `I-i*l*star` then has opposite real chiral
weights and determinant `1-l^2`.
-/

/-- Lorentzian Hodge star on one complex chiral pair. -/
def lorentzHodge : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.I, 0; 0, -Complex.I]

theorem lorentzHodge_sq : lorentzHodge * lorentzHodge = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [lorentzHodge, Matrix.mul_apply, Fin.sum_univ_succ,
      Complex.I_mul_I]

/-- The complexified chiral response `I-i*l*star`. -/
noncomputable def chiralAreaResponse (l : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  1 - (Complex.I * (l : ℂ)) • lorentzHodge

/-- Its two real chiral weights are `1+l` and `1-l`. -/
theorem chiralAreaResponse_eq (l : ℝ) :
    chiralAreaResponse l =
      !![(1 + (l : ℂ)), 0; 0, (1 - (l : ℂ))] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralAreaResponse, lorentzHodge]
  all_goals
    rw [mul_comm Complex.I (l : ℂ), mul_assoc, Complex.I_mul_I]
    ring

/-- The determinant on one chiral pair is the screening coefficient. Unlike
the scalar Kraus split, this operator acts differently on the two chiral
subspaces. -/
theorem chiralAreaResponse_det (l : ℝ) :
    Matrix.det (chiralAreaResponse l) = (screening l : ℂ) := by
  rw [chiralAreaResponse_eq]
  simp [Matrix.det_fin_two, screening]
  ring

/-- Multiplying the response by its orientation flip removes chirality and
leaves the scalar screening stiffness. -/
theorem chiralAreaResponse_mul_flip (l : ℝ) :
    chiralAreaResponse l * chiralAreaResponse (-l) =
      (screening l : ℂ) • 1 := by
  rw [chiralAreaResponse_eq, chiralAreaResponse_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, screening] <;>
    ring

/-- At the quartic residue, the chiral Hodge-pair determinant is exactly the
deposited gravity-screening rational function. -/
theorem quartic_chiralAreaResponse_det (q : ℝ) (hq : q ≠ 0) :
    Matrix.det (chiralAreaResponse (lambda4 q)) =
      (((2 * q - 1) / q ^ 2 : ℝ) : ℂ) := by
  rw [chiralAreaResponse_det, quartic_screening_identity q hq]

/-- On the full six-dimensional bivector space in four dimensions, the two
chiral eigenweights each occur three times, so the full determinant would
carry the third power of the screening coefficient. This distinguishes a
single horizon binormal/area pair from a determinant over all bivectors. -/
theorem fullBivector_chiralDet (l : ℝ) :
    (1 + l) ^ 3 * (1 - l) ^ 3 = screening l ^ 3 := by
  simp [screening]
  ring

/-- If the two chiral weights are kinetic stiffnesses and an orientation-even
source reads the normalized average of their inverse responses, the resulting
compliance is exactly enhanced by `1/(1-l^2)`. -/
theorem orientationEven_chiralCompliance (l : ℝ)
    (hplus : 1 + l ≠ 0) (hminus : 1 - l ≠ 0) :
    (1 / 2 : ℝ) * (1 / (1 + l) + 1 / (1 - l)) =
      1 / screening l := by
  have hs : 1 - l ^ 2 ≠ 0 := by
    rw [show 1 - l ^ 2 = (1 - l) * (1 + l) by ring]
    exact mul_ne_zero hminus hplus
  unfold screening
  field_simp [hplus, hminus, hs]
  ring

/-- At the positive quartic root, the orientation-even inverse chiral response
is exactly the reciprocal screening factor appearing in Newton's coupling. -/
theorem quartic_orientationEven_chiralCompliance (q : ℝ) (hq : 1 < q) :
    (1 / 2 : ℝ) *
        (1 / (1 + lambda4 q) + 1 / (1 - lambda4 q)) =
      q ^ 2 / (2 * q - 1) := by
  have hq0 : q ≠ 0 := by linarith
  have hplus : 1 + lambda4 q ≠ 0 := by
    intro h
    unfold lambda4 at h
    field_simp [hq0] at h
    nlinarith
  have hminus : 1 - lambda4 q ≠ 0 := by
    intro h
    unfold lambda4 at h
    field_simp [hq0] at h
    nlinarith
  rw [orientationEven_chiralCompliance (lambda4 q) hplus hminus]
  rw [quartic_screening_identity q hq0]
  have hden : 2 * q - 1 ≠ 0 := by nlinarith
  field_simp [hq0, hden]

/-! ## A real doubled kinetic realization

The complex chiral involution can be realified by retaining a second Hodge-
paired mode. The resulting quadratic action is real. Eliminating the second
mode produces the same Schur complement `1-l^2` and hence the reciprocal
source response.
-/

/-- Realification of the complex chirality involution on two real Hodge-paired
modes, in coordinates `(x₁,x₂,y₁,y₂)`. -/
def realifiedChirality : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0,0,0,1; 0,0,-1,0; 0,-1,0,0; 1,0,0,0]

theorem realifiedChirality_transpose :
    realifiedChirality.transpose = realifiedChirality := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [realifiedChirality, Matrix.transpose_apply]

theorem realifiedChirality_sq :
    realifiedChirality * realifiedChirality = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [realifiedChirality, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The real doubled response operator `I+lR`, written explicitly so its
coordinate action is transparent. -/
def realDoubledResponse (l : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1,0,0,l; 0,1,-l,0; 0,-l,1,0; l,0,0,1]

def realifiedPlus (x₁ x₂ : ℝ) : Fin 4 → ℝ := ![x₁,x₂,-x₂,x₁]
def realifiedMinus (x₁ x₂ : ℝ) : Fin 4 → ℝ := ![x₁,x₂,x₂,-x₁]

/-- The plus realified-chiral plane has kinetic weight `1+l`. -/
theorem realDoubledResponse_plus (l x₁ x₂ : ℝ) :
    (realDoubledResponse l).mulVec (realifiedPlus x₁ x₂) =
      fun i => (1 + l) * realifiedPlus x₁ x₂ i := by
  funext i
  fin_cases i <;>
    norm_num [realDoubledResponse, realifiedChirality, realifiedPlus,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
    ring

/-- The minus realified-chiral plane has kinetic weight `1-l`. -/
theorem realDoubledResponse_minus (l x₁ x₂ : ℝ) :
    (realDoubledResponse l).mulVec (realifiedMinus x₁ x₂) =
      fun i => (1 - l) * realifiedMinus x₁ x₂ i := by
  funext i
  fin_cases i <;>
    norm_num [realDoubledResponse, realifiedChirality, realifiedMinus,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
    ring

/-- Euclidean norm squared on one real Hodge pair. -/
def hodgePairNormSq (x₁ x₂ : ℝ) : ℝ := x₁ ^ 2 + x₂ ^ 2

/-- The oriented pairing `x₁*y₂-x₂*y₁`, equivalently the contraction of one
mode with the Hodge rotation of the other. -/
def hodgePairCross (x₁ x₂ y₁ y₂ : ℝ) : ℝ := x₁ * y₂ - x₂ * y₁

/-- The real doubled quadratic kinetic form. The physical mode is `x`; `y`
is its independent dual or auxiliary partner. -/
def doubledHodgeKinetic
    (l x₁ x₂ y₁ y₂ : ℝ) : ℝ :=
  hodgePairNormSq x₁ x₂ + hodgePairNormSq y₁ y₂ +
    2 * l * hodgePairCross x₁ x₂ y₁ y₂

/-- Completing the two real squares displays the screened physical stiffness. -/
theorem doubledHodgeKinetic_completed_square
    (l x₁ x₂ y₁ y₂ : ℝ) :
    doubledHodgeKinetic l x₁ x₂ y₁ y₂ =
      (y₁ - l * x₂) ^ 2 + (y₂ + l * x₁) ^ 2 +
        screening l * hodgePairNormSq x₁ x₂ := by
  simp [doubledHodgeKinetic, hodgePairNormSq, hodgePairCross, screening]
  ring

theorem doubledHodgeKinetic_nonneg
    (l x₁ x₂ y₁ y₂ : ℝ) (hs : 0 ≤ screening l) :
    0 ≤ doubledHodgeKinetic l x₁ x₂ y₁ y₂ := by
  rw [doubledHodgeKinetic_completed_square]
  have hn : 0 ≤ hodgePairNormSq x₁ x₂ := by
    simp [hodgePairNormSq]
    positivity
  positivity

/-- Eliminating the auxiliary Hodge partner leaves coefficient `1-l^2` on
both components of the sourced mode. -/
theorem doubledHodgeKinetic_at_auxiliary_stationary
    (l x₁ x₂ : ℝ) :
    doubledHodgeKinetic l x₁ x₂ (l * x₂) (-l * x₁) =
      screening l * hodgePairNormSq x₁ x₂ := by
  rw [doubledHodgeKinetic_completed_square]
  ring

/-- If the second real mode is removed before variation, the Hodge coupling
vanishes and no screening remains. -/
theorem doubledHodgeKinetic_on_real_slice (l x₁ x₂ : ℝ) :
    doubledHodgeKinetic l x₁ x₂ 0 0 = hodgePairNormSq x₁ x₂ := by
  simp [doubledHodgeKinetic, hodgePairNormSq, hodgePairCross]

/-- Running the action backward: if a nonzero residue `l` is multiplied by an
additional coupling `g`, reproducing the same screening factor forces the
coupling magnitude to be one. -/
theorem normalizedCoupling_magnitude_forced (g l : ℝ) (hl : l ≠ 0) :
    screening (g * l) = screening l ↔ g ^ 2 = 1 := by
  unfold screening
  constructor
  · intro h
    have hl2 : 0 < l ^ 2 := sq_pos_of_ne_zero hl
    nlinarith [sq_nonneg g]
  · intro h
    nlinarith

theorem normalizedCoupling_eq_one
    (g l : ℝ) (hl : l ≠ 0) (hg : 0 ≤ g)
    (hs : screening (g * l) = screening l) :
    g = 1 := by
  have hg2 := (normalizedCoupling_magnitude_forced g l hl).mp hs
  nlinarith

/-- The deposited scalar portal coefficient as a function of the two positive
roots. -/
noncomputable def pdtPortalCoupling (r q : ℝ) : ℝ := (q / r) ^ 2

theorem pdtPortalCoupling_mem_openUnit
    (r q : ℝ) (hq : 0 < q) (hqr : q < r) :
    0 < pdtPortalCoupling r q ∧ pdtPortalCoupling r q < 1 := by
  have hr : 0 < r := lt_trans hq hqr
  have hratio0 : 0 < q / r := div_pos hq hr
  have hratio1 : q / r < 1 := (div_lt_one hr).mpr hqr
  unfold pdtPortalCoupling
  constructor <;> nlinarith

/-- Directly multiplying the quartic residual by the deposited portal
coefficient gives the wrong screening factor whenever `1<q<r`. -/
theorem pdtPortalCoupling_screening_ne
    (r q : ℝ) (hq : 1 < q) (hqr : q < r) :
    screening (pdtPortalCoupling r q * lambda4 q) ≠
      screening (lambda4 q) := by
  have hl : lambda4 q ≠ 0 := by
    have hq0 : q ≠ 0 := by linarith
    intro h
    unfold lambda4 at h
    field_simp [hq0] at h
    nlinarith
  have hk := pdtPortalCoupling_mem_openUnit r q (by linarith) hqr
  intro hs
  have hk2 :=
    (normalizedCoupling_magnitude_forced
      (pdtPortalCoupling r q) (lambda4 q) hl).mp hs
  nlinarith [sq_nonneg (pdtPortalCoupling r q)]

/-- The stationary equations with a source coupled only to the first mode.
Their solution has response `x=j/(1-l^2)`. -/
theorem doubledHodge_source_solution
    (l j₁ j₂ : ℝ) (hs : screening l ≠ 0) :
    let x₁ := j₁ / screening l
    let x₂ := j₂ / screening l
    let y₁ := l * x₂
    let y₂ := -l * x₁
    x₁ + l * y₂ = j₁ ∧
      x₂ - l * y₁ = j₂ ∧
      y₁ - l * x₂ = 0 ∧
      y₂ + l * x₁ = 0 := by
  dsimp
  constructor
  · unfold screening at hs ⊢
    field_simp [hs]
    ring
  constructor
  · unfold screening at hs ⊢
    field_simp [hs]
  · constructor <;> ring

/-- At the quartic residue, the sourced-mode response is exactly enhanced by
`Q^2/(2Q-1)`. -/
theorem quartic_doubledHodge_response (q j : ℝ) (hq : 1 < q) :
    j / screening (lambda4 q) = (q ^ 2 / (2 * q - 1)) * j := by
  have hq0 : q ≠ 0 := by linarith
  have hden : 2 * q - 1 ≠ 0 := by nlinarith
  rw [quartic_screening_identity q hq0]
  field_simp [hq0, hden]

/-- A scalar real coefficient acting on a one-dimensional complex amplitude
space. -/
noncomputable def scalarKraus (a : ℝ) (z : ℂ) : ℂ := (a : ℂ) * z

/-- A scalar Kraus branch has a state-independent relative weight. This is why
the bare scalar dilation is algebraically useful but cannot by itself transmit
information about the input state to its branch flag. -/
theorem scalarKraus_normSq (a : ℝ) (z : ℂ) :
    Complex.normSq (scalarKraus a z) =
      a ^ 2 * Complex.normSq z := by
  simp [scalarKraus, Complex.normSq_mul, Complex.normSq_ofReal, pow_two]

theorem scalarKraus_relativeWeight (a : ℝ) (z : ℂ)
    (hz : Complex.normSq z ≠ 0) :
    Complex.normSq (scalarKraus a z) / Complex.normSq z = a ^ 2 := by
  rw [scalarKraus_normSq]
  field_simp [hz]

/-- The minimal two-channel completion conserves the Born norm exactly. -/
theorem scalarKraus_completeness (l d : ℝ)
    (hdefect : d ^ 2 = screening l) (z : ℂ) :
    Complex.normSq (scalarKraus l z) +
      Complex.normSq (scalarKraus d z) = Complex.normSq z := by
  have hsum := julia_row_norm l d hdefect
  rw [scalarKraus_normSq, scalarKraus_normSq]
  calc
    l ^ 2 * Complex.normSq z + d ^ 2 * Complex.normSq z =
        (l ^ 2 + d ^ 2) * Complex.normSq z := by ring
    _ = Complex.normSq z := by rw [hsum]; ring

/-- The exact conditional Perron-horizon theorem: the quartic inverse-step
residue has amplitude `lambda4` on its positive scaling line, and any supplied
minimal complementary amplitude conserves Born norm with it. The mathematical
statement does not identify this completion with a physical causal horizon. -/
theorem quarticPerron_horizon_instrument
    (q d : ℝ) (z : ℂ) (hq : q ^ 4 = q + 1) (hq0 : q ≠ 0)
    (hdefect : d ^ 2 = screening (lambda4 q)) :
    quarticResidual.mulVec (quarticPerronVector q) =
        (fun i => lambda4 q * quarticPerronVector q i) ∧
      Complex.normSq (scalarKraus (lambda4 q) z) +
        Complex.normSq (scalarKraus d z) = Complex.normSq z := by
  exact ⟨quarticResidual_perron q hq hq0,
    scalarKraus_completeness (lambda4 q) d hdefect z⟩

/-! ## The same residue from KMS detailed balance -/

/-- The normalized causal asymmetry between a process and its thermal reverse. -/
noncomputable def detailedBalanceDefect (β ω : ℝ) : ℝ :=
  1 - Real.exp (-β * ω)

/-- If the reverse spectral weight is fixed by KMS detailed balance, subtracting
it from the forward weight and normalizing by the forward weight gives the
thermal causal-response defect. -/
theorem kms_causal_response (β ω forward reverse : ℝ) (hforward : forward ≠ 0)
    (hkms : reverse = Real.exp (-β * ω) * forward) :
    (forward - reverse) / forward = detailedBalanceDefect β ω := by
  rw [hkms]
  unfold detailedBalanceDefect
  field_simp [hforward]

/-- At the Perron inverse temperature of the quartic graph and unit gauge
frequency, the KMS causal-response defect is exactly the quartic residue. -/
theorem quartic_kms_defect (q : ℝ) (hq : 0 < q) :
    detailedBalanceDefect (Real.log q) 1 = lambda4 q := by
  unfold detailedBalanceDefect lambda4
  rw [mul_one, Real.exp_neg, Real.exp_log hq]
  simp [one_div]

/-- The residue eigen-amplitude and the unit-frequency KMS response coincide
at the quartic Perron inverse temperature. -/
theorem quarticPerron_kms_response
    (q : ℝ) (hq4 : q ^ 4 = q + 1) (hq : 0 < q) :
    quarticResidual.mulVec (quarticPerronVector q) =
        (fun i => detailedBalanceDefect (Real.log q) 1 *
          quarticPerronVector q i) := by
  rw [quartic_kms_defect q hq]
  exact quarticResidual_perron q hq4 (ne_of_gt hq)

/-- A scalar modular-frequency shift preserves the quartic KMS response if and
only if the shift vanishes. This is the exact cocycle-neutrality test for a
one-dimensional quartic spectral subspace. -/
theorem quartic_response_shift_eq_iff (q δ : ℝ) (hq : 0 < q) :
    detailedBalanceDefect 1 (Real.log q + δ) = lambda4 q ↔ δ = 0 := by
  have hbase : Real.exp (-Real.log q) = 1 / q := by
    rw [Real.exp_neg, Real.exp_log hq]
    simp [one_div]
  constructor
  · intro h
    have h' : 1 - Real.exp (-(Real.log q + δ)) = 1 - 1 / q := by
      simpa [detailedBalanceDefect, lambda4] using h
    have hexp : Real.exp (-(Real.log q + δ)) =
        Real.exp (-Real.log q) := by
      rw [hbase]
      linarith [h']
    have harg := Real.exp_injective hexp
    linarith
  · intro hδ
    subst δ
    simpa [detailedBalanceDefect] using quartic_kms_defect q hq

/-- The full reverse KMS test: the quartic response fixes the product of
inverse temperature and spectral frequency to `log q`. -/
theorem kms_response_eq_quartic_iff (q beta omega : ℝ) (hq : 0 < q) :
    detailedBalanceDefect beta omega = lambda4 q ↔
      beta * omega = Real.log q := by
  have hbase : Real.exp (-Real.log q) = 1 / q := by
    rw [Real.exp_neg, Real.exp_log hq]
    simp [one_div]
  constructor
  · intro h
    have h' : 1 - Real.exp (-beta * omega) = 1 - 1 / q := by
      simpa [detailedBalanceDefect, lambda4] using h
    have hexp : Real.exp (-beta * omega) =
        Real.exp (-Real.log q) := by
      rw [hbase]
      linarith [h']
    have harg := Real.exp_injective hexp
    linarith
  · intro hproduct
    unfold detailedBalanceDefect lambda4
    have hneg : -beta * omega = -Real.log q := by
      nlinarith
    rw [hneg, Real.exp_neg, Real.exp_log hq]
    simp [one_div]

/-- With the conventional wedge inverse temperature `2*pi`, matching the
quartic response fixes the boost frequency to `log(q)/(2*pi)`. The physical
choice of this normalization is an input; the equivalence is exact algebra. -/
theorem wedge_response_eq_quartic_iff (q omega : ℝ) (hq : 0 < q) :
    detailedBalanceDefect (2 * Real.pi) omega = lambda4 q ↔
      omega = Real.log q / (2 * Real.pi) := by
  rw [kms_response_eq_quartic_iff q (2 * Real.pi) omega hq]
  constructor <;> intro h
  · apply (eq_div_iff (mul_ne_zero (by norm_num) Real.pi_ne_zero)).2
    nlinarith
  · apply (eq_div_iff (mul_ne_zero (by norm_num) Real.pi_ne_zero)).1 at h
    nlinarith

/-! ## The continuous-core trace ray

For the continuous core of a type-III factor, the canonical trace satisfies
`tau ∘ theta_s = exp (-s) tau` under the dual action. The operator-algebraic
existence of the core, trace, and dual action is a carried theorem of
Connes--Takesaki theory. The declarations below kernel-check the exact scalar
consequences on its one-dimensional trace ray.
-/

/-- Scalar action induced on a finite trace value by the dual flow. -/
noncomputable def coreTraceScale (s mass : ℝ) : ℝ :=
  Real.exp (-s) * mass

/-- A quartic logarithmic step retains exactly the inverse Perron fraction. -/
theorem coreTraceScale_log (q mass : ℝ) (hq : 0 < q) :
    coreTraceScale (Real.log q) mass = mass / q := by
  unfold coreTraceScale
  rw [Real.exp_neg, Real.exp_log hq]
  field_simp [ne_of_gt hq]

/-- The relative trace loss of one quartic logarithmic step is `lambda4`. -/
theorem coreTraceDefect_log (q mass : ℝ) (hq : 0 < q) (hmass : mass ≠ 0) :
    (mass - coreTraceScale (Real.log q) mass) / mass = lambda4 q := by
  rw [coreTraceScale_log q mass hq]
  unfold lambda4
  field_simp [ne_of_gt hq, hmass]

/-- Two successive dual-flow steps multiply their trace-scale factors. -/
theorem coreTraceScale_add (s t mass : ℝ) :
    coreTraceScale (s + t) mass =
      coreTraceScale s (coreTraceScale t mass) := by
  unfold coreTraceScale
  rw [neg_add, Real.exp_add]
  ring

/-- On the trace ray, subtracting the quartic scale step twice and taking the
complement gives exactly the proposed gravitational survivor. Equivalently,
`I - (I-T_Q)^2 = 2*T_Q - T_Q^2` has eigenvalue `1-lambda4^2` when
`T_Q` has trace eigenvalue `1/q`. -/
theorem coreSelfDefect_survivor (q mass : ℝ)
    (hq : 0 < q) (hmass : mass ≠ 0) :
    (2 * coreTraceScale (Real.log q) mass -
        coreTraceScale (2 * Real.log q) mass) / mass =
      screening (lambda4 q) := by
  rw [coreTraceScale_log q mass hq]
  have htwo : coreTraceScale (2 * Real.log q) mass = mass / q ^ 2 := by
    unfold coreTraceScale
    have hrewrite : -(2 * Real.log q) = -Real.log q + -Real.log q := by ring
    rw [hrewrite, Real.exp_add, Real.exp_neg, Real.exp_log hq]
    field_simp [ne_of_gt hq]
  rw [htwo, quartic_screening_identity q (ne_of_gt hq)]
  field_simp [ne_of_gt hq, hmass]

/-! ## Trace normalization and entropy

The continuous-core trace is canonical only up to an overall positive scalar.
For a normalized state, rescaling the trace by `c` simultaneously rescales its
density by `1/c`.  The entropy therefore changes by the additive constant
`log c`, rather than being multiplied by `c`.  The declarations below isolate
this obstruction in a finite scalar model and record its first-law consequence.
-/

/-- The entropy contribution of one positive density value relative to a
trace whose scalar normalization is `traceWeight`. -/
noncomputable def entropyContribution
    (traceWeight density : ℝ) : ℝ :=
  -traceWeight * density * Real.log density

/-- Compensating the density when a trace is rescaled changes a normalized
entropy contribution by `density * log c`.  Summing a normalized density gives
the state-independent shift `log c`. -/
theorem entropyContribution_trace_rescale (c density : ℝ)
    (hc : c ≠ 0) (hdensity : density ≠ 0) :
    entropyContribution c (density / c) =
      entropyContribution 1 density + density * Real.log c := by
  unfold entropyContribution
  rw [Real.log_div hdensity hc]
  field_simp [hc]
  ring

/-- The additive trace-normalization ambiguity cancels from entropy
differences. -/
theorem entropyDifference_trace_rescale (S1 S2 c : ℝ) :
    (S1 + Real.log c) - (S2 + Real.log c) = S1 - S2 := by
  ring

open scoped BigOperators

/-- A finite diagonal model of the entropy first-law pairing
`delta S = Tr(delta rho K)`. -/
def firstLawVariation {n : ℕ} (k delta : Fin n → ℝ) : ℝ :=
  ∑ i, delta i * k i

/-- Adding a scalar to a modular Hamiltonian cannot change its pairing with a
normalization-preserving state perturbation. -/
theorem firstLaw_add_constant {n : ℕ} (k delta : Fin n → ℝ) (c : ℝ)
    (hdelta : ∑ i, delta i = 0) :
    firstLawVariation (fun i => k i + c) delta =
      firstLawVariation k delta := by
  unfold firstLawVariation
  calc
    (∑ i, delta i * (k i + c)) =
        (∑ i, delta i * k i) + (∑ i, delta i * c) := by
      simp only [mul_add, Finset.sum_add_distrib]
    _ = ∑ i, delta i * k i := by
      rw [← Finset.sum_mul, hdelta, zero_mul, add_zero]

/-- An affine change `K -> s K + c I` multiplies every normalized first-law
variation by `s`; the scalar part is invisible.  Thus a genuine uniform
screening of entropy variations requires a multiplicative change of the
noncentral modular generator, not an overall trace normalization. -/
theorem firstLaw_affine_scale {n : ℕ} (k delta : Fin n → ℝ) (s c : ℝ)
    (hdelta : ∑ i, delta i = 0) :
    firstLawVariation (fun i => s * k i + c) delta =
      s * firstLawVariation k delta := by
  rw [firstLaw_add_constant (fun i => s * k i) delta c hdelta]
  unfold firstLawVariation
  simp_rw [show ∀ i, delta i * (s * k i) = s * (delta i * k i) by
    intro i
    ring]
  exact (Finset.mul_sum Finset.univ (fun i => delta i * k i) s).symm

/-! ## Horizon area-density calibration

If a positive scalar `d` rescales both inverse-length resolution directions on
a two-dimensional horizon section, the number of microscopic cells per unit
physical area is multiplied by `d^2`. This is a change in physical area
calibration, not a normalization of the Type-II trace.
-/

/-- Isotropic rescaling of a two-dimensional inverse-length frame multiplies
its cell count per physical area by the square of the frame amplitude. -/
def horizonAreaDensityScale (d countedArea : ℝ) : ℝ :=
  d ^ 2 * countedArea

/-- A unitary-defect amplitude therefore gives exactly the screening factor as
the horizon area-density response. -/
theorem defect_horizonAreaDensity_scale (l d countedArea : ℝ)
    (hdefect : d ^ 2 = screening l) :
    horizonAreaDensityScale d countedArea =
      screening l * countedArea := by
  simp [horizonAreaDensityScale, hdefect]

/-- The area-density response is uniformly `s` for every counted area exactly
when the inverse-length frame amplitude has square `s`. -/
theorem horizonAreaDensityScale_all_iff (d s : ℝ) :
    (∀ countedArea : ℝ,
      horizonAreaDensityScale d countedArea = s * countedArea) ↔
        d ^ 2 = s := by
  constructor
  · intro h
    simpa [horizonAreaDensityScale] using h 1
  · intro h countedArea
    simp [horizonAreaDensityScale, h]

/-- Entropy variation for a constant microscopic density per unit area. -/
def horizonEntropyVariation (eta deltaArea : ℝ) : ℝ :=
  eta * deltaArea

/-- Rescaling the inverse-length horizon resolution by a defect amplitude is
equivalent, in Jacobson's local area law, to multiplying the entropy-per-area
coefficient by the defect weight. -/
theorem defect_areaDensityMap_eq_densityScale
    (eta l d deltaArea : ℝ)
    (hdefect : d ^ 2 = screening l) :
    horizonEntropyVariation eta
        (horizonAreaDensityScale d deltaArea) =
      horizonEntropyVariation (screening l * eta) deltaArea := by
  simp [horizonEntropyVariation, horizonAreaDensityScale, hdefect]
  ring

/-! ## Conditional Jacobson scaling consequences -/

/-- In natural units, Jacobson's area-entropy density fixes the gravitational
coupling by `G = 1/(4*eta)`. This declaration records that scalar relation. -/
noncomputable def jacobsonCoupling (eta : ℝ) : ℝ :=
  1 / (4 * eta)

/-- Reducing the horizon entropy density by a nonzero factor `s` increases
Jacobson's gravitational coupling by the inverse factor. -/
theorem jacobsonCoupling_density_scale (eta s : ℝ)
    (heta : eta ≠ 0) (hs : s ≠ 0) :
    jacobsonCoupling (s * eta) = jacobsonCoupling eta / s := by
  unfold jacobsonCoupling
  field_simp [heta, hs]

/-- If an independent physical mechanism multiplies the microscopic entropy
density by the core-survivor scalar, Jacobson's relation gives precisely the
inverse screening correction to Newton's coupling.  The trace-scaling law by
itself does not supply this premise. -/
theorem coreSurvivor_jacobsonCoupling (q eta : ℝ)
    (hq : 0 < q) (heta : eta ≠ 0)
    (hs : screening (lambda4 q) ≠ 0) :
    jacobsonCoupling (screening (lambda4 q) * eta) =
      jacobsonCoupling eta / ((2 * q - 1) / q ^ 2) := by
  rw [jacobsonCoupling_density_scale eta (screening (lambda4 q)) heta hs]
  rw [quartic_screening_identity q (ne_of_gt hq)]

/-- The squared Planck scale is the reciprocal gravitational coupling. -/
noncomputable def planckScaleSq (G : ℝ) : ℝ :=
  1 / G

/-- Under the same independent entropy-density premise, the squared Planck
scale is multiplied by the screening coefficient. -/
theorem coreSurvivor_planckScaleSq (q eta : ℝ)
    (heta : eta ≠ 0)
    (hs : screening (lambda4 q) ≠ 0) :
    planckScaleSq
        (jacobsonCoupling (screening (lambda4 q) * eta)) =
      screening (lambda4 q) *
        planckScaleSq (jacobsonCoupling eta) := by
  rw [jacobsonCoupling_density_scale eta (screening (lambda4 q)) heta hs]
  unfold planckScaleSq jacobsonCoupling
  field_simp [heta, hs]

/-- If a mass amplitude is multiplied by the defect coefficient, its square is
multiplied by the screening coefficient. -/
theorem defect_mass_square (l d m : ℝ)
    (hdefect : d ^ 2 = screening l) :
    (m * d) ^ 2 = m ^ 2 * screening l := by
  rw [mul_pow, hdefect]

/-- The gravitational and centrifugal radial exponents agree only in four
spatial dimensions. -/
theorem radial_homogeneity_iff (d : ℤ) :
    2 - d = -2 ↔ d = 4 := by
  omega

/-- The standard circular-orbit stiffness coefficient is marginal at `d=4`. -/
theorem ehrenfest_stiffness_identity (d : ℝ) :
    3 - (d - 1) = 4 - d := by
  ring

theorem ehrenfest_marginal_iff (d : ℝ) :
    4 - d = 0 ↔ d = 4 := by
  constructor <;> intro h <;> linarith

/-! ## Audit of the deposited two-scalar action

For a scalar-curvature theory with curvature coefficient `f`, scalar kinetic
matrix `k`, and fields indexed by `A,B`, the standard frame-covariant field
metric is

`G_AB = k_AB / f + (3/2) * f_A * f_B / f^2`.

The theorem below checks the algebraic consequence used in the accompanying
audit. The transformation formula itself is a physics input, not proved here.
-/

/-- The off-diagonal entry of the standard two-field frame-covariant metric. -/
noncomputable def frameMetricCross
    (kCross f fPhi fChi : ℝ) : ℝ :=
  kCross / f + (3 / 2 : ℝ) * fPhi * fChi / f ^ 2

/-- A diagonal Jordan-frame kinetic term and a curvature coefficient independent
of the second field cannot produce an off-diagonal Einstein-frame kinetic term. -/
theorem frameMetricCross_eq_zero (f fPhi : ℝ) :
    frameMetricCross 0 f fPhi 0 = 0 := by
  simp [frameMetricCross]

/-- The mixed scalar Hessian of the portal potential is proportional to the
product of the two background fields. -/
def portalMixedHessian (kappa phi chi : ℝ) : ℝ :=
  4 * kappa * phi * chi

/-- At the selected `chi = 0` axis vacuum, the portal potential supplies no
bilinear mixing between the two fluctuations. -/
theorem portalMixedHessian_at_chi_axis (kappa phi : ℝ) :
    portalMixedHessian kappa phi 0 = 0 := by
  simp [portalMixedHessian]

/-- The deposited portal potential written in fluctuations `phi = v + h` and
`chi = x` about the selected axis background `(v,0)`. -/
def shiftedPortalPotential
    (lambda3 lambda4c kappa v u h x : ℝ) : ℝ :=
  lambda3 * (((v + h) ^ 2 - v ^ 2) ^ 2) +
    lambda4c * ((x ^ 2 - u ^ 2) ^ 2) +
    kappa * (v + h) ^ 2 * x ^ 2

/-- The exact fluctuation expansion. There is no bilinear `h*x` term; the
first cross-sector interaction is the cubic term `2*kappa*v*h*x^2`. -/
theorem shiftedPortalPotential_expand
    (lambda3 lambda4c kappa v u h x : ℝ) :
    shiftedPortalPotential lambda3 lambda4c kappa v u h x =
      lambda4c * u ^ 4 +
      4 * lambda3 * v ^ 2 * h ^ 2 +
      4 * lambda3 * v * h ^ 3 +
      lambda3 * h ^ 4 +
      (kappa * v ^ 2 - 2 * lambda4c * u ^ 2) * x ^ 2 +
      2 * kappa * v * h * x ^ 2 +
      kappa * h ^ 2 * x ^ 2 +
      lambda4c * x ^ 4 := by
  unfold shiftedPortalPotential
  ring

/-- The unbroken `chi -> -chi` symmetry is exact about the axis background. -/
theorem shiftedPortalPotential_chi_even
    (lambda3 lambda4c kappa v u h x : ℝ) :
    shiftedPortalPotential lambda3 lambda4c kappa v u h (-x) =
      shiftedPortalPotential lambda3 lambda4c kappa v u h x := by
  simp [shiftedPortalPotential]

end GravityScreening

#print axioms GravityScreening.response_completed_square
#print axioms GravityScreening.normalized_even_null_quadratic_forced
#print axioms GravityScreening.response_at_stationary
#print axioms GravityScreening.normalized_block_det
#print axioms GravityScreening.channelEmbedding_det
#print axioms GravityScreening.channelEmbedding_gram
#print axioms GravityScreening.projectionResidual_normSq
#print axioms GravityScreening.normalizedIntrinsicTrace_affine
#print axioms GravityScreening.normalizedHermitianTrace_affine
#print axioms GravityScreening.intrinsicTrace_eq_screening_iff
#print axioms GravityScreening.quarticSpaceUnit_sq
#print axioms GravityScreening.quarticTimeUnit_sq
#print axioms GravityScreening.quarticTimeObserver_sq
#print axioms GravityScreening.quarticTimeUnit_eq_normalized_observer
#print axioms GravityScreening.quarticSpaceTime_orthogonal
#print axioms GravityScreening.quarticTraceResponse_sq
#print axioms GravityScreening.quarticTimeObserverResponse_sq
#print axioms GravityScreening.normalizedLorentzPair_weight
#print axioms GravityScreening.inducedPlanckSq_conformal
#print axioms GravityScreening.traceInducedPlanckSq_eq
#print axioms GravityScreening.traceInducedPlanckSq_conformal
#print axioms GravityScreening.traceInducedNewton_eq
#print axioms GravityScreening.conditional_pdt_planck_chain
#print axioms GravityScreening.conditional_pdt_quartic_planck_chain
#print axioms GravityScreening.quadraticInducedPlanckSq_forced
#print axioms GravityScreening.residueCompensatedCurvatureWeight_eq
#print axioms GravityScreening.commonWeight_cancels
#print axioms GravityScreening.curvatureOnlyWeight_survives
#print axioms GravityScreening.nonnegative_defect_unique
#print axioms GravityScreening.constitutiveBlock_det
#print axioms GravityScreening.raw_constitutive_twist_sq
#print axioms GravityScreening.raw_constitutive_conformal_symplectic
#print axioms GravityScreening.unimodularConstitutive_det
#print axioms GravityScreening.unimodular_constitutive_twist_sq
#print axioms GravityScreening.unimodularConstitutive_symplectic
#print axioms GravityScreening.constitutiveBlock_scale_shape
#print axioms GravityScreening.unimodularConstitutive_schur
#print axioms GravityScreening.scale_times_unimodular_schur
#print axioms GravityScreening.firstOrderMode_at_momentum_stationary
#print axioms GravityScreening.quarticScale_firstOrderMode_reduction
#print axioms GravityScreening.scaledUnimodular_source_solution
#print axioms GravityScreening.relativeSchur_eq_screening_iff
#print axioms GravityScreening.oneStatistic_twoParameterFisher_relativeSchur_zero
#print axioms GravityScreening.independentFisher_relativeSchur_one
#print axioms GravityScreening.screening_pos
#print axioms GravityScreening.quartic_screening_identity
#print axioms GravityScreening.lambda4_eq_relative_increment
#print axioms GravityScreening.quartic_squeeze_ratio
#print axioms GravityScreening.quarticCompanion_mul_inv
#print axioms GravityScreening.quarticCompanion_inv_mul
#print axioms GravityScreening.quarticCompanion_perron
#print axioms GravityScreening.quarticRenewalFrequency
#print axioms GravityScreening.quarticResidual_eq_one_sub_inv
#print axioms GravityScreening.quarticResidual_perron
#print axioms GravityScreening.quarticResidual_not_normal
#print axioms GravityScreening.quarticResidual_no_diagonal_symmetrizer
#print axioms GravityScreening.quarticResidual_left_perron
#print axioms GravityScreening.quarticPerron_pairing
#print axioms GravityScreening.quarticBiResidualCoefficient_eq_lambda4
#print axioms GravityScreening.quarticPerron_compensator_curvature
#print axioms GravityScreening.defect_sq_forced
#print axioms GravityScreening.defect_sqrt_sq
#print axioms GravityScreening.julia_row_norm
#print axioms GravityScreening.julia_rows_orthogonal
#print axioms GravityScreening.juliaBlock_sq
#print axioms GravityScreening.lorentzHodge_sq
#print axioms GravityScreening.chiralAreaResponse_eq
#print axioms GravityScreening.chiralAreaResponse_det
#print axioms GravityScreening.chiralAreaResponse_mul_flip
#print axioms GravityScreening.quartic_chiralAreaResponse_det
#print axioms GravityScreening.fullBivector_chiralDet
#print axioms GravityScreening.orientationEven_chiralCompliance
#print axioms GravityScreening.quartic_orientationEven_chiralCompliance
#print axioms GravityScreening.realifiedChirality_transpose
#print axioms GravityScreening.realifiedChirality_sq
#print axioms GravityScreening.realDoubledResponse_plus
#print axioms GravityScreening.realDoubledResponse_minus
#print axioms GravityScreening.doubledHodgeKinetic_completed_square
#print axioms GravityScreening.doubledHodgeKinetic_nonneg
#print axioms GravityScreening.doubledHodgeKinetic_at_auxiliary_stationary
#print axioms GravityScreening.doubledHodgeKinetic_on_real_slice
#print axioms GravityScreening.normalizedCoupling_magnitude_forced
#print axioms GravityScreening.normalizedCoupling_eq_one
#print axioms GravityScreening.pdtPortalCoupling_mem_openUnit
#print axioms GravityScreening.pdtPortalCoupling_screening_ne
#print axioms GravityScreening.doubledHodge_source_solution
#print axioms GravityScreening.quartic_doubledHodge_response
#print axioms GravityScreening.scalarKraus_normSq
#print axioms GravityScreening.scalarKraus_relativeWeight
#print axioms GravityScreening.scalarKraus_completeness
#print axioms GravityScreening.quarticPerron_horizon_instrument
#print axioms GravityScreening.kms_causal_response
#print axioms GravityScreening.quartic_kms_defect
#print axioms GravityScreening.quarticPerron_kms_response
#print axioms GravityScreening.quartic_response_shift_eq_iff
#print axioms GravityScreening.kms_response_eq_quartic_iff
#print axioms GravityScreening.wedge_response_eq_quartic_iff
#print axioms GravityScreening.coreTraceScale_log
#print axioms GravityScreening.coreTraceDefect_log
#print axioms GravityScreening.coreTraceScale_add
#print axioms GravityScreening.coreSelfDefect_survivor
#print axioms GravityScreening.entropyContribution_trace_rescale
#print axioms GravityScreening.entropyDifference_trace_rescale
#print axioms GravityScreening.firstLaw_add_constant
#print axioms GravityScreening.firstLaw_affine_scale
#print axioms GravityScreening.defect_horizonAreaDensity_scale
#print axioms GravityScreening.horizonAreaDensityScale_all_iff
#print axioms GravityScreening.defect_areaDensityMap_eq_densityScale
#print axioms GravityScreening.jacobsonCoupling_density_scale
#print axioms GravityScreening.coreSurvivor_jacobsonCoupling
#print axioms GravityScreening.coreSurvivor_planckScaleSq
#print axioms GravityScreening.defect_mass_square
#print axioms GravityScreening.radial_homogeneity_iff
#print axioms GravityScreening.ehrenfest_marginal_iff
#print axioms GravityScreening.frameMetricCross_eq_zero
#print axioms GravityScreening.portalMixedHessian_at_chi_axis
#print axioms GravityScreening.shiftedPortalPotential_expand
#print axioms GravityScreening.shiftedPortalPotential_chi_even
