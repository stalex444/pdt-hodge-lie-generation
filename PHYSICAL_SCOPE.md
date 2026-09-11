# Physical response: established structure and remaining implications

## What the generation theorem establishes

The fixed orthogonal adjoint actions and local Hodge operation generate
`sl(15)`. Consequently their least commutator-closed linear response space
has dimension 224. The generators, chosen four-plane and closure requirement
are explicit premises when this result is applied to a physical response.
For an arbitrary physical response algebra, inclusion of these generators
and closure under commutators imply containment of `sl15`. Equality and
dimension 224 additionally require the minimal generated algebra, or a
trace-free upper bound. The larger algebra `gl15` also contains the generators
and is closed under commutators. The added response theorem proves that a
linear response on this trace-free space is scalar if it commutes with the
adjoint actions of the same sixteen generators. The scalar form is therefore
a conclusion under covariance. Its value, a state, an entropy density and
a gravitational coupling are not selected by that theorem.

One nonzero-mode calibration `R(X0)=(rho Q)X0` then fixes the entire
224-dimensional response and its determinant to `(rho Q)^224`. This is now
a supporting Lean theorem. It connects the scalar form to an explicit
calibration; it does not silently infer physical covariance or that
calibration from generator inclusion. See
[RESPONSE_UNIQUENESS.md](RESPONSE_UNIQUENESS.md).

## An exact condition for extending the divide

The existing `HodgeBulkScreen.lean` uses a complex two-dimensional Hodge pair.
Its two chiral projectors give a divide/flip product `(rho Q) I` on that pair.
The separate `scalarResponseMatrix` definition in `UnifiedCouplingGrammar.lean`
assumes a scalar matrix on an arbitrary response space; the structural
exponent file specializes its dimension to 224. These are different spaces
and the earlier proofs do not transport one operator into the other.

The new theorem `two_sided_preserves_trace_zero_iff` supplies a precise test.
For matrices over any commutative ring with a finite nonempty index set,

```text
(for every trace-free T, D T E is trace free)
    iff (there exists r such that E D = r I).
```

The proof uses trace cyclicity, off-diagonal matrix units and diagonal
differences. A verified witness shows that unequal diagonal entries of `ED`
produce a nonzero output trace from a trace-free diagonal difference.

For the local Hodge generator, `H^2=-P`, with `P` the rank-six local
projector. Thus

```text
(a I+b H)(a I-b H) = a^2 I+b^2 P.
```

For real nonzero `b`, the two-sided map with these factors fails the new
trace-preservation test. The six local directions and nine complementary
directions carry unequal product weights.

The original complex chirality is `C=-iH`. Under zero extension, `C^2=P`.
With `a=(rho+Q)/2`, `b=(rho-Q)/2`, the divide and flip instead give

```text
(a I+b C)(a I-b C) = (rho Q) P+a^2 (I-P).
```

This also fails the trace-preservation test for real unequal `rho,Q`.
A complex involution can be assigned on the complement to repair the
algebraic product, but its choice and physical meaning would be additional
input. Over the reals there is no full fifteen-dimensional complex structure:
`J^2=-I` would imply `(det J)^2=-1`.

There is a more economical local calibration route. The actual Hodge matrix
also satisfies `PH=HP=H`, so the same factors obey

```text
D H E = (a^2-b^2) H = (rho Q) H.
```

Here H itself is a canonical nonzero trace-free element of the response
algebra. Thus it suffices to match the same physical response on this one
element, `R(H)=DHE`; the generator-covariance theorem then fixes the entire
response and its determinant. This calculation needs no chirality choice
on the complement. It does not assert that `R(T)=DTE` for every T, which
would fail the trace-preservation test. The factors already contain rho and
Q, and the physical same-response matching remains explicit. The identity
therefore reduces the transport requirement, rather than independently
selecting the calibration scale.

This route is proved in `HodgeModeCalibration.lean`. In particular,
`real_geometric_hodge_calibrated_determinant` keeps R real-linear on
`sl(15,R)` and takes its determinant over the reals, in dimension 224.
Only the one-mode comparison is complexified entrywise to use the chiral
factors; injectivity of that scalar inclusion recovers the real calibration.
No identification of complex dimension 224 with real dimension 224 is used.

There is a broader sufficient construction. For invertible factors with
`DE=rI`, the two-sided map is `T ↦ r D T D^-1`. Over characteristic zero,
conjugation has determinant one on `sl15`, so this map has determinant
`r^224` without being a scalar map itself. This determinant argument is
ordinary mathematical reasoning in this note; the supporting Lean theorem
checks the trace-preservation criterion. An application must identify the
physical factors and match their product to the PDT calibration `r=rho Q`
on this response space.

## Covariance and positive physical modes

Hodge covariance is an additional condition with concrete content. Write
`q_biv=diag(eta_a eta_b)` in the displayed bivector basis and set
`tau(T)=q_biv T^transpose q_biv`. This nonscalar involution preserves `sl15`
and commutes with the commutator action of every original orthogonal adjoint
generator. Those generators are q_biv-skew; H is q_biv-self-adjoint. On
`T=E00-E99`, the Hodge covariance defect is
`tau([H,T])-[H,tau(T)]=-4(E09+E90)`. Thus the orthogonal covariance conditions
alone do not imply the Hodge condition. Even `R=2I+tau` is positive and
self-adjoint for the ordinary real Frobenius pairing, with eigenvalues one
and three, while remaining nonscalar and satisfying the original fifteen
covariance conditions. These are elementary matrix consequences, not
additional selected Lean theorems.

A distinct issue arises if these transformations are interpreted as exact
symmetries of a positive quadratic action on all 224 directions. No positive
definite real bilinear form B on `sl(15,R)` can be invariant under all sixteen
adjoint actions. Invariance propagates through their Lie closure. Taking
`D=E00-E11` and `X=E01` gives `[D,X]=2X`, and hence
`0=B([D,X],X)+B(X,[D,X])=4 B(X,X)`, a contradiction. This ordinary algebraic
obstruction does not contradict scalar-response covariance. It requires
that an application distinguish an intertwining law for R from invariance
of a physical action or state. An indefinite covariant field description,
or a separate constrained physical space, is not excluded by this argument.
In particular, the positive TT Gaussian cannot be promoted to 224 positive
invariant modes solely by the generated dimension.

## Existing action and Gaussian results

The broader PDT proposal already gives a gravity formula with one dimensional
anchor, the electron mass. With `S_Q=(2Q-1)/Q^2`, it reads

```text
alpha_G = G m_e^2/(hbar c) = pi^4 / [S_Q (rho Q)^224].
```

Its exponent is obtained from the proposed algebraic rules; neither 224 nor
112 needs measured `G` as an input. The corresponding area quantum, in
`hbar=c=1` units, is `4 pi^4/[S_Q m_e^2 (rho Q)^224]`. The mass exponent
112 is half the squared-mass exponent 224. These are definite consequences
within the stated PDT coupling grammar. A separate microscopic entropy
calculation would test or explain the physical identification further; its
absence from the selected theorems does not make the existing formula a
fit to measured `G`. See the
[deposited Newton manuscript](https://doi.org/10.5281/zenodo.20417378) and its
[reproducible coupling calculation](https://github.com/stalex444/dimensional-origin-Newton/blob/6277d1b94eda7b19588a0a207baf204f43d00f75/gravity_correction.py).

There is also substantial existing uniqueness work. Exchange symmetry, a
unit mean stiffness and the Q-clock eigenweight force the constitutive
matrix. Positivity, the Gram form and preservation of the electric source
ray fix its canonical frame. Gauge identities and self-adjointness fix the
parity-even two-derivative spin-two operator up to its overall coefficient.
The passive rotationally covariant TT response is fixed by its quadratic
weight, and matching the same normalized physical metric is equivalent to
`G_Q=G_0/S_Q` under the stated metric normalization. These are conditional
uniqueness theorems, not merely evaluations of selected matrices. See the
[existing uniqueness ladder](https://github.com/stalex444/gravity-screening-mechanism/blob/4ad8be8c95f3170d77e4675294df79a5d53a976b/UNIQUENESS_LADDER.md)
and [TT response theorem](https://github.com/stalex444/gravity-screening-mechanism/blob/4ad8be8c95f3170d77e4675294df79a5d53a976b/GravityScreening/TTResponseUniqueness.lean).

The generation theorem and these uniqueness statements answer different
questions. To combine them, their state spaces, response operators and
normalizations must be related explicitly. An adopted physical
identification is a legitimate model premise; the mathematical consequences
must then be proved on those same objects. The limitations below concern
that composition and the scope of the selected statements, rather than an
assertion that the broader theory has no ruler, scale or uniqueness work.

The supporting source already contains a doubled quadratic action, exact
first variations, completed-square positivity, partner elimination for an
arbitrary linear operator, and time-dependent TT mode kinetic forms.
`DoubledTTGaussian.lean` relates the action to the Frobenius pairing of the
two TT polarizations and evaluates a real four-dimensional Gaussian. For
the defined quartic response it gives `pi^2/screening`; multiplying by the
defined projective boundary volume gives `pi^4/screening`.

These are concrete variational and integration results. They do not yet
calculate the curvature term of a metric-dependent quantum effective action.
The final displayed coupling identity still divides by the independently
defined `(rho Q)^224` bulk factor. A fixed-mode Gaussian normalization is not
automatically an absolute physical entropy coefficient or Newton coupling.

## An additional microscopic calculation

The Adler–Zee framework relates an induced Newton coefficient to a regulated
stress-trace correlation function. Casini, Mazzitelli and Testé identify a
direct connection between that correlator term and the area term in
entanglement entropy, while keeping improvement, contact and modular boundary
terms explicit. [Area terms in entanglement entropy](https://arxiv.org/abs/1412.6522).
Donoghue and Menezes carry out an induced-coupling calculation for a
specified QCD-like model using correlation data, perturbation theory and
lattice input. [Inducing the Einstein action in QCD-like theories](https://arxiv.org/abs/1712.04468).

Applying this route to the present action would require a metric-dependent
completion, its physical stress tensor, the full covariant mode spectrum or
stress correlations, and a regulator and renormalization prescription.
Curvature couplings matter: flat-space data alone need not determine them.
The integer 224 counts algebra directions; identifying these with physical
field species or independent horizon states needs a further representation
and constraint analysis. Heat-kernel formulas explicitly depend on such
field content, curvature couplings and ultraviolet scales.
[Newton constant, contact terms and entropy](https://arxiv.org/abs/1502.03758).

Once a physical area-entropy density `eta` is established, Jacobson's
equilibrium argument relates it to `G=1/(4 hbar eta)` in the stated natural
units. It does not determine the microscopic density itself.
[Thermodynamics of Spacetime](https://arxiv.org/abs/gr-qc/9504004).

These sources identify a possible additional derivation from microscopic
dynamics. They do not prove the specific PDT coupling formula and do not
make that particular derivation a prerequisite for stating PDT with its
physical foundations. This bounded search does not establish that a
dynamical completion is impossible.

## Optical repair and energy interpretation

The repaired coordinate family is

```text
X(u,y) = (u, [y dot S y+u |S y|^2]/2, (I+uS)y).
```

For symmetric `S`, its verified label derivatives are orthogonal to the
verified null tangent. Nonsingularity of `I+uS` gives a positive induced
screen pairing. The Perron specialization preserves the earlier transverse
map and satisfies the actual induced-metric evolution `q'=2qB`.

The general finite-cut charge and density are

```text
C(u)=A(u)-u A(u) theta(u),
C'(u)=u A(u)[sigma^2(u)+Ric(k,k)(u)-theta(u)^2/2].
```

For the nonsingular trace-free affine two-screen model, the evolving
shear-minus-expansion density is constant after multiplication by area:
`A(sigma^2-theta^2/2)=2 ell^2`. Its boost integral from zero to `L` is
`ell^2 L^2`, with endpoint expansion retained. The shear-only integral is
different; its logarithmic value is not part of the selected Lean statement.

The nonlinear density and boundary charge match the conventions of
[Faulkner and Speranza, equations 3.27 and 3.31](https://arxiv.org/html/2405.00847v2#S3.SS2).
Their future area/modular relation requires additional gravitational
constraints and future stationarity. The repaired flat family supplies
neither a global event horizon nor a quantum state with that modular
Hamiltonian. Optical shear in flat spacetime is not evidence of gravitational
radiation. The local Clausius premise remains independent of these
coordinate and real-analysis results.
