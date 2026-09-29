# Response rigidity on the generated algebra

Let K be any field with `2 != 0`. Let `g=sl(15,K)`, and let the sixteen
matrices be the fifteen geometrically defined orthogonal adjoint generators
and the local Lorentz Hodge extension used in the generation theorem.
Suppose `R:g->g` is K-linear and, for each of those matrices s,

```text
R([s,X]) = [s,R(X)]    for every X in g.
```

Then `R=c I` for a scalar c and `det R=c^224`. The principal selected
`geometricHodgeGeneration` statement now includes this implication along
with the generated-algebra equality and its dimension. It is an implication
from explicitly stated covariance, not a definition of R as a scalar matrix.

The field restriction is exactly the same as for generation. The proof
does not assume that `sl15` is simple or its adjoint representation is
irreducible. In characteristics three and five the identity matrix is a
nonzero central trace-free element, so those assumptions would be false.
The direct proof still applies.

## Proof

For a fixed response R, the elements s for which `R ad_s = ad_s R` form
a Lie subalgebra: this follows from linearity and
`[ad_s,ad_t]=ad_[s,t]`. The existing generation theorem therefore extends
covariance under the sixteen matrices to covariance under every element of g.

For any distinct i,j and any matrix X, direct multiplication gives

```text
[Eij,[Eij,X]] = -2 Xji Eij.
```

Commuting R through this identity, with `X=Eji`, forces `R(Eij)=c Eij`
for a scalar c. The c-eigenspace of R is invariant under all adjoint
actions. Starting with this one matrix unit, brackets generate its reverse,
all other off-diagonal matrix units, and every diagonal difference.
Those matrices span all of g. Consequently the eigenspace is g and `R=c I`.
Taking its determinant gives `c^dim(g)=c^224`.

The reusable matrix-unit argument is proved for any finite matrix index
type containing two distinct indices. It does not divide by the matrix
size, take an algebraic closure, or extract an eigenvalue of an arbitrary
operator. This is why the field scope survives the non-simple cases.

## Calibration and physical scope

If any nonzero `X0` satisfies `R(X0)=w X0`, then the scalar above must be w.
The supporting theorem
`geometric_response_calibrated_determinant` therefore proves

```text
R(X0)=(rho Q)X0, X0 != 0
    => R=(rho Q)I and det R=(rho Q)^224,
```

under the same generator-covariance conditions. The two factors rho and Q
are arbitrary supplied scalars in this theorem. Their arithmetic selection
and physical interpretation belong to the PDT foundations.

There is now a distinguished calibration witness. The actual nonzero Hodge
generator H has `H^3=-H`. With the complex local chiral factors
`D=aI+b(-iH)` and `E=aI-b(-iH)`, where
`a=(rho+Q)/2` and `b=(rho-Q)/2`, the supporting proof gives
`DHE=(rho Q)H`. Its real-response wrapper assumes that the entrywise
complexification of the same `R(H)` agrees with this product, then concludes
`R=(rho Q)I` and the real determinant `(rho Q)^224`. This requires matching
one canonical mode, without extending `T->DTE` to all trace-free T.
The agreement is still an explicit physical identification; the factors
already encode the supplied arithmetic weights.

R acts on the **224-dimensional algebra**, while s is a **15-by-15 matrix**
whose commutator acts on that algebra. These roles differ. A nonzero scalar acting
on the natural 15-dimensional space induces the identity by conjugation;
that operation does not supply the required scalar calibration on g.
Also, R is a linear response, not a bracket-preserving Lie homomorphism:
a general scalar multiple of the identity does not preserve the bracket.

The covariance assumption applies to every X for each generator. Merely
knowing R's values at the sixteen generators would be a weaker condition.
Likewise, inclusion of a Hodge operation in the response algebra does not
by itself make the physical response invariant under that operation.
These are application premises that must be identified when using the
result in an action or entropy calculation.

## Sources and verification

For a general reference on the scalar-centroid ingredient, see Georgia Benkart
and Erhard Neher, [*The centroid of extended affine and root graded Lie
algebras* (2005), Proposition 3.1(b), p. 15](https://arxiv.org/pdf/math/0502561#page=15).
With `L=sl(15,K)`, a one-dimensional off-diagonal weight space generates `L`
as an ideal, so their criterion yields a scalar centroid. This application
also covers characteristics three and five: their characteristic-zero
restriction starts in section 3.2. This provides context for the standard
rigidity step after covariance extends to the full algebra. The paper does
not present the fixed local-Hodge generation calculation.

- `GravityScreening/HodgeResponseCovariance.lean` proves propagation from
  the actual geometric generators to full adjoint covariance.
- `GravityScreening/TraceFreeResponseUniqueness.lean` proves the direct
  scalar-centroid theorem, the determinant and one-mode calibration.
- `GravityScreening/GeometricResponseRigidity.lean` composes those results.
- `GravityScreening/HodgeModeCalibration.lean` proves the actual Hodge-mode
  identity and its calibration consequence for both complex and real responses.
- `GravityScreening/AdjointResponseUniqueness.lean` separately supplies the
  ordinary simple-adjoint/Schur interface; the direct theorem does not
  depend on it.

The original component verification used Lean 4.31. The September 29
compatibility port compiles with Lean 4.35.0-rc2 and matching Mathlib; the
selected generation-and-rigidity theorem still uses only `propext`,
`Classical.choice` and `Quot.sound`. The earlier direct response and covariance
proofs also received an independent AI source review and recompilation.
These checks establish the displayed mathematical implications. The
standard centroid/Schur principle is not claimed as a newly discovered
mathematical fact; its explicit connection to the generated algebra
strengthens this development. They do not establish empirical validity
or guarantee editorial acceptance.
