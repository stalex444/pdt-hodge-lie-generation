# Proof map for the revised comparison

The single selected result begins with geometric generators, proves their
full Lie closure, and forces generator-covariant linear responses on that
algebra to be scalar. The other modules listed below retain the broader
supporting development.

| Source module | Verified role |
|---|---|
| `ResponseClosureGeometry` | Fixed metric and basis pairs; actual orthogonal-generator brackets; local Hodge complement formula, zero extension, square and local equivariance. |
| `ResponseClosureOrthogonalBasis` | Full spanning, independence and unique coordinates over every field with two nonzero, using exactly the entrywise casts of the displayed geometric generators. |
| `ResponseClosureCertificate` | Integral adjoint/Hodge identities, fourteen derived-operator recipes, all signed skew directions and one symmetric seed. |
| `GravityScreening.SignedLieGeneration` | General field proof propagating the seed to every trace-free matrix; trace-rank dimension formula without division by the matrix size. |
| `GravityScreening.HodgeLieGeneration` | Scalar extension, membership of all derived operators, equality with `sl15` and dimension 224 for every field with two nonzero. |
| `GravityScreening.HodgeResponseCovariance` | Covariance under the sixteen actual generators is equivalent to full adjoint covariance on the 224-dimensional algebra. |
| `GravityScreening.TraceFreeResponseUniqueness` | Direct matrix-unit scalar-centroid theorem, determinant exponent and one-mode calibration, with no simplicity assumption. |
| `GravityScreening.GeometricResponseRigidity` | Composes generation/covariance and scalarity; proves the calibrated `(rho Q)^224` determinant under one nonzero-mode calibration. |
| `GravityScreening.HodgeModeCalibration` | Actual nonzero Hodge witness, cubic identity and `DHE=(rho Q)H`; explicit same-mode matching calibrates the real 224-dimensional response and determinant. Supporting result, not a separate Comparator selection. |
| `GravityScreening.AdjointResponseUniqueness` | Supporting interface from Mathlib's simple-adjoint irreducibility to the usual Schur exponent theorem; the direct matrix-unit proof does not depend on it. |
| `GravityScreening.PdtOpticalRepair` | Actual affine and label derivatives, nullness and screen orthogonality, positive pullback pairing, intrinsic metric evolution, full finite-cut energy balance. |
| `GravityScreening.TwoSidedTraceFree` | Necessary and sufficient scalar-product condition for a two-sided response; explicit diagonal-difference obstruction witnesses. |

`Solution.lean` connects the one displayed Challenge statement,
`HorizonEinsteinClosure.geometricHodgeGeneration`, to its proof dependencies.
The root library also exports the optical and two-sided preservation proofs;
those results are not selected claims of the current comparison.

The older PDT modules retain the root arithmetic, KMS selection premises,
Hodge pair, doubled quadratic action, Gaussian integrals and conditional
local Einstein-tensor consequence, as well as constitutive, source-frame and
spin-two uniqueness results. The broader model already gives a definite
gravity expression relative to the electron mass. Applying these results
together still requires explicitly relating their response spaces and
physical normalizations. In particular, a local 2D divide is not automatically
the response on the full 224-dimensional algebra. The current scope is
described in `PHYSICAL_SCOPE.md` and `RESPONSE_UNIQUENESS.md`.
