# Local Hodge generation of sl(15) and scalar response rigidity

This development proves that fifteen explicitly defined orthogonal adjoint
actions, together with one local Lorentz Hodge operation, generate every
trace-free endomorphism of their fifteen-dimensional coordinate space.
The proof works over every field in which two is nonzero. The generated
algebra therefore has dimension 224.

The fixed six-dimensional form is `diag(1,1,1,-1,1,-1)`. The Hodge operation
uses the oriented four-plane `0123` and is zero on the remaining nine
bivectors. The adjoint operators are computed from actual six-by-six
orthogonal-generator commutators. The generated algebra is defined as the
least subspace containing these operators and closed under commutators.
The full trace-free space is the conclusion of the generation theorem.

The same principal theorem now proves response rigidity. A linear response
on this 224-dimensional algebra that commutes with the commutator action of
each of the sixteen generators must be `c I`, with determinant `c^224`.
The proof uses matrix units directly and works in every characteristic
except two, including characteristics three and five where `sl15` is not
simple. Supporting theorems show that one nonzero-mode calibration fixes c,
and provide the actual Hodge generator as a canonical witness: matching the
same response on that mode to its divide/flip product fixes `c=rho Q`.
The physical matching and covariance are explicit premises. See
[RESPONSE_UNIQUENESS.md](RESPONSE_UNIQUENESS.md).

The mathematical proof and its relation to known representation theory are
in [LIE_GENERATION.md](LIE_GENERATION.md). Its proposed contribution is an
explicit integral generation mechanism, a reusable matrix-unit propagation
lemma, and a uniform field statement. The literature search has not
established global novelty or priority, and no human peer review is claimed.

## The selected theorem

The Palomar comparison selects exactly one declaration:
`HorizonEinsteinClosure.geometricHodgeGeneration`.
It proves the geometrically specified Lie closure equals `sl(15,K)`, derives
dimension 224, and then forces every linear response covariant under those
same generators to be scalar with determinant `c^224`. Generation extends
covariance to the whole algebra, connecting the clauses of this single theorem.

The optical calculations and the two-sided trace-preservation criterion
remain in the substantive supporting modules. They are outside the selected
claim of this note. [PROOF_MAP.md](PROOF_MAP.md) records their source locations.

## Relation to PDT gravity

Stephanie Alexander's PDT proposal motivates the displayed operator choice.
The theorem determines their least Lie closure and the form of a response
under the stated covariance hypotheses. Physical selection of this closure
and the value of the scalar require the corresponding physical premises.

The supporting Hodge-mode calibration fixes `c = rho Q` when the same response
matches its divide/flip product on the actual nonzero Hodge mode. Its precise
hypotheses and the distinction between the local Hodge pair and the full
response space are stated in [RESPONSE_UNIQUENESS.md](RESPONSE_UNIQUENESS.md).

The broader PDT gravity expression, existing uniqueness results and optical
interpretation are documented in [PHYSICAL_SCOPE.md](PHYSICAL_SCOPE.md).
[NEWTON_EXPRESSION.md](NEWTON_EXPRESSION.md) evaluates that expression against
CODATA. Those physical applications are outside the selected mathematical
claim of this note.

## Reproduction and provenance

```sh
lake build
python3 scripts/check_render_statements.py
```

Lean 4.31.0 and the Mathlib revision in `lake-manifest.json` are pinned.
`Challenge.lean` imports only Mathlib and has complete ordinary definitions;
`Solution.lean` proves the one selected statement from the source modules.
The theorem statement definitions are fixed dependencies, and
`comparator.json` has an empty `definition_names` list. The complete
statement is repeated exactly in its theorem documentation so the partial
reviewer view exposes the quantified claim. See
[RENDER_COMPATIBILITY.md](RENDER_COMPATIBILITY.md).

The finite identities use kernel-checked matrix-unit arithmetic. The proofs
use only `propext`, `Classical.choice`, and `Quot.sound`; no native computation
axiom is required. AI agents assisted with theorem design, exact exploratory
calculations, Lean proofs, literature checks and integration under Stephanie
Alexander's direction. Source relationships and limitations are recorded in
[formalization.yaml](formalization.yaml) and [PROOF_MAP.md](PROOF_MAP.md).

New public commits require their own Palomar verification and editorial
review. Local proof checking does not establish acceptance or experimental
validation.
