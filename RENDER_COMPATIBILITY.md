# Complete statements in the reviewer view

The comparison uses the presentation developed for
[PalomarSubmission issue134](https://github.com/PalomarRegistry/PalomarSubmission/issues/134).
For every selected result, Challenge and Solution define an ordinary
`<theoremName>Statement : Prop` containing the complete quantified claim.
The theorem proves that proposition. These are fixed definitions, never
Comparator definition holes: `definition_names` remains empty.

Palomar's partial declaration view shows a theorem and its immediately
preceding documentation. Each documentation block therefore repeats the
complete proposition definition verbatim. The script
`scripts/check_render_statements.py` checks agreement between the displayed
copy, compiled definition and corresponding Challenge/Solution definition.
The geometric/operator definitions are ordinary checked dependencies.

The current comparison selects one generation-and-rigidity theorem. Its
quantified proposition and proof are preserved from commit 919c3e5; the optical
and two-sided companion selections have been removed. Their substantive
proof modules remain in the supporting library. Earlier verification receipts
apply to their original commits. The narrowed intake requires fresh build,
statement, axiom and rendering checks, followed by Palomar's own mechanical
and editorial review.

```sh
lake build
python3 scripts/check_render_statements.py
```
