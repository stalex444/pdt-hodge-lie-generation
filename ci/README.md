# Verification workflow template

The source is checked with `lake build` and `python3 scripts/check_render_statements.py`.
Palomar independently performs mechanical verification when a commit is submitted.

`lean-workflow.yml.example` preserves the previous GitHub Actions build configuration.
It is an inactive template. Publishing it as `.github/workflows/lean.yml` requires a
GitHub authorization that can create workflows; the current publisher credential
has repository write access without that scope. No GitHub Actions CI result is
claimed for this repository until that workflow is enabled and run.
