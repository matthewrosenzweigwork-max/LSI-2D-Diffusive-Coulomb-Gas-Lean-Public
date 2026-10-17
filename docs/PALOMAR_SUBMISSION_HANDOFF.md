# Exact-commit Palomar submission handoff

All three full mechanical preflights passed. These are the immutable submission inputs; the release-preparation branch only preserves documentation and evidence.

| Component | Repository | Exact tested commit | Project path | Comparator configuration |
| --- | --- | --- | --- | --- |
| Periodic (per202610161) | matthewrosenzweigwork-max/DGR-Singular-LSI-Lean-Public | 587bf340cfd5fcf808d37105532d470dd3552b3b | trials/periodic/project | trials/periodic/project/comparator.json |
| Whole-space (whl202610161) | matthewrosenzweigwork-max/DGR-Singular-LSI-Lean-Public | 587bf340cfd5fcf808d37105532d470dd3552b3b | trials/whole-space/project | trials/whole-space/project/comparator.json |
| Planar (pla202610161) | matthewrosenzweigwork-max/LSI-2D-Diffusive-Coulomb-Gas-Lean-Public | 37081a3acb793917b284b93558c6b8598282dcb3 | repository root (empty) | comparator.json |

Use each package's formalization.yaml in its project directory. The complete declaration selections and report receipts are recorded in [PALOMAR_SUBMISSION_CANDIDATES.json](PALOMAR_SUBMISSION_CANDIDATES.json). Do not substitute the release-preparation head or a moving branch name for these tested commits.

## Evidence

- [Joint periodic/whole-space full preflight](https://github.com/matthewrosenzweigwork-max/DGR-Singular-LSI-Lean-Public/actions/runs/38946980451): both pass, high Challenge trust, no warnings.
- [Planar full preflight](https://github.com/matthewrosenzweigwork-max/LSI-2D-Diffusive-Coulomb-Gas-Lean-Public/actions/runs/38989785472): pass/complete, high Challenge trust, no warnings or errors; 21 theorem selections and 4 definition selections. The 300-line, 23,709-byte Challenge has no untrusted sources. Lean default kernel, nanoda and con-ron accept the solution.
- [Preserved planar receipt](../verification/palomar/FULL_PREFLIGHT_EVIDENCE.json) and [exact mechanical report](../verification/palomar/planar/mechanical-report.json). The downloaded artifact ZIP SHA-256 was independently matched to GitHub's authenticated artifact digest.
- Pinned verifier: PalomarRegistry/PalomarSubmission at d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44. Lean v4.35.0-rc2; canonical Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55; palomar-standard-v1.

## Owner's next step

Review the exact metadata and declaration selections, then separately authorize intake for these three packages. Follow the current [official intake instructions](https://submit.palomar-registry.org/llms.txt) when performing that later action. No intake, registration, temporary tag or gist has been created by this evidence-preservation step. A mechanical pass is not registry acceptance or a mathematical manuscript-correspondence audit.

The frozen release-preparation baseline and public main are unchanged in source content. The migration branch contains the tested planar source fixes; this documentation commit does not replace that tested snapshot.
