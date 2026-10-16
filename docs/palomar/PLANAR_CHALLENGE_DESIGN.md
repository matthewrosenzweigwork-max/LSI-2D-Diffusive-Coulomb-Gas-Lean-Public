# Compact planar Challenge design

This candidate selects the original full-form labeled LSI endpoints and positive rates. It does not claim to register every auxiliary or sharpness theorem appearing in the historical 2,290-line Challenge. The current root `Challenge.lean` is 184 physical lines / 9,578 bytes, below both the preferred and hard size limits. Its sole direct import is canonical `Mathlib`; it has no project-source import. The Solution's sole direct import is `LeanResearch.RepulsiveCoulomb.PaperRoute.OriginalInputLabeledLSI`, and it does not import Challenge.

## Physical statement preserved

The copied declaration bodies are from the frozen planar source and preserve their existing fully qualified names:

- `CoulombConfig N` is `EuclideanSpace ℂ (Fin N)`, with its Euclidean norm.
- `coulombPairs N` selects the unordered particle pairs `i < j`; `coulombVandermonde` is their product of differences. The test functions live on the open set where this product is nonzero.
- `coulombWeight β z` is exactly `exp (-β * ‖z‖² / 2)` times the product of `‖z i - z j‖ ^ (β / N)`. The partition function is its nonnegative Lebesgue integral, and the law is the inverse partition function times Lebesgue measure with this density.
- The ambient graph is the genuine value/gradient Hilbert jet `Lp (WithLp 2 (ℝ × CoulombConfig N)) 2 (coulombMeasure N β)`. Its core consists of all compactly supported smooth test functions on the collision-free open set, paired with their real Euclidean gradients. `CoulombFormDomain` remains the closure of the range of this exact core map. It has not been replaced by an abstract space, a restricted test-function class, or a supplied certificate.
- The value and gradient projections and the squared gradient `Lp` norm defining `coulombFormEnergy` are copied verbatim.
- `PeriodicAttractiveLogGas.entropy` retains its extended-real shifted nonnegative Lebesgue integral definition, so infinite entropy does not silently become a default real integral.

The fixed-temperature theorem retains `β > 0`, all `N ≥ 2`, and every element of the original full closed form domain. The uniform theorem retains a single positive rate for the whole positive compact interval `[a,b]`, fixed before `β`, `N`, and the observable. Neither endpoint takes a reference measure, moment estimate, prior LSI, or thermal-tail certificate from its caller. The source's separate higher thermal derivative-tail manuscript clause remains outside these endpoint claims.

## Deliberate Comparator holes

The configuration selects eight theorem statements: the original fixed-temperature and compact-temperature positivity and LSI theorems, plus four construction lemmas (`coulombVandermonde_continuous`, `coulombCoreJet_memLp`, `coulombCoreJet_add`, `coulombCoreJet_smul`). The latter are proof obligations needed by the exact open-domain/core/closed-form definitions. Their Challenge proofs are `sorry`; the Solution imports the existing accepted proof bodies. Every Challenge `sorry` occurs in one of the explicitly selected declarations.

Two `definition_names` are deliberate witness holes:

1. `paperOriginalLabeledRate : {β : ℝ} → 0 < β → ℝ`;
2. `paperOriginalCompactLabeledRate : {a b : ℝ} → 0 < a → ℝ`.

Their Challenge bodies are `sorry`. Their types, positivity obligations, and occurrences in both endpoint statements are fixed, while the Comparator permits their bodies to differ. Thus the Challenge specifies physical LSI with positive rates and the exact uniform dependence, but does **not** independently prescribe or compare the internal thermal-reference construction or literal family-supremum formula of those rates. The Solution supplies the existing source's actual thermal-reference rates. This explicit boundary avoids importing the entire thermal-construction tree into the Challenge or disguising the construction as a caller assumption. The Solution kernel and independent replay must still validate the rate bodies and all their proof dependencies without `sorryAx` or any new axiom.

All ordinary transitive dependencies of the selected statement types remain subject to the Comparator's declaration-closure comparison. None of the physical law, domain, energy, or entropy definitions is a selected definition hole. Permitted axioms are only `propext`, `Classical.choice`, and `Quot.sound`; NanoDa is enabled.

## Source correspondence

Frozen public baseline: `c1faa35a5258f743890515f01c858c07e4eca2ff`. Original historical reference: `7ebe828bf7f69471c8120bd03a876666abd8e53f`.

| Surface | Existing source |
| --- | --- |
| Configuration, pair set, Vandermonde, domain, Gibbs law | `LeanResearch/RepulsiveCoulomb/LabeledCoulombModel.lean` |
| Ambient jet and core jet | `LeanResearch/RepulsiveCoulomb/CoulombFormCore.lean` |
| Core linearity, graph closure, form value/gradient/energy | `LeanResearch/RepulsiveCoulomb/CoulombClosedForm.lean` |
| Euclidean Sobolev jet alias | `LeanResearch/RepulsiveCoulomb/Imported/TauCeti/Analysis/Sobolev/W1p/Basic.lean` (Tau Ceti contributors, Apache-2.0) |
| Extended entropy | `LeanResearch/PeriodicAttractiveLogGas/Entropy.lean` |
| Positive rates and original endpoints | `LeanResearch/RepulsiveCoulomb/PaperRoute/OriginalInputLabeledLSI.lean` |

The historical root Challenge aliases these endpoints as claims `01_01` through `01_04`; it is retained as statement evidence in the sibling `migration-reference-evidence/PlanarHistoricalChallenge.lean`. The compact surface directly selects the original declaration names rather than introducing weaker replacement theorems.

## Validation status and required checks

Static checks passed: Challenge size, canonical Mathlib-only direct import, every proof/definition hole registered exactly once, JSON shape, and Solution independent of Challenge. The source-backed statement and ordinary definition text have been checked against the existing files. No Lean build, Comparator run, external-kernel replay, or full Palomar preflight has yet validated this candidate. In particular, equality of elaborated declarations, module visibility, Mathlib API migration, and admissible complete import closure remain CI obligations; this design document is not a verification receipt.

Build `Challenge` and `Solution` as separate root Lake libraries. First run the authorized Linux migration build, then the exact-commit full Palomar reusable workflow with this `comparator.json`. Preserve both frozen `main` and its original input-hash manifest. Any needed API repair must retain the literal statement/physical definition correspondence; a mathematical discrepancy must be reported rather than resolved by weakening the Challenge.

Every `def` and `abbrev` in the compact Challenge now has a declaration-level mathematical docstring, including the two rate witness holes and their exact permitted dependence. A comment-stripped comparison confirmed that this documentation pass changed no declaration, statement, or body.
