# Compact planar Challenge design

This candidate covers both introductory manuscript theorems: `thm:main` (fixed and compact-temperature full labeled Coulomb LSI) and `thm:weighted` (uniform point-weighted planar Gaussian Poincare and LSI). It does not register every auxiliary or sharpness theorem in the historical 2,290-line Challenge. The root `Challenge.lean` is 413 physical lines / 23,439 bytes, below the hard limits and preferred byte limit; the extra lines beyond the preferred 300 preserve both physical model/domain definitions, declaration-level mathematical docstrings, and disclosed elaborator-cache alignment commands. Its direct imports are canonical `Mathlib`, `Lean.Meta.Tactic.AuxLemma`, and `Lean.Elab.Command`; the latter two are meta imports used only for the nonlogical cache reset. Challenge-local instance registration changes restore the canonical instance paths used by the original narrow source imports. The generic Sobolev jet retains the original universe parameter name. Solution imports the existing `OriginalInputLabeledLSI` and `OriginalGaussianWeightedRoute` proof modules, independently of Challenge.

## Physical statements preserved

### Full labeled Coulomb LSI

The ordinary declaration bodies retain their existing fully qualified names and are copied from the frozen planar source:

- `CoulombConfig N` is `EuclideanSpace ℂ (Fin N)`, with its Euclidean norm.
- `coulombPairs N` selects the unordered particle pairs `i < j`; `coulombVandermonde` is their product of differences. The test functions live on the open set where this product is nonzero.
- `coulombWeight β z` is exactly `exp (-β * ‖z‖² / 2)` times the product of `‖z i - z j‖ ^ (β / N)`. The partition function is its nonnegative Lebesgue integral; the law is the inverse partition function times Lebesgue measure with this density.
- The ambient graph is the actual value/gradient Hilbert jet `Lp (WithLp 2 (ℝ × CoulombConfig N)) 2 (coulombMeasure N β)`. Its core consists of all compactly supported smooth test functions on the collision-free open set, paired with their real Euclidean gradients. `CoulombFormDomain` remains the closure of the range of this exact core map.
- Value/gradient projections and the squared gradient `Lp` norm defining `coulombFormEnergy` are copied verbatim.
- `PeriodicAttractiveLogGas.entropy` retains its extended-real shifted nonnegative Lebesgue integral definition, including possibly infinite entropy.

The fixed-temperature theorem retains `β > 0`, all `N ≥ 2`, and every element of the original full closed form domain. The uniform theorem retains a single positive rate for the whole positive compact interval `[a,b]`, fixed before `β`, `N`, and the observable. Neither endpoint takes a reference measure, moment estimate, prior LSI, or thermal-tail certificate from its caller. The source's separate higher thermal derivative-tail manuscript clause remains outside these endpoint claims.

### Uniform planar point-weighted Gaussian Poincare and LSI

`verification/PUBLIC_TARGETS.json` explicitly selects `RepulsiveCoulomb.PaperRoute.paper_weighted_named_inequalities` from `OriginalGaussianWeightedRoute`. That exact declaration is now selected in Comparator, together with the existing positivity/scaling and positive-confinement-threshold variants.

The full physical definitions remain ordinary compared declarations, not definition holes:

- `pointWeight γ a y z` is exactly `exp (-γ * ‖z‖² / 2) ∏ j, ‖z - y j‖^(a j)` on the complex plane. `pointPartition` is its extended nonnegative integral; `pointMeasure` is the actual normalized Lebesgue-density law. `pointMeasure_isProbability` is also a selected proof obligation for `γ > 0` and nonnegative exponents.
- `pointPunctures a y` consists precisely of point locations with positive exponents. `pointDomain` is their open complement. Zero exponents do not puncture the plane; coincident points are allowed.
- `PointFormDomain` is the closure of the range of the full `C_c^∞` core off those punctures in the `L²` Hilbert norm of the literal value/real-gradient jet. The actual scalar and gradient projections and squared gradient norm defining `pointFormEnergy` are copied unchanged. No abstract Sobolev space, supplied certificate, or smaller test class replaces them.
- The endpoint quantifies over every real `Q`, every positive confinement `γ`, every finite number of points `m`, every nonnegative exponent family with `∑ a j ≤ Q`, arbitrary locations, and every full-domain observable. It imposes no separation, clustering, support, or cardinality restriction. For negative `Q` the admissible class is empty, exactly as in the source.
- `paperWeightedP1 Q` and `paperWeightedK1 Q` depend only on the total-exponent bound. `paperCwt γ Q = paperWeightedP1 Q / γ` and `paperRhoWt γ Q = 2 * γ / paperWeightedK1 Q` retain their exact ordinary definition bodies. Positivity and both accepted scaling equalities are selected theorem obligations. Thus the weighted constants are fixed before point count, locations, exponent allocation, and observable, and their dependence on confinement is fixed by exact formulas.
- The selected `paper_weighted_named_full_above` additionally retains the source's common estimates with constants at any positive lower confinement threshold `γ₀`, uniformly for all `γ ≥ γ₀`.

Both main endpoint statements retain the original use of canonical `ProbabilityTheory.variance`, extended entropy of the squared full-domain value, and the exact physical Dirichlet energy.

## Deliberate Comparator holes

Comparator selects 21 theorem statements: four original labeled rate/LSI claims; four labeled-domain construction lemmas; five point-domain/normalization construction lemmas; and eight accepted weighted positivity, scaling, inequality and threshold-uniformity claims. Their Challenge proofs are `sorry`; Solution imports the existing proofs. Every Challenge `sorry` occurs in an explicitly selected declaration.

Four `definition_names` are deliberate witness holes:

1. `paperOriginalLabeledRate : {β : ℝ} → 0 < β → ℝ`;
2. `paperOriginalCompactLabeledRate : {a b : ℝ} → 0 < a → ℝ`;
3. `paperWeightedP1 : ℝ → ℝ`;
4. `paperWeightedK1 : ℝ → ℝ`.

The Challenge fixes their types, permitted parameter dependence, positivity obligations, and occurrences in the exact endpoint statements. It does **not** prescribe the internal thermal-reference/family-supremum construction of the labeled rates or the internal choice construction of the two weighted unit-confinement constants. Solution supplies the existing actual constructions. The weighted `paperCwt`/`paperRhoWt` definitions and their confinement scaling are ordinary compared definitions, not holes. This explicit boundary avoids importing entire proof constructions into the Challenge or disguising them as caller assumptions. Solution's kernel and independent replay must still validate the actual witness bodies and all proof dependencies without `sorryAx` or any new axiom.

The Comparator follows ordinary transitive dependencies of the selected statement types. No physical law, domain, energy, entropy, or variance definition is a selected definition hole. Permitted axioms are only `propext`, `Classical.choice`, and `Quot.sound`; NanoDa is enabled. Every `def` and `abbrev` has a declaration-level mathematical docstring.

## Source correspondence

Frozen public baseline: `c1faa35a5258f743890515f01c858c07e4eca2ff`. Original historical reference: `7ebe828bf7f69471c8120bd03a876666abd8e53f`.

| Surface | Existing source |
| --- | --- |
| Labeled configuration, domain, Gibbs law | `LeanResearch/RepulsiveCoulomb/LabeledCoulombModel.lean` |
| Labeled ambient jet and core | `LeanResearch/RepulsiveCoulomb/CoulombFormCore.lean` |
| Labeled closed form and energy | `LeanResearch/RepulsiveCoulomb/CoulombClosedForm.lean` |
| Euclidean Sobolev jet alias | `LeanResearch/RepulsiveCoulomb/Imported/TauCeti/Analysis/Sobolev/W1p/Basic.lean` (Tau Ceti contributors, Apache-2.0) |
| Extended entropy | `LeanResearch/PeriodicAttractiveLogGas/Entropy.lean` |
| Labeled rates and endpoints | `LeanResearch/RepulsiveCoulomb/PaperRoute/OriginalInputLabeledLSI.lean` |
| Point density, punctures, partition and law | `LeanResearch/RepulsiveCoulomb/WeightedPointModel.lean` |
| Finite punctures and open point domain | `LeanResearch/RepulsiveCoulomb/PointWeightRegularity.lean` |
| Point-law probability | `LeanResearch/RepulsiveCoulomb/WeightedPointNormalization.lean` |
| Point ambient jet and core | `LeanResearch/RepulsiveCoulomb/PointWeightFormCore.lean` |
| Point closed form and energy | `LeanResearch/RepulsiveCoulomb/PointWeightClosedForm.lean` |
| Weighted constants, positivity, scaling, endpoints | `LeanResearch/RepulsiveCoulomb/PaperRoute/OriginalGaussianWeightedRoute.lean` |

The historical Challenge aliases the labeled endpoints as claims `01_01` through `01_04`, the weighted endpoint as `02_02`, and its scaling claims as `02_03`/`02_04`. It is preserved as statement evidence in sibling `migration-reference-evidence/PlanarHistoricalChallenge.lean`. The compact surface selects original names directly. The manuscript states `thm:weighted` at lines 185–192 and the exact confinement scaling at lines 373–379 of sibling `migration-reference-evidence/planar-manuscript.tex`.

## Validation status and required checks

Static checks cover size, canonical Mathlib-only direct import, one registration for every proof/definition hole, JSON shape, Solution independent of Challenge, and source correspondence of ordinary declaration bodies and selected headers modulo comments/whitespace. No local Lean build has been performed. Earlier preflight for a narrower Challenge does not validate this extended scope: the exact new commit must undergo a fresh full Palomar preflight and all configured kernels. Equality of elaborated declarations and complete allowed import closure remain CI obligations; this document is not a verification receipt.

Build `Challenge` and `Solution` as separate root Lake libraries. Preserve frozen `main` and the original input-hash manifest. Any API repair must retain literal statement and physical-definition correspondence; a mathematical discrepancy must be reported rather than resolved by weakening the Challenge.
