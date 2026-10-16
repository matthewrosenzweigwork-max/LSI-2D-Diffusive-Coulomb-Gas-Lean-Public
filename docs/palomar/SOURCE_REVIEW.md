# Bounded source review

This record describes a bounded source review by a separate Codex agent with fresh context on 16 October 2026. The reviewer reconstructed the selected mathematical statements before reading their formal statements, then compared them against the accepted sources. It is an automated source review, not external human review, a full manuscript proof-argument audit, or a kernel/Comparator pass. Mechanical results must be read from the exact-commit workflow report.

The reviewer did not edit source files or run builds. For the compatibility batches, it inspected diffs before reading writer repair notes. It found no added logical assumptions, axioms, or proof holes and no change to mathematical definitions, hypotheses, or theorem signatures. Exact new-Mathlib elaboration remains the responsibility of hosted verification.

## Statement scope

The reference is accepted public commit `c1faa35a5258f743890515f01c858c07e4eca2ff` and the revised manuscript's `thm:main` and `thm:weighted`. The final compact statement surface at `2987599ed28fa225a3de6fde2ce9a722e5feae4c` was reviewed in two stages; the second extended the first to the weighted theorem.

The reviewer found no discrepancy in all 63 declaration surfaces: 38 fixed definitions/abbreviations, 21 theorem signatures, and four witness types. All 25 holes are selected exactly in `comparator.json`.

- Labeled law: original Coulomb law, full smooth-core closed domain, physical energy and entropy, and fixed/compact-positive-temperature uniform LSI with positive rates.
- Weighted law: literal normalized `exp(-gamma*|z|²/2)` times the finite product of point distances to nonnegative exponents; only a total-exponent bound, with unrestricted point count, coincidences, and locations. The domain is the full graph closure of smooth compactly supported functions off exactly the positive-exponent punctures.
- Weighted conclusions: full-domain Poincaré and entropy LSI; exact named `Cwt=P1(Q)/gamma` and `RhoWt=2*gamma/K1(Q)` scaling and the confinement-lower-bound statements.

The four witness holes retain their dependency types. The Solution retains the original choice/thermal-reference constructions, but their literal internal formulas are outside the Challenge contract. No caller certificate or extra separation, regularity, or rate assumption was introduced.

The weighted Solution import adds no local source files to the previous endpoint closure: its 1,282-file closure was already a subset of the previous 1,848-file closure. No Challenge import or stripped-source proof-hole/axiom token was found in that inspected closure.

## Compatibility scope

The initial source review covered the `TwoConnected.lean` public-API adaptation and found no statement or mathematical-definition change. Later graph-library repairs are outside that initial review and require their own review and fresh machine verification. This record does not automatically certify future commits.

## Incremental graph repair review

The same separate reviewer inspected the three graph proof changes at `a145ceeca2efb6146934f420b204c205ab27af66` against `2987599ed28fa225a3de6fde2ce9a722e5feae4c`, before reading repair notes. In `Graph/Tree.lean`, `Graph/Relabel.lean`, and `InitialPair.lean`, explicit public vertex-set identities expose the same membership propositions before construction, simplification, or case analysis. All declaration signatures, hypotheses, maps, and mathematical content were retained; no new axiom or proof hole was found. This is source-plausibility review, with no build/elaboration assertion.

## Further planar interface review

A separate review against `a145ceeca2efb6146934f420b204c205ab27af66` covered four modules: `CoulombCenterRelativeForm`, `PointGeodesicBigonExtraction`, `GeodesicTriangleBridgeInterval`, and `DbarBranchCoreCompatibility`. The two helper theorem visibility changes preserve their mathematical statements and complete proofs. Explicit ordered-subtype arguments and equality transport preserve the same endpoint claims. The public `HasWeakFDerivOn.hasWeakLineDerivOn` eliminator has exactly the directional weak-derivative conclusion previously accessed through the predicate body. No mathematical definitions, hypotheses, axioms, or proof holes were added or changed. This was read-only source/API review; elaboration remains subject to hosted verification.

## Phase helper and holomorphic weak-kernel review

A separate reviewer inspected the two-file source diff against `64f871f3f772b6d6afd12082b3a2694b2af4c8e2` before reading writer notes. `conePhase_neg_mul_self` changes only private/public visibility; its exact statement and complete proof are preserved. The four directional calls in `coulombHolomorphic_weak_dbar_pairing` use the imported public `HasWeakFDerivOn.hasWeakLineDerivOn` lemma, whose conclusion is precisely the same directional weak derivative as the original internal function application. Both integration-by-parts identities and both derivative-local-integrability consumers retain their original evidence and conclusions. No mathematical definition, declaration signature (apart from intended helper visibility), assumption, axiom, or proof hole changed. Reviewed SHA256 values: `TranslatedSupportingHalfplane.lean` = `d8b612bf95524df5bbbac7c2d710974948c81aac01ac1feaea534240d036126c`; `DbarBranchHolomorphicWeakKernel.lean` = `44a9ce21a8a7db3b570e38f9fa04d89c157197df171bcd4179848b5a7d3d7bea`. Hosted elaboration remains required.

## Module-aware retained audit review

A separate reviewer compared the `IntegratedPaperRoute` repair against `506828c9101402756100488ef40bf1b918e0078e` before reading repair notes. All 94 name arrays, 92 fatal guards, original 60 public imports, allowed citation cut, required/forbidden route checks and `sorry` checks are retained. Seventeen local nonexporting environment snapshots expose imported project proof data for the same custom graph walks. Seventeen axiom classifiers now use Lean's standard `collectAxioms`, preserving exactly `propext`, `Classical.choice` and `Quot.sound`; no placeholder is added to the allowlist. Pinned rc2 source shows that this collector uses saved imported axiom metadata rather than mistaking exported body placeholders for genuine axioms.

The audit-only helper imports exactly the prior 1,929-module project closure. At that review stage it was absent from Solution's dependencies; the final wrapper described below explicitly includes the retained audit chain. Root review caught an unsupported `public import all` modifier combination before push; the helper now uses supported plain `import all`. Independent review checked the corrected syntax and transitive private-import semantics against exact rc2 source. A tiny three-module rc3 fixture was run successfully, including a root rerun: the endpoint and its original private helper proof bodies were accessible through both private import layers, with empty collected axioms. This is a targeted syntax/visibility test, not an rc2 project build. No mathematical proof or statement changed. Hosted compilation remains required.

The source-build workflow also retains a read-only JSONL comparison of both compact environments. The script reads the configured theorem and definition-hole selections, uses the same comparison boundaries as Lake, and reports all Challenge-owned declarations. Its diagnostics are not a Comparator or independent-kernel pass.


## Bounded review of the planar correspondence repair

After the `d2ee2fc` hosted diagnostic, a separate agent streamed every selected
theorem type difference and accounted for all ten by canonical complex-instance
paths and generated auxiliary-proof names. Root separately accounted for all
20 differing fixed-root type fields and 28 differing fixed-root value fields
using only the same paths, the canonical real finite-dimensional construction,
and auxiliary-proof-name correspondence. The generic Sobolev jet had only a
universe-parameter spelling difference. This identifies elaboration causes;
it does not establish actual Comparator acceptance.

A separate read-only diff review then checked the next administrative repair
against `d2ee2fc`: removing only the two canonical meta imports and reset lines
recovered all twelve original source files byte for byte. The same held for
Challenge after additionally undoing its intended canonical-instance erasures
and explicit source universe spelling. All 25 configured holes, original
docstrings, and audit guards were retained. No new mathematical axiom,
hypothesis, Solution hole, fixed-formula change, or proof-body edit was found.
The retained audit root itself is unchanged by this cache repair. Its helper
keeps exactly the same 1,929 imports, with documentation moved after them.

The review is bounded automated source review. It is not external human review
or a full manuscript proof-argument audit. The fresh hosted rc2 source/audit
build and full exact-commit preflight remain required; actual selected witness
heights will be inspected before any height override is applied.

## Final wrapper and downstream audit review

A separate read-only review against `c87ca63aa31701c0deb9d087b408e5244ed362ec` found no material issue in the downstream audit batch. `RetainedReload` retains its exact original 1,929-name literal array, with only the known audit helper appended separately; both fatal census guards remain. `PlanBAudit` retains all four literal arrays, all seven fatal guards, the original three-axiom allowlist and the exact `visitFixed` traversal, including its theorem-hole body cuts. Its private environment snapshot and standard `Lean.collectAxioms` inspection follow the pinned compiler's module metadata semantics. No mathematical declaration or proof text changed.

The final Solution retains both original endpoint imports and adds `public import PlanBAudit`. The local dependency graph has 1,934 modules: four wrapper/audit roots and 1,930 LeanResearch modules, including the explicit adapter. It has no cycle and no Challenge import. `IntegratedPaperRoute` itself remains byte-identical to the reviewed parent, retaining all 94 arrays and 92 fatal guards. The exact candidate must compile this complete audit chain in full preflight. This source review is not a kernel, Comparator, or independent replay result. Later Challenge metadata changes require their own review.

## Observed weighted-height and compact-format review

A separate read-only review against `c87ca63` confirmed that the compact draft preserves all 250 original nonblank code lines, all 63 declaration surfaces, all 25 selected holes and all 42 docstring targets. Its only additional code at that stage was the two immediately placed weighted-witness height overrides. The canonical rc2 implementation was independently inspected: the API changes only the nonpersistent height-lookup extension, without rewriting any existing `ConstantInfo`, body, type or kernel option. The values 55 were subsequently preserved in the authenticated c87 hosted diagnostic artifact. The later local instance section and audit resource adjustment require their own bounded review and fresh exact-candidate compilation.

## Final local registration review

The separate reviewer then inspected the complete final 300-line / 23,709-byte Challenge (SHA256 `9aeace75383beb5146f2bebc0424a4e0b390e807563c56f0ff062dafd7480651`). Every original code line, all 63 mathematical declaration surfaces, all fixed formulas/hypotheses, all 25 selected holes and all 42 declaration docstring attachments remain. The only new code relative to the whitespace-compacted parent consists of the two observed-height commands and the four-line local instance section. The section affects only `coulombPartition` and `coulombMeasure` and ends before the jet declarations. It registers existing canonical instance proofs and adds no mathematical declaration or axiom.

The reviewer independently read the saved c87 diagnostic: all 21 configured theorem types match, the two weighted source witness heights are 55, and the other four mismatches are precisely the generated finite-dimensional and T0 proof paths targeted by the local section. The tiny scope fixture tests the administrative mechanism, not actual Mathlib elaboration. The review found no material issue; post-edit full verification remains required.

## Final audit resource review

A separate read-only diff check confirmed that removing only the seventeen scoped finite-budget commands and reverting the one prior unlimited setting recovers the parent integrated audit file byte for byte. All 94 literal arrays, 92 fatal guards, citation/body cuts and the original recursion-depth setting remain unchanged. The retained and Plan B diffs consist exactly of their previously reviewed visibility/census/collector repairs plus one scoped budget each. At that stage, all nineteen audit commands received finite 2,000,000-heartbeat budgets. No mathematical proof text, statement or logical check changed. Completion of these commands is a fresh full-preflight obligation.

## Retained private-census diagnosis

A separate investigator reproduced the failed final candidate's exact public-only module count and the two missing private-only module names. A three-module Lean-only fixture established that retaining the public root import and separately adding `import all` restores the full private header census. It recommended the one-line visibility addition, retaining expected count 1,930, every literal module name, and both census guards. This diagnosis does not turn the failed candidate's report into a pass; the corrected immutable candidate requires a new full report.

A fresh separate diff review verified the applied change: removing only `import all IntegratedPaperRoute` recovers `RetainedReload` at `5d88919` byte for byte. All 1,929 unique literal names, the single helper append, expected count 1,930, both fatal guards, budgets and example checks remain unchanged. No other source, audit or mathematical file changed in this batch; the migration ledger records the new reload hash. No blocking issue was found.


## Retained literal annotation and finite headroom

An independent read-only review of the authenticated `8116dfc` report located the sole observed failure at elaboration of the retained module-name array. It recommended the explicit `Array Lean.Name` annotation as stating the type already imposed downstream. Four separate Lean-only smoke runs used the exact 1,929-name literal plus the known helper append and confirmed both forms return 1,930 names. Reverse-order timings did not establish a consistent annotation speedup, and the tiny fixture did not reproduce the full-environment timeout. The smoke is bounded compatibility evidence on local rc3, not a pinned rc2 project pass.

The applied source diff adds only that type annotation and raises only this audit command's finite heartbeat budget to 10,000,000. The original literal bytes, helper append, exact count comparison and per-module membership rejection are unchanged. No mathematical statement, proof, declaration, permitted axiom or audit guard changes; all other audit budgets remain fixed. The next exact-commit full preflight remains decisive.
