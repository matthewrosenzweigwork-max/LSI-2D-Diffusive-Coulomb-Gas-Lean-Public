# Planar compatibility repairs

## `Graph.deleteVerts_singleton_eq_self`

Current Linux migration CI identified the first failing declaration in `LeanResearch/RepulsiveCoulomb/Imported/Schoenflies/Graph/TwoConnected.lean`, line 126: `rw [deleteVerts, ...]` rejected `deleteVerts` as a rewrite argument of graph type.

The pinned Mathlib revision `065356127b1dc0016f66b7283ce0ce2c4055aa55`, in `Mathlib/Combinatorics/Graph/Delete.lean`, declares `deleteVerts` in a `public section` without `@[expose]`. It is therefore inappropriate to make the downstream proof depend on unfolding that definition across the new module interface. An `unfold` or definitional `change` would retain that dependency.

The repair keeps the exact theorem statement and every definition unchanged. It uses the public order and deletion API instead: deletion is a subgraph (`deleteVerts_le`); the reverse inclusion preserves vertices because the deleted singleton is absent (`vertexSet_deleteVerts`); every old edge survives because both endpoints are vertices of the original graph and consequently differ from the absent vertex (`deleteVerts_isLink`). This replaces the single unfolding rewrite by an explicit proof of the same elementary graph equality. No mathematical hypothesis, axiom, model, or conclusion changes.

This repair has been inspected against the pinned Mathlib public API but has not been compiled locally. The next Linux CI run must validate elaboration and downstream imports. No broad API edits were made in anticipation of unobserved errors.

## Preliminary API scan

The pinned `Mathlib/MeasureTheory/SpecificCodomains/WithLp.lean` still provides `MemLp.of_fst_of_snd_prodLp` as the backward implication of `memLp_prodLp_iff`. It takes the conjunction of component `MemLp` statements. The inspected planar uses supply that conjunction (`constructor`, `⟨...,...⟩`, or equivalent refinement); no mismatch was established. Relevant sites include `CoulombFormCore.lean:36`, `PointAmbientCore.lean:47`, `CoulombCenterRelativeForm.lean:38`, and imported `TauCeti/Analysis/Sobolev/W1p/Basic.lean:245,436`.

Real-valued factor comparisons in the current tree use `Finset.prod_le_prod₀` with a nonnegativity premise. `PartitionMomentBranchHolder.lean:64` retains the deprecated alias `Finset.prod_le_prod'`, but its codomain is `ℝ≥0∞`, where the generic order-monotone product lemma remains applicable; the pinned source still defines that alias. This is a likely warning rather than a demonstrated failure. No proof was changed for it.

These are static observations, not a declaration that the whole upgraded proof tree is compatible. Compiler-reported first causes should continue to drive minimal repairs.

## Full-preflight `d2013fa`: opaque vertex membership

The full-preflight report for exact commit `d2013fadf65d9c9bca34729a2aec87167111a705` failed during Solution compilation. The saved report is `migration-reference-evidence/planar-report-d2013fa.json`; its diagnostics identify three failed source targets. The earlier `TwoConnected` repair had already passed sufficiently for these downstream modules to be checked.

Three narrowly targeted repairs replace implicit reduction of the opaque `Graph.deleteVerts` vertex set with its public equation `Graph.vertexSet_deleteVerts`:

- `Graph/Tree.lean`, `Graph.IsWalk.deleteVerts`: rewrite the surviving source-vertex membership goal before constructing its old-membership/non-deletion pair.
- `Graph/Relabel.lean`, `Graph.IsWalk.relabelEdges_deleteVerts`, nil branch: normalize both the hypothesis and goal with `vertexSet_deleteVerts` and `vertexSet_relabelEdges`; the original proof rewrote only the goal and then supplied a still-opaque hypothesis.
- `InitialPair.lean`, `Schoenflies.deleteVert_connected_initSkel`: rewrite the hub vertex membership before constructing it, and rewrite an arbitrary surviving-vertex membership hypothesis before destructuring it as the conjunction it represents.

All theorem statements and definitions remain unchanged. These edits insert public-API rewrites into existing proof steps and neither add proof holes nor alter the graph-theoretic argument. No local build was run. The next source-build CI must validate them before another full preflight.

The report's abbreviated diagnostics additionally contain five `ring` tactic failures without file locations, goals, or contexts. Their full source diagnostics are outside its retained 20,000-character build tail. The three identified modules contain only one explicit `ring` invocation (`InitialPair.lean`, `openSegment_chord_supNorm_lt`), so there is insufficient evidence to attribute all five messages or modify an arithmetic argument safely. No speculative arithmetic changes were made; full source-build logs must establish any remaining first cause.

## Hosted source build `a145cee`: exposure and subtype equality

Hosted source run `38931900543` at commit `a145cee` confirmed that the prior three graph repairs compile. Its next reported failures identify the following four modules (two line errors concern separate helpers in the first module):

- `CoulombCenterRelativeForm.lean`: the exposed public definition `coulombCenterRelativeCoreJetLinear` referred to two private same-module additivity/homogeneity helper theorems. Those two helpers are now public theorem declarations under the existing exposed public section. Their mathematical statements and proof bodies are unchanged; the public linear-map definition and all physical definitions are unchanged. This is visibility repair rather than replacement of the form or core.
- `PointGeodesicBigonExtraction.lean`, `exists_interval_of_curve_disagreement`: explicit `a`/`b` arguments to `lt_of_le_of_ne` force comparisons in the interval subtype. The disequality branches now receive equalities of subtype points, allowing direct substitution of endpoint membership/equality into the contradiction. Previously elaboration inferred underlying real-number comparisons, and the simplification could not transport the curve endpoint equality. No extremum, continuity, endpoint, or disagreement condition changes.
- `GeodesicTriangleBridgeInterval.lean`, `exists_curve_bridge_interval`: the same explicit subtype arguments keep the hypothesized equality in the interval domain, so its existing substitution correctly transports membership in the second closed set. The disjointness contradiction and bridge statement are unchanged.
- `DbarBranchCoreCompatibility.lean`, `coulombComplexCore_lineDeriv_pairing`: use the existing public eliminator `TauCeti.HasWeakFDerivOn.hasWeakLineDerivOn` to obtain the directional weak derivative, rather than applying the sealed `HasWeakFDerivOn` proposition as a function. The original integration-by-parts identity is unchanged.

These repairs add no assumptions, axioms, proof holes, or altered mathematical-definition bodies. No local build was run; the next hosted source build remains required. The source visibility change alters the two helpers' exported names from their former private generated names, but preserves their statements and proofs.

## Hosted source build `64f871f`: phase-helper and directional API failures

Hosted source run `38936516048` at commit `64f871f` reported only `TranslatedSupportingHalfplane` and `DbarBranchHolomorphicWeakKernel` as failed targets. The preceding exposure/subtype/weak-core repairs had compiled.

- `TranslatedSupportingHalfplane.lean`: remove only `private` from `conePhase_neg_mul_self`. Its statement and complete proof body are unchanged. The existing exposed public definition `translatedSupportingRigid` can now use this elementary phase-inverse equality when constructing its inverse isometry. The isometry definition, physical geometry, and all theorem statements are unchanged. A repository-wide exact-name search found only this declaration and two same-module references: the inverse construction and `translatedSupportingRigid_sheared`; there are no additional downstream references to repair.
- `DbarBranchHolomorphicWeakKernel.lean`, `coulombHolomorphic_weak_dbar_pairing`: replace all four direct applications of the sealed weak-Frechet-derivative proposition (`hw vx` / `hw vy`) by the existing public projection `hw.hasWeakLineDerivOn vx` / `hw.hasWeakLineDerivOn vy`. Both integration-by-parts identities and both directional local-integrability arguments now use the public API. The original holomorphic zero-derivative identity and integral algebra remain unchanged.

The API rationale is exact: imported `TauCeti/Analysis/Sobolev/WeakDeriv/Basic.lean` defines `HasWeakFDerivOn` as the proposition that all directional weak derivatives exist, and exposes `HasWeakFDerivOn.hasWeakLineDerivOn` with precisely that directional conclusion. Its definition is sealed to downstream modules, so direct function application is invalid there; using its proved eliminator changes no mathematical content.

A repository-wide static audit of references to `HasWeakFDerivOn`, its constructors, and aliases found no remaining direct sealed-predicate application outside the defining module. `DbarBranchCoreCompatibility`, the point metric-map route, and the thermal radial route use `hasWeakLineDerivOn`; local-graph and extension consumers use the public congruence/monotonicity API. `W1p/Basic.lean` applies a hypothesis as a function only after explicitly rewriting it through the public `hasWeakFDerivOn_iff`, which is valid. Applications inside `WeakDeriv/Basic.lean` are internal to its own definition module and remain valid. Other occurrences are statement surfaces or public constructors.

No assumptions, axioms, proof holes, definition bodies, or theorem statements changed. No local build or commit was performed; the next hosted source build remains the validation step.

## Hosted source build `6398553`: module-aware integrated axiom and route audit

Hosted source run `38942437216` compiled the project proof modules but failed the custom checks in `IntegratedPaperRoute`. Its ordinary `#print axioms` output showed only `propext`, `Classical.choice`, and `Quot.sound`; the custom graph walk then called canonical `Nat.gcd` or generated `lipschitzSmoothingBump._proof_3` an unexpected axiom.

The cause is the new module interface representation. `Environment.find?` sees the imported interface, where a sealed declaration can have an axiom-shaped placeholder rather than its mathematical body. The old audit classified `.axiomInfo` directly and therefore confused an interface representation with an actual axiom dependency. This is not evidence that the proof acquired a new mathematical axiom.

The exact pinned Lean source at `11acb17ec6b07a8f9e9173e6845197929540936b` supplies the correct API in `src/Lean/Util/CollectAxioms.lean`: `Lean.collectAxioms` consults persistent imported axiom-dependency metadata, uses a nonexporting environment, and reads checked kernel declarations. `#print axioms` itself uses this collector. The audit now calls that same collector for every declaration visited by each existing audit; all 17 three-axiom allowlist checks remain fatal and unchanged in their permitted names. Diagnostics also identify the declaration whose dependency was rejected. No canonical name, generated helper, `sorryAx`, or other exception was added to an allowlist.

Axiom checking and project proof-route checking remain separate obligations. Merely using `setExporting false` cannot recover bodies that were never imported. The new audit-only aggregator `LeanResearch/PalomarAuditPrivateImports.lean` requests `import all` private data for precisely the 1,929 already-reachable project modules. The root privately imports that aggregator with `import all`, retaining all 60 original public imports unchanged. The helper is inside the existing `LeanResearch` Lake library; no build-configuration change is needed. Its import graph is the original project dependency DAG with the same existing module nodes, plus this audit-only aggregator. Mathematical consumers and Solution do not import the helper. This does not introduce a new project dependency or alter any mathematical module; it makes the same proof bodies available to the existing custom route walks. All 17 environment snapshots explicitly select nonexporting visibility. The canonical-library frontier uses the collector's proper metadata for actual axiom checking, rather than falsely classifying its hidden bodies.

Every original audit root, required-producer check, forbidden-producer check, type traversal, `sorryAx` rejection, and the explicit authored-route citation-body boundary is retained. Those guards were not removed or bypassed. Both files remain below the 10,000-line source limit (3,475 root lines; 1,941 helper lines). No mathematical statement, definition, or proof body changed; only audit imports and metaprogram diagnostics/inspection changed.

Source evidence: [pinned Lean axiom collector](https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/Lean/Util/CollectAxioms.lean), [pinned Lean module environment](https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/Lean/Environment.lean). This repair has not been built locally. A successful hosted build is required to confirm the preserved provenance guards and the module-aware checks; the compiler error alone does not authorize declaring any axiom safe.

### Audit helper import syntax correction and minimal executable fixture

The pinned rc2 parser (`src/Lean/Parser/Module.lean`, lines 100–105) explicitly rejects combining `public` with `import all`. The initial helper draft used that invalid combination; it was caught and corrected before push. Its 1,929 header directives are now plain `import all`, with the root also using plain `import all LeanResearch.PalomarAuditPrivateImports`. No duplicated public import directives are necessary in this audit-only helper. The original 60 public root imports remain unchanged.

The exact pinned module loader's private-import rule propagates private bodies through an `import all` chain: if `A` is loaded at private-all level and `A import all B`, then `B` is loaded at private-all level as well. A three-module Lean-only fixture confirmed the behavior with the installed Lean v4.35.0-rc3: `A` defined a public endpoint proved by a private helper; `B` used plain `import all A`; `C` used plain `import all B`. In `C`, a nonexporting `Environment.find?` returned actual theorem bodies for both the endpoint and its original private helper, and `collectAxioms` returned the empty array. All three fixture compilations exited zero in about three seconds. Fixture source/output lives at `/tmp/planar-private-import-fixture-_ja63m2h`.

This is an executable rc3 syntax/import-transitivity smoke plus exact rc2 parser/loader source inspection, not an rc2 project build. The rc2 hosted project build remains required. Source: [pinned rc2 parser restriction](https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/Lean/Parser/Module.lean#L100-L105). No project mathematical source, axiom allowlist, or build/cache configuration changed during this correction.

### Audit helper module-documentation ordering correction

Hosted source run `38947998056` compiled the mathematical source and Solution, then rejected the audit helper's first import because its preceding `/-! ... -/` module documentation had already ended Lean's import header. The helper documentation now follows all 1,929 plain `import all` directives. The import names, their order, and every other non-comment token remain unchanged; the file remains 1,941 lines. `IntegratedPaperRoute` has no analogous issue: before its final import it uses only ordinary whitespace and a line comment, with its first actual command after all imports.

The revised Lean-only `B`/`C` fixture compiled successfully with the installed rc3 compiler, preserving transitive access to both original theorem bodies and returning no axioms. In addition, a Lean-only parser check read the **exact saved project files** as text, without importing/building the project, and called `Lean.Parser.parseHeader`: it parsed all 1,929 helper imports and all 61 integrated-root imports with no errors. This verifies the complete header layouts rather than a shortened approximation. The check source is `/tmp/planar-private-import-fixture-_ja63m2h/HeaderCheck.lean`; it is an rc3 parser smoke, not an rc2 project build.

No mathematical file, build/cache setting, audit allowlist, or traversal guard changed. No project build, commit, or push was performed during this correction.

### Strict compact correspondence: elaborator cache metadata

The twelve source files containing the 63 compact declarations receive only
canonical meta imports and auxiliary-lemma cache resets before those existing
declarations. Removing those added lines recovers their previous bytes exactly;
no original mathematical statement, definition or proof body is edited.
[PLANAR_COMPARATOR_REPAIRS.md](PLANAR_COMPARATOR_REPAIRS.md) records the raw
instance/cache/universe findings, scope and required fresh verification. The
accepted frozen baseline and original source manifest remain unchanged.

## Downstream audit adapters: exact import census and fixed-definition inspection

Static inspection identified two downstream audit adaptations needed after introducing the private-body adapter. `RetainedReload` retains its original literal 1,929-name expected project-module array byte-for-byte, then explicitly appends the single known new name `LeanResearch.PalomarAuditPrivateImports` in a separate `expected.push` expression. Its exact-count comparison and per-module membership rejection are unchanged. No blanket namespace exclusion, broad adapter exception, or inferred count replaces them.

`PlanBAudit` retains `public import RetainedReload` and separately adds plain `import all IntegratedPaperRoute`. This gives its private metaprogram access to the original integrated root declarations and the transitive private-body adapter while preserving its existing public reexport. Both audit adapters use an explicit nonexporting environment snapshot. The existing fixed-closure walk, including its type traversal and theorem-hole body cuts, is unchanged. All literal theorem-hole, four-definition, and witness arrays remain unchanged, as do the declaration-kind checks, missing-constant rejection, `sorryAx` rejection, and required fixed-definition membership guards.

Only the fixed-closure axiom classifier changes from raw `.axiomInfo` inspection to official `Lean.collectAxioms` for each visited constant, rejecting every returned axiom outside the original `propext` / `Classical.choice` / `Quot.sound` list. This avoids treating sealed interface placeholders as new axioms. The public collector checks actual proof dependencies, including those recorded in imported module metadata; it does not allow a new mathematical axiom. The adapter's fixed dependency traversal still has exactly its original cuts, while axiom safety is checked independently with Lean's collector.

These are static bookkeeping/module-visibility repairs. No mathematical source, model, bound, theorem, or proof changed; the original mathematical source remains unchanged by this audit batch. The final Solution wrapper imports PlanBAudit after its two original endpoint imports, requiring IntegratedPaperRoute, RetainedReload, and PlanBAudit to compile in the exact full-preflight candidate. This wiring does not itself establish a full pass.

## Audit elaboration resource budget

The c87 hosted audit build produced exactly fourteen deterministic heartbeat-limit diagnostics in `IntegratedPaperRoute`, all at the compiler's 200,000-heartbeat default while elaborating large audit metaprograms. The mathematical source and Challenge/Solution build had already passed. No additional type, axiom, producer, forbidden-route, or kernel diagnostic was reported, although timed-out commands had not completed their checks.

All seventeen integrated `run_cmd` audit blocks, plus the retained census and Plan B audit block, now receive a finite scoped 2,000,000-heartbeat elaboration budget. The pre-existing unlimited setting in the point-admissibility namespace is replaced with the same finite budget. The original recursion-depth setting remains unchanged. This allocates compiler work; it does not disable an audit, alter a root/name array, change traversal cuts or the three-axiom allowlist, or modify mathematical declarations. The hosted workflow's wall-clock bound remains in force. The tenfold budget is headroom, not an assertion that compilation has passed; the exact final full preflight must execute every retained guard.

## Retained reload: explicitly load the private import census

Full candidate `5d88919aa48a754a609d0a385363aa57b0276aa4`, workflow `38963104233`, compiled the integrated audit root with its finite budgets but stopped in `RetainedReload`: its public-only import view contained 1,928 project modules, while the strict expected census requires 1,930. Comparator was not reached. The failed raw report is preserved privately; it is not a passing receipt.

Independent static import-graph reconstruction gives exactly 1,928 public-reachable modules versus 1,930 with the private closure. The two private-only names are `LeanResearch.PalomarAuditPrivateImports` and the original `LeanResearch.RepulsiveCoulomb.Imported.TauCeti.Analysis.Distribution.TestFunction.Translation`. A tiny three-module Lean fixture reproduced this module-header behavior and confirmed that a separate `import all` restores the private module names even when the original public import is retained. Merely changing the environment's exporting flag does not import missing module data.

`RetainedReload` therefore retains `public import IntegratedPaperRoute` and adds plain `import all IntegratedPaperRoute`. Its original 1,929-name literal array, explicit single-helper append, exact expected count 1,930, namespace filter and per-module membership rejection are unchanged. No count is lowered and no exception is added. This is a module-visibility correction, with no mathematical declaration, proof, axiom allowance or audit guard changed. A fresh exact-commit full preflight remains required.
