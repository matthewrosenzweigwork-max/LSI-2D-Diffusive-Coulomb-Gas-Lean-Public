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
