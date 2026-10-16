# Lean formalization of uniform logarithmic Sobolev inequalities for the two-dimensional Coulomb gas

This repository contains the frozen Lean source supporting the paper's two main theorems and the listed supporting results. The [target inventory](verification/PUBLIC_TARGETS.json) identifies the checked declarations.

## Building
The source uses Lean 4.34.1 and Mathlib commit `d13f23b723b8a846827a245b89c10fc7d3f11612`. Retain the supplied dependency lock.
From this repository root, obtain the pinned dependencies and their compatible cache, then run:
```sh
lake exe cache get
lake build IntegratedPaperRoute RetainedReload PlanBAudit
```
The default target list is intentionally empty; use the explicit targets above.

## Verification
The exact source was checked on 10 October 2026. The recorded checks cover 148 theorems, four frozen definitions and 185 export roots, including transitive axiom checks, exact statement and frozen-definition correspondence, Lean's default kernel and strict Nanoda. Only propext, Classical.choice and Quot.sound occur in the selected transitive axiom closures. See the [source manifest](verification/PUBLIC_SOURCE_MANIFEST.json) and [verification summary](verification/README.md) for precise identities and scope. These records describe the historical verification campaign; this public mirror does not contain its full machine-checking logs, and publication is not a new kernel replay.

Kernel checking establishes the formal declarations. Correspondence to the written mathematical statements and arguments is a separate review. The repository does not imply that every sentence of the manuscript is a Lean declaration.

## Citation and notices
Use [CITATION.cff](CITATION.cff) for the release citation. Original source notices are preserved. No root license file is present and no new blanket license is assigned by this snapshot. A repository license decision is still needed before a Palomar submission.

## Frozen source and release preparation

The frozen public source baseline is commit `c1faa35a5258f743890515f01c858c07e4eca2ff`. Check all 1,936 frozen source/configuration inputs from the repository root:

```sh
python3 verification/check_sources.py
```

The manifest includes the current build adapter `lakefile.toml`, the dependency lock, and the toolchain. Preserve these bytes along with the proof sources.

See the [release inventory and staged submission plan](docs/RELEASE_PREPARATION.md). Its metadata draft is incomplete and is not a submission. Current registry compatibility requires a separate migration of Lean, Mathlib, and module interfaces; historical kernel checks do not establish compatibility with the current Palomar verifier.

