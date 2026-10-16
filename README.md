# Lean formalization of uniform logarithmic Sobolev inequalities for the two-dimensional Coulomb gas

This repository contains the frozen Lean source supporting the paper's two main theorems and the listed supporting results. The target inventory in verification/PUBLIC_TARGETS.json identifies the checked declarations.

## Building
The source uses Lean 4.34.1 and Mathlib commit d13f23b723b8a846827a245b89c10fc7d3f11612. Retain the supplied dependency lock.
From this repository root, obtain the pinned dependencies and their compatible cache, then run:
```sh
lake exe cache get
lake build IntegratedPaperRoute RetainedReload PlanBAudit
```
The default target list is intentionally empty; use the explicit targets above.

## Verification
The exact source was checked on 10 October 2026. The recorded checks cover 148 theorems, four frozen definitions and 185 export roots, including transitive axiom checks, exact statement and frozen-definition correspondence, Lean's default kernel and strict Nanoda. Only propext, Classical.choice and Quot.sound occur in the selected transitive axiom closures. See the source manifest and verification summary for precise identities and scope.

Kernel checking establishes the formal declarations. Correspondence to the written mathematical statements and arguments is a separate review. The repository does not imply that every sentence of the manuscript is a Lean declaration.

## Citation and notices
Use CITATION.cff for the release citation. Original source notices are preserved; no new blanket license is assigned by this snapshot.

