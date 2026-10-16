# Uniform logarithmic Sobolev inequalities for the two-dimensional Coulomb gas in Lean

[![Palomar full preflight](https://github.com/matthewrosenzweigwork-max/LSI-2D-Diffusive-Coulomb-Gas-Lean-Public/actions/workflows/palomar-full.yml/badge.svg?branch=palomar-migration-2026-10-16)](https://github.com/matthewrosenzweigwork-max/LSI-2D-Diffusive-Coulomb-Gas-Lean-Public/actions/workflows/palomar-full.yml?query=branch%3Apalomar-migration-2026-10-16)

This repository formalizes the paper's two main theorems: full labeled Coulomb-gas LSI at fixed and compact positive temperatures, and point-weighted full-domain Gaussian Poincaré/LSI with constants uniform in the point configuration under a total-exponent bound.

This branch is a compatibility candidate for Palomar. Its new toolchain, module interfaces, and documented API repairs require fresh exact-commit verification; historical checks do not certify the migrated sources. No Palomar intake or registration has been performed.

## Statements and implementation

The compact [Challenge](Challenge.lean) fixes the physical laws, entropy, full closed form domains, hypotheses, and exact named weighted scaling. Four selected positive witness constants retain their original dependency types; their internal construction formulas are deliberately not fixed by the Challenge. This boundary is disclosed in [formalization.yaml](formalization.yaml) and the [statement design](docs/palomar/PLANAR_CHALLENGE_DESIGN.md).

[Solution](Solution.lean) imports the existing labeled and weighted implementations. [comparator.json](comparator.json) selects all 21 theorem holes and four definition holes. The historical [target inventory](verification/PUBLIC_TARGETS.json) also lists supporting declarations beyond this compact submission surface.

## Build and verification

The candidate pins Lean `v4.35.0-rc2` and canonical Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`. Install elan from its official distribution and retain the committed dependency lock. From the repository root:

```sh
python3 scripts/check_migration.py
lake exe cache get
lake build Challenge Solution
lake build IntegratedPaperRoute RetainedReload PlanBAudit
```

The first Lake build checks the candidate statement and implementation closure; the second explicitly checks all retained audit roots. The default target list is empty.

Source compilation does not substitute for Palomar's Comparator, independent kernels, and provenance checks. The [full verification workflow](.github/workflows/palomar-full.yml) pins the reusable verifier and `pipeline_commit` to `d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44`, with `mode: full` and `palomar-standard-v1`. Only its actual report for an exact commit establishes a pass. See [workflow runs](https://github.com/matthewrosenzweigwork-max/LSI-2D-Diffusive-Coulomb-Gas-Lean-Public/actions) and [migration status](docs/palomar/MIGRATION_STATUS.md).

## Frozen provenance

The accepted public baseline is `c1faa35a5258f743890515f01c858c07e4eca2ff`, copied from upstream `7ebe828bf7f69471c8120bd03a876666abd8e53f`. It pins Lean 4.34.1 and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`. The original [source manifest](verification/PUBLIC_SOURCE_MANIFEST.json) binds 1,936 source/configuration inputs. Run `python3 verification/check_sources.py` on that frozen baseline or the separate preparation branch.

On this migration branch, the original checker intentionally rejects changed inputs. [MIGRATION_LEDGER.json](docs/palomar/MIGRATION_LEDGER.json) records before/after hashes and distinguishes module-interface changes from explicit API repairs. No frozen manifest has been rewritten to imply that new bytes are the accepted old bytes.

The [historical verification summary](verification/README.md) records checks on 10 October 2026 covering 148 theorems, four definitions, and 185 export roots, including exact statement/definition correspondence, axiom checks, Lean's kernel, and strict Nanoda. The mirror omits full historical logs. Only `propext`, `Classical.choice`, and `Quot.sound` occur in the recorded selected closures. Kernel acceptance and correspondence to written mathematical arguments remain separate review questions.

## Citation and license

Use [CITATION.cff](CITATION.cff). Original repository code is licensed under [Apache-2.0](LICENSE). Existing third-party notices and dependency licenses remain in force; see [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md). The [release inventory](docs/RELEASE_PREPARATION.md) describes the separately preserved frozen snapshot.
