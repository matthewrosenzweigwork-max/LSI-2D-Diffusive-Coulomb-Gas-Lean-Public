# Public release preparation

Update, 17 October 2026: all three migrated packages now have passing full exact-commit Palomar preflights. See [the submission handoff](PALOMAR_SUBMISSION_HANDOFF.md) and [candidate ledger](PALOMAR_SUBMISSION_CANDIDATES.json). The historical inventory and staged plan below describe the frozen source branch, not the current migration verification status. No intake or registration has occurred.

Status on 16 October 2026: this `release-preparation-2026-10-16` branch contains documentation, metadata, licensing, and byte-integrity automation. Its accepted source inputs and toolchain pins are unchanged. The owner-approved Apache-2.0 license is present; existing third-party notices are retained.

The [hosted frozen-source integrity check](https://github.com/matthewrosenzweigwork-max/LSI-2D-Diffusive-Coulomb-Gas-Lean-Public/actions/runs/38929864796) passed for all 1,936 manifest inputs. The inventory and staged plan below describe this frozen branch. Compatibility migration, complete statement metadata, and fresh verification are tracked separately on [`palomar-migration-2026-10-16`](https://github.com/matthewrosenzweigwork-max/LSI-2D-Diffusive-Coulomb-Gas-Lean-Public/tree/palomar-migration-2026-10-16). Neither branch changes public `main`, and no Palomar intake or registration has been performed.

## Snapshot and build

The accepted public baseline is `c1faa35a5258f743890515f01c858c07e4eca2ff`. The existing `verification/PUBLIC_SOURCE_MANIFEST.json` binds 1,936 inputs copied from upstream `7ebe828bf7f69471c8120bd03a876666abd8e53f`. It includes the three audit-build roots, current `lakefile.toml` adapter, `lake-manifest.json`, and `lean-toolchain`. `FROZEN_LAKEFILE.toml` is retained separately; it is not the active Lakefile.

The project pins `leanprover/lean4:v4.34.1` and canonical Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`. Reading that Mathlib revision's `lean-toolchain` confirmed an exact match. From the repository root:

```sh
python3 verification/check_sources.py
lake exe cache get
lake build IntegratedPaperRoute RetainedReload PlanBAudit
```

The Python check was run successfully during this preparation. The Lake commands are the configured explicit build commands and were not run here. A bare `lake build` has an empty default target list. The target inventory contains 148 theorems and four definitions. The verification summary records 185 export roots and historical default-kernel/strict-Nanoda and Comparator checks; the underlying full machine-checking logs are not included in this public mirror.

## Concrete inventory

[RELEASE_INVENTORY.json](RELEASE_INVENTORY.json) records the accepted commit's static scan. Reproduce it with:

```sh
python3 scripts/release_inventory.py c1faa35a5258f743890515f01c858c07e4eca2ff
```

- 1,945 regular tracked files, totaling 15,545,145 bytes; 1,932 Lean files.
- 18 files have a leading module header; 1,914 need migration. There are no Lean Lakefiles requiring an exemption.
- No file exceeds 10,000 physical lines. The largest is `LeanResearch/RepulsiveCoulomb/Imported/ScalarCoarea/ScalarCoarea.lean` at 3,620 lines; `IntegratedPaperRoute.lean` has 3,467 lines. No submodule gitlinks, symlinks, Git LFS pointers, or listed compiled artifacts were found in the submitted tree.
- The committed manifest uses public HTTPS GitHub Git URLs and full lowercase 40-character commit revisions. These syntactic checks do not authenticate dependency bytes.
- There is exactly one active root Lakefile and a committed manifest, but no completed `formalization.yaml`, Challenge/Solution pair, Comparator configuration, or current full Palomar workflow report.
- Lean 4.34.1 is below the currently declared Palomar minimum, v4.35.0-rc2. A new toolchain also requires a matching new Mathlib pin and source migration.

These are lexical/source inventory checks, not a Lean parser run or certification of registry compliance. Dependencies fetched in a future build were not scanned.

## Statement-surface work

The public target inventory is a useful selection index, but it is not a small standalone Challenge. The integrated roots import project-specific definitions and cannot be reused unchanged as a permitted Challenge. Select the main paper claims and their precise definitions, reconstruct their statement surface using approved dependencies, and retain all actual hypotheses. No claim is made that the current definitions already fit the Challenge limits.

All retained and imported source files remain part of the repository-wide module check. Their reachability and historical acceptance are reasons to preserve them, not to discard frozen sources to bypass registry rules. Historical exact-definition and statement comparisons do not establish those properties for a migrated Challenge/Solution pair.

## Decisions and evidence still needed

- The owner authorized Apache-2.0 for both repositories and confirmed authority on behalf of the authors. The root license and draft SPDX metadata now agree. Existing third-party notices remain intact.
- Confirm the human author and responsible-maintainer lists, precise paper/source titles and identifiers, source relationships, historical automation roles, and completed review status. Existing citations establish attribution, not a new endorsement of a submission.
- Select the principal declarations to register and document all their actual hypotheses and limitations. Supporting targets do not automatically become advertised principal results. A fresh statement/argument correspondence audit remains distinct from a kernel check.
- Recover or link the exact historical machine-readable receipts and logs from the original verification campaigns if they will be cited as release evidence. The public summaries alone do not reproduce those runs.

[formalization.yaml.draft](formalization.yaml.draft) supplies a conservative abstract and proposed classification. Empty provenance and automation fields are deliberate unresolved decisions. Do not copy it to the project root as submission-ready metadata. No Comparator configuration is supplied: its theorem list cannot be finalized before the statement surface is designed.

## Staged route to Palomar

1. Review and commit the documentation changes separately from the accepted source snapshot. Keep the accepted commit and manifests available as the reproducible historical baseline.
2. Create a separate submission-migration branch. Choose an accepted Lean release at or above the current minimum together with canonical Mathlib at an exactly matching Lean toolchain; regenerate manifests only there. Port every committed Lean file, including contained projects and applications, to the module system with appropriate public declarations/imports and exposed bodies. Adding a header alone is insufficient. Rebuild and recheck the changed interfaces.
3. Construct a small Challenge using only the allowed canonical dependency closure. Project-specific definitions needed for the statement must be stated directly in that audited file, with their ordinary mathematical meaning, rather than imported from the project. Prove the corresponding Solution declarations and compare the actual types/definition values. Preserve all main claims attributed to the selected formalization and disclose limitations. Aim below 300 lines/32 KiB; the hard Challenge caps are 1,000 physical lines and 100 KiB.
4. Complete the v0.4 metadata, approved root license, and one Comparator configuration per intended entry. Use only the permitted standard axioms (`propext`, `Classical.choice`, `Quot.sound`) in Solution closures. Recheck full dependency identities, artifacts, source visibility, and correspondence on the new commit.
5. Re-read and pin the actual current verifier commit before adding or running CI. The reusable `PalomarRegistry/PalomarSubmission/.github/workflows/submission.yml` reference and its `pipeline_commit` must be the same full SHA; use `mode: full`, `execution_profile: palomar-standard-v1`, and the exact repository commit/project/configuration paths. Require a passing mechanical report. This preparation has not configured, dispatched, or passed that workflow.
6. Review the resulting exact-commit reports before any intake or registration. Intake authorization and its temporary tag/gist mechanism are separate later actions; no tag, gist, submission, or registry entry has been created here.

The current verifier describes bundled `lake comparator`, `leanexport`, `leanchecker`, NanoDa and con-ron under bubblewrap. Older policy passages describing other tool names must not be used as a current execution recipe. Historical checks are evidence about their recorded snapshot, not a pass of today's reusable workflow.

## Sources checked on 16 October 2026

- [Current contribution policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md), read in GitHub HTML rather than relying on a cached raw copy.
- [Current intake and preflight instructions](https://submit.palomar-registry.org/llms.txt).
- [Minimum toolchain declaration](https://github.com/PalomarRegistry/PalomarSubmission/blob/main/toolchains.json).
- [Verifier and reusable-workflow documentation](https://github.com/PalomarRegistry/PalomarSubmission).

These are preparation references, not a pinned verifier choice. Recheck them when scheduling a migration or full preflight.
