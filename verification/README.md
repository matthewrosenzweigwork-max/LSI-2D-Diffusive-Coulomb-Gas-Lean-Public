# Verification provenance

The frozen input contains 1,936 files, including 1,932 Lean files. Every copy is bound by size and SHA-256 in PUBLIC_SOURCE_MANIFEST.json. The source was copied byte for byte from the accepted solution-source tree at upstream commit 7ebe828bf7f69471c8120bd03a876666abd8e53f.

The original direct verification completed on 10 October 2026 at 17:17:03 UTC. It covered 148 theorems, four frozen definitions, and 185 export roots. The recorded checks passed Lean's default kernel, strict Nanoda, Comparator exact statement/body comparisons, declaration-kind checks, and transitive axiom restrictions to propext, Classical.choice and Quot.sound. This is historical verification provenance; publication is not a new kernel replay or a new manuscript-correspondence audit.

Historical source checkpoint: 53a726b63365b27777d0ce18d036482ff8a8ade4.
Source ledger SHA-256: 0d0e716e1ea32fe305436e61401d9a75cc0289d323cb6b17240a9324bc0df157.
Accepted solution assembly manifest SHA-256: 1725aaf7b33476b6e18aa4d7761478cbc91ad19301a9d1aab33d704a4fac24f9.
Historical final report SHA-256: 319b730baa06b454c5846cfc8ae78c09385ade5ff231200b58f5349e06ac4ca1.

All 1,932 Lean files are reachable from the exact audit-build roots. This establishes module reachability, not the necessity of every declaration. Imported helper files are preserved rather than rewritten. Duplicate source trees, challenge files, private runtime history, operational logs, and author-review material are omitted.

To check the published source bytes, run `python3 verification/check_sources.py`.
