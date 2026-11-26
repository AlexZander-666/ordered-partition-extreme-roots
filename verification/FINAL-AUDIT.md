# Spark cold verification

The exact frozen source ZIP was independently extracted into an empty local project on Linux ARM64. Lean 4.33.1 built all 114 local project modules with warnings treated as errors. The verifier cross-checked the local imports resolved by Lean and ran 114 separate `leanchecker` processes. The nine external Git checkouts matched the dependency lock. They were supplied through a separately located, version-locked external dependency cache.

The lexical source scan passed. The 304 source reports and 17 additional targeted reports used only `propext`, `Classical.choice` and `Quot.sound`. `module-receipts.tsv` and `axioms.tsv` contain the exact module digests and declarations. `STATEMENT-MAP.md` maps the fixed-threshold outer-root theorem and its degree-dependent orientation to the original rows.

- Source ZIP SHA-256 `7873d151f90b0fded928c6af7c32c3771e1b2e97674d3e11990f592b0e994ff1`
- Entry source SHA-256 `e9545a3425fcb9160ae16fd48f868732b1372d418f897151abe923a6b0d6e0b3`
- Cold log SHA-256 `d147839d0d49fcf0ed15ce2ea40fbfc94346656770ca360dcf23adfa728229b0`

Use `python3 -B run-cold.py /absolute/path/to/locked/.lake/packages --workers 2` next to the source ZIP to extract the project into a fresh temporary directory and verify it again. The README inside the ZIP also gives the commands for direct verification after extraction.
