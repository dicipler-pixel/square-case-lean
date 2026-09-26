# Provenance

Every Lean file in `OperatorFirst/` is a byte-identical copy of the file on branch
`formal/fourbody-psd-wall-bridge-2026-09-12` (commit `8857c797440`, "Import PSD four-body
wall bridge into audited root") of the private `operator-first` repository.
`FourBodyWallInvariant`, `HypersurfaceSquareLineage` and `ProjectionTraceBridge` have the
same bytes on `formal/hypersurface-square-lineage-2026-09-11`.

| File | SHA-256 |
| :--- | :--- |
| `FourBodyWallInvariant.lean` | `08bf4561df471392df6bc5b13c7eab521182f9f4096320fa636e4d4c32958433` |
| `FourBodyPSDWallBridge.lean` | `cb0ad26d2b8f392abd5d76daeca1b62e9ca5614880fd1c2faa04c7fbab4c3f4f` |
| `ProjectionTraceBridge.lean` | `3b0407736058b30b4c5ab878237f74b26b9bb6adf1f6bd07f81c4311e86766b7` |
| `HypersurfaceSquareLineage.lean` | `4b81d5d38c00641b611c4a1389b5b586a4aa30e4fe7c24a63325ec674a442c54` |

`SquareCase/Transport.lean` and the three files in `FalseControls/` were written for this
repository; `SquareCase/Transport.lean` is taken from the paper's Sections 2, 5 and 6. The SHA-256 of every
checked file is written to `verification/report.json` on each run.
