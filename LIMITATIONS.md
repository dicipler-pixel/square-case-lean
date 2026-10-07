# Limitations

These files prove finite-dimensional algebra. They do not prove:

- the physical derivation of the inertia tensor `T`, the wall matrix `W` or the flow itself;
- that the four-body wall is a smooth hypersurface of the trace-one Gram slice;
- the counting statement that the gap eigenvalues exhaust the spectrum of the eigenvalue block;
  Theorem 6.2's interlacing (exactly one eigenvalue in each gap between distinct `tᵢ`, for
  `gᵢtᵢ > 0`) is proved, as two theorems: existence (`eigenvalue_in_gap`) and at most one per
  gap (`eigenvalues_separated`). Also the boundary spectrum (Theorem 6.5) and Section 11;
- Theorem 6.1 beyond the relation `T E_ij + E_ij T = (tᵢ + tⱼ) E_ij` for diagonal `T`, which is
  proved for the map `H ↦ TH + HT` without the trace term of the transport operator;
- any identification of the projector metric with a spacetime metric. In
  `HypersurfaceSquareLineage`, `g = n²` is an explicit hypothesis, not a claim;
- the reduced four-body wall map is a two-variable model, not the full flow;
- that the model definitions in `HypersurfaceSquareLineage` describe the physics. The fold/Gram
  `1/s⁴` and three-body `sec⁴θ` statements are algebra on `gramSoft s = s²` and
  `rigidityFromGram λ = 1/λ²`, and the rank-one distance `2 sin²θ` is proved for the
  hand-expanded entrywise formula `rankOneProjectorHSDistanceSq`, not for projector matrices.

Model-specific inputs appear as named hypotheses of each theorem or, in
`HypersurfaceSquareLineage`, as the model definitions named above.

A file-by-file mapping of the `OperatorFirst/` results to statements of *5D Spectral Anatomy of
Four-Body Obstructions* is not yet given.
