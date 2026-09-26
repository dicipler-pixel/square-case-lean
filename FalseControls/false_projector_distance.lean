import OperatorFirst.HypersurfaceSquareLineage
-- Two orthogonal lines (θ = π/2) are at squared projector distance 2 sin²θ = 2, not 1.
example : 2 * Real.sin (Real.pi / 2) ^ 2 = (1:ℝ) := by norm_num
