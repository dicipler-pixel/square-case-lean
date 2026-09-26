import OperatorFirst.FourBodyPSDWallBridge
-- Without positive semidefiniteness the wall bridge fails: for W = diag(1, -1) and
-- L = (1, 1), L·(W L) = 1 - 1 = 0, yet the first entry of W L is 1, not 0.
example : (1:ℝ) * 1 + (-1) * 1 = 0 → (1:ℝ) * 1 = 0 := by norm_num
