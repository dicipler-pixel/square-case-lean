import OperatorFirst.FourBodyWallInvariant
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Positive-semidefinite binary-wall bridge

Closes the remaining finite-dimensional bridge in the four-body wall module:
for a positive-semidefinite matrix, vanishing of the wall quadratic form in a
collision direction is equivalent to that direction lying in the matrix kernel.

This removes the need to assume the wall null-vector condition separately once
positive semidefiniteness and the wall equation are available.  It does not
formalize the physical derivation of the matrix itself.
-/

open Matrix

namespace OperatorFirst.FourBodyWallInvariant

variable {n : Type*} [Fintype n]

/-- On a real positive-semidefinite matrix, the binary-wall equation
`L^T W L = 0` is equivalent to `W L = 0`.

This is the exact bridge left open in `FourBodyWallInvariant.lean`. -/
theorem wallScalar_zero_iff_mulVec_zero_of_posSemidef
    (L : n → ℝ) (W : Matrix n n ℝ) (hW : W.PosSemidef) :
    wallScalar L W = 0 ↔ W *ᵥ L = 0 := by
  simpa [wallScalar] using
    (Matrix.PosSemidef.dotProduct_mulVec_zero_iff hW (x := L))

/-- The wall equation supplies the null-vector hypothesis required by the
connection-correction theorem whenever the wall matrix is positive semidefinite. -/
theorem wallScalar_zero_implies_mulVec_zero_of_posSemidef
    (L : n → ℝ) (W : Matrix n n ℝ) (hW : W.PosSemidef)
    (hWall : wallScalar L W = 0) :
    W *ᵥ L = 0 :=
  (wallScalar_zero_iff_mulVec_zero_of_posSemidef L W hW).mp hWall

/-- Full tangent invariance with the wall null-vector condition derived rather
than assumed.  Symmetry is kept explicit here because it is the exact
hypothesis consumed by the previously verified commutator lemma; PSD already
contains the corresponding Hermitian property, but no physical identification
is added by this wrapper. -/
theorem intrinsic_preserves_wall_tangent_of_posSemidef
    (L : n → ℝ) (T W H Omega : Matrix n n ℝ) (lambda : ℝ)
    (hTsymm : T.transpose = T)
    (hWsymm : W.transpose = W)
    (hWpsd : W.PosSemidef)
    (hEig : T *ᵥ L = lambda • L)
    (hWall : wallScalar L W = 0)
    (hTan : wallTangent L H) :
    wallTangent L (rawIntrinsic T W H - (Omega * W - W * Omega)) := by
  have hNull : W *ᵥ L = 0 :=
    wallScalar_zero_implies_mulVec_zero_of_posSemidef L W hWpsd hWall
  exact intrinsic_preserves_wall_tangent L T W H Omega lambda
    hTsymm hWsymm hEig hNull hTan

end OperatorFirst.FourBodyWallInvariant

#print axioms OperatorFirst.FourBodyWallInvariant.wallScalar_zero_iff_mulVec_zero_of_posSemidef
#print axioms OperatorFirst.FourBodyWallInvariant.wallScalar_zero_implies_mulVec_zero_of_posSemidef
#print axioms OperatorFirst.FourBodyWallInvariant.intrinsic_preserves_wall_tangent_of_posSemidef
