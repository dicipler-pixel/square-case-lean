import Mathlib

/-!
# OperatorFirst.FourBodyWallInvariant

Finite-dimensional algebra extracted from the four-body binary-wall construction.

The source wall is the zero set of the scalar functional

  sigma_L(W) = L W L^T.

At a wall point, tangent variations satisfy the linearized condition

  L H L^T = 0.

For the raw intrinsic term

  H_T = T H + H T - Tr(T H) W,

if the collision row is an eigenrow of the local inertia tensor,

  L T = lambda L,

then the raw term preserves the wall tangent condition.

For the mechanical-connection correction `[Omega,W]`, if the wall direction is a
null direction of `W`, then the correction also has zero wall functional. The
full projected intrinsic term therefore preserves the wall tangent space under
these explicit hypotheses.

This module does not claim the PSD implication
`L W L^T = 0 -> W L^T = 0`; that is isolated as the remaining bridge needed to
recover the null-vector hypothesis directly from positive semidefiniteness.
-/

open Matrix

namespace OperatorFirst.FourBodyWallInvariant

variable {n : Type*} [Fintype n]

/-- Row-vector form of the binary-wall scalar `L W L^T`. -/
def wallScalar (L : n → ℝ) (W : Matrix n n ℝ) : ℝ :=
  L ⬝ᵥ (W *ᵥ L)

/-- The linearized binary-wall condition. Because `wallScalar` is linear in
`W`, this is exactly the derivative of the wall equation along `H`. -/
def wallTangent (L : n → ℝ) (H : Matrix n n ℝ) : Prop :=
  wallScalar L H = 0

/-- The wall functional is linear in the matrix argument. -/
theorem wallScalar_add (L : n → ℝ) (A B : Matrix n n ℝ) :
    wallScalar L (A + B) = wallScalar L A + wallScalar L B := by
  simp [wallScalar, Matrix.add_mulVec, dotProduct_add]

/-- Scalar homogeneity of the wall functional. -/
theorem wallScalar_smul (L : n → ℝ) (c : ℝ) (A : Matrix n n ℝ) :
    wallScalar L (c • A) = c * wallScalar L A := by
  simp [wallScalar, Matrix.smul_mulVec, dotProduct_smul]

/-- A line `W + t H` stays on this linear wall whenever the base point lies on
the wall and `H` satisfies the wall tangent condition. -/
theorem wall_line_stays_zero
    (L : n → ℝ) (W H : Matrix n n ℝ)
    (hW : wallScalar L W = 0) (hH : wallTangent L H) (t : ℝ) :
    wallScalar L (W + t • H) = 0 := by
  rw [wallScalar_add, wallScalar_smul, hW]
  simp [wallTangent] at hH
  rw [hH]
  ring

/-- Raw symmetrized intrinsic term before the horizontal connection correction. -/
def rawIntrinsic (T W H : Matrix n n ℝ) : Matrix n n ℝ :=
  T * H + H * T - (Matrix.trace (T * H)) • W

/-- If `L` is a right eigenvector of `T`, the left action through a symmetric
`T` is also multiplication by `lambda`. -/
theorem transpose_mulVec_eigen
    (T : Matrix n n ℝ) (L : n → ℝ) (lambda : ℝ)
    (hTsymm : T.transpose = T)
    (hEig : T *ᵥ L = lambda • L) :
    T.transpose *ᵥ L = lambda • L := by
  rw [hTsymm]
  exact hEig

/-- The raw symmetrized transport term preserves the binary-wall tangent
condition when the collision vector is an eigenvector of the symmetric local
inertia tensor.

This is the algebra behind the source statement that the parallel component is
mapped back into the parallel tangent space. -/
theorem rawIntrinsic_preserves_wall_tangent
    (L : n → ℝ) (T W H : Matrix n n ℝ) (lambda : ℝ)
    (hTsymm : T.transpose = T)
    (hEig : T *ᵥ L = lambda • L)
    (hWall : wallScalar L W = 0)
    (hTan : wallTangent L H) :
    wallTangent L (rawIntrinsic T W H) := by
  unfold wallTangent rawIntrinsic wallScalar at *
  have hleft : L ⬝ᵥ ((T * H) *ᵥ L) = lambda * (L ⬝ᵥ (H *ᵥ L)) := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
    rw [← Matrix.mulVec_transpose, hTsymm, hEig]
    rw [smul_dotProduct]
    rfl
  have hright : L ⬝ᵥ ((H * T) *ᵥ L) = lambda * (L ⬝ᵥ (H *ᵥ L)) := by
    rw [← Matrix.mulVec_mulVec, hEig, Matrix.mulVec_smul, dotProduct_smul]
    rfl
  rw [Matrix.sub_mulVec, Matrix.add_mulVec]
  simp only [dotProduct_sub, dotProduct_add]
  rw [hleft, hright]
  simp only [Matrix.smul_mulVec, dotProduct_smul]
  rw [hTan, hWall]
  ring

/-- A null wall direction kills the first half of the connection commutator. -/
theorem wallScalar_left_commutator_term_zero
    (L : n → ℝ) (Omega W : Matrix n n ℝ)
    (hNull : W *ᵥ L = 0) :
    L ⬝ᵥ ((Omega * W) *ᵥ L) = 0 := by
  rw [← Matrix.mulVec_mulVec, hNull]
  simp

/-- For symmetric `W`, a null right direction also kills the second half of the
connection commutator in the wall functional. -/
theorem wallScalar_right_commutator_term_zero
    (L : n → ℝ) (Omega W : Matrix n n ℝ)
    (hWsymm : W.transpose = W)
    (hNull : W *ᵥ L = 0) :
    L ⬝ᵥ ((W * Omega) *ᵥ L) = 0 := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
  rw [← Matrix.mulVec_transpose, hWsymm, hNull]
  simp

/-- The horizontal connection correction `[Omega,W]` is tangent to the binary
wall whenever the collision direction is a null direction of the symmetric wall
matrix. -/
theorem commutator_correction_preserves_wall
    (L : n → ℝ) (Omega W : Matrix n n ℝ)
    (hWsymm : W.transpose = W)
    (hNull : W *ᵥ L = 0) :
    wallTangent L (Omega * W - W * Omega) := by
  unfold wallTangent wallScalar
  rw [Matrix.sub_mulVec, dotProduct_sub]
  rw [wallScalar_left_commutator_term_zero L Omega W hNull]
  rw [wallScalar_right_commutator_term_zero L Omega W hWsymm hNull]
  simp

/-- Full algebraic tangent-invariance theorem for the source-form intrinsic
operator `rawIntrinsic - [Omega,W]`.

This is the formal source of the lower-left zero once the geometric hypotheses
(eigenrow and wall null direction) have been established for the physical
four-body realization. -/
theorem intrinsic_preserves_wall_tangent
    (L : n → ℝ) (T W H Omega : Matrix n n ℝ) (lambda : ℝ)
    (hTsymm : T.transpose = T)
    (hWsymm : W.transpose = W)
    (hEig : T *ᵥ L = lambda • L)
    (hNull : W *ᵥ L = 0)
    (hTan : wallTangent L H) :
    wallTangent L (rawIntrinsic T W H - (Omega * W - W * Omega)) := by
  have hWall : wallScalar L W = 0 := by
    unfold wallScalar
    rw [hNull]
    simp
  have hRaw := rawIntrinsic_preserves_wall_tangent L T W H lambda hTsymm hEig hWall hTan
  have hCorr := commutator_correction_preserves_wall L Omega W hWsymm hNull
  unfold wallTangent at *
  unfold wallScalar at *
  rw [Matrix.sub_mulVec, dotProduct_sub, hRaw, hCorr]
  simp

end OperatorFirst.FourBodyWallInvariant

#print axioms OperatorFirst.FourBodyWallInvariant.wallScalar_add
#print axioms OperatorFirst.FourBodyWallInvariant.wallScalar_smul
#print axioms OperatorFirst.FourBodyWallInvariant.wall_line_stays_zero
#print axioms OperatorFirst.FourBodyWallInvariant.transpose_mulVec_eigen
#print axioms OperatorFirst.FourBodyWallInvariant.rawIntrinsic_preserves_wall_tangent
#print axioms OperatorFirst.FourBodyWallInvariant.wallScalar_left_commutator_term_zero
#print axioms OperatorFirst.FourBodyWallInvariant.wallScalar_right_commutator_term_zero
#print axioms OperatorFirst.FourBodyWallInvariant.commutator_correction_preserves_wall
#print axioms OperatorFirst.FourBodyWallInvariant.intrinsic_preserves_wall_tangent
