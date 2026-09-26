import Mathlib

/-!
# OperatorFirst.ProjectionTraceBridge

Finite-dimensional algebra for orthogonal projections.

This module deliberately avoids principal-angle or SVD machinery.  Its central
identity is the trace form of the Hilbert--Schmidt distance between two
orthogonal projections:

  Tr((P-Q)^T(P-Q)) = Tr P + Tr Q - 2 Tr(PQ).

For equal-rank projections this becomes `2k - 2 Tr(PQ)`.  Thus the rank-one
`2 sin^2(theta)` formula and the higher-rank persistence quantity `Tr(PQ)` are
instances of the same finite matrix identity once their respective geometric
interpretations are supplied.
-/

open Matrix

namespace OperatorFirst.ProjectionTraceBridge

variable {n : Type*} [Fintype n]

/-- Algebraic Hilbert--Schmidt/Frobenius square over real matrices. -/
def frobeniusSq (A : Matrix n n ℝ) : ℝ :=
  Matrix.trace (A.transpose * A)

/-- Expanding the square of the difference of two idempotents. -/
theorem projection_difference_square
    (P Q : Matrix n n ℝ)
    (hP : P * P = P) (hQ : Q * Q = Q) :
    (P - Q) * (P - Q) = P + Q - (P * Q + Q * P) := by
  calc
    (P - Q) * (P - Q)
        = P * P - P * Q - Q * P + Q * Q := by noncomm_ring
    _ = P - P * Q - Q * P + Q := by rw [hP, hQ]
    _ = P + Q - (P * Q + Q * P) := by noncomm_ring

/-- For symmetric matrices, Frobenius square is the trace of the ordinary
square. -/
theorem frobeniusSq_eq_trace_square_of_symmetric
    (A : Matrix n n ℝ) (hA : A.transpose = A) :
    frobeniusSq A = Matrix.trace (A * A) := by
  unfold frobeniusSq
  rw [hA]

/-- The k-dimensional projection trace bridge.

No rank equality, principal angles, or SVD are required. -/
theorem orthogonal_projection_frobenius_sq
    (P Q : Matrix n n ℝ)
    (hPsymm : P.transpose = P) (hQsymm : Q.transpose = Q)
    (hPidem : P * P = P) (hQidem : Q * Q = Q) :
    frobeniusSq (P - Q)
      = Matrix.trace P + Matrix.trace Q - 2 * Matrix.trace (P * Q) := by
  have hsymm : (P - Q).transpose = P - Q := by
    rw [Matrix.transpose_sub, hPsymm, hQsymm]
  rw [frobeniusSq_eq_trace_square_of_symmetric (P - Q) hsymm]
  rw [projection_difference_square P Q hPidem hQidem]
  simp only [Matrix.trace_sub, Matrix.trace_add]
  rw [Matrix.trace_mul_comm Q P]
  ring

/-- Equal trace `k` gives the persistence form `2k - 2 Tr(PQ)`.  In the
orthogonal-projection setting, equal trace is the finite-dimensional rank
condition. -/
theorem equal_trace_projection_frobenius_sq
    (P Q : Matrix n n ℝ) (k : ℝ)
    (hPsymm : P.transpose = P) (hQsymm : Q.transpose = Q)
    (hPidem : P * P = P) (hQidem : Q * Q = Q)
    (htrP : Matrix.trace P = k) (htrQ : Matrix.trace Q = k) :
    frobeniusSq (P - Q) = 2 * k - 2 * Matrix.trace (P * Q) := by
  rw [orthogonal_projection_frobenius_sq P Q hPsymm hQsymm hPidem hQidem,
      htrP, htrQ]
  ring

/-- Rearranged equal-rank identity: persistence is determined by distance. -/
theorem persistence_from_frobenius_sq
    (P Q : Matrix n n ℝ) (k : ℝ)
    (hPsymm : P.transpose = P) (hQsymm : Q.transpose = Q)
    (hPidem : P * P = P) (hQidem : Q * Q = Q)
    (htrP : Matrix.trace P = k) (htrQ : Matrix.trace Q = k) :
    Matrix.trace (P * Q) = k - frobeniusSq (P - Q) / 2 := by
  have h := equal_trace_projection_frobenius_sq P Q k hPsymm hQsymm hPidem hQidem htrP htrQ
  linarith

end OperatorFirst.ProjectionTraceBridge

#print axioms OperatorFirst.ProjectionTraceBridge.projection_difference_square
#print axioms OperatorFirst.ProjectionTraceBridge.frobeniusSq_eq_trace_square_of_symmetric
#print axioms OperatorFirst.ProjectionTraceBridge.orthogonal_projection_frobenius_sq
#print axioms OperatorFirst.ProjectionTraceBridge.equal_trace_projection_frobenius_sq
#print axioms OperatorFirst.ProjectionTraceBridge.persistence_from_frobenius_sq
