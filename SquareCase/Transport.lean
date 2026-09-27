/-
Finite results of *The Square Case: Gram Reduction and Spectral Transport for N = d + 1
Bodies* (Jeromie Beasley, DOI 10.5281/zenodo.21855590), written for this repository.

Proved here:
* Proposition 2.1: `G = XᵀX` is invariant under `X ↦ RX` for orthogonal `R`, and `G`
  determines an invertible `X` up to an orthogonal factor.
* Lemma 5.2: `tr(TH + HT − c tr(TH) G) = (2 − c) tr(TH)` when `tr G = 1`, so the transport
  operator preserves the traceless tangent space exactly when `c = 2`.
* Proposition 5.4: on diagonal `H = diag h`, `A(H) = 2 diag((D_t − g tᵀ) h)`.
* Theorem 5.6: `D_t − g tᵀ = S (D_t − u uᵀ) S⁻¹` with `u = √(g ⊙ t)`, `S = diag √(g/t)`;
  and `diag(t/g) (D_t − g tᵀ)` is symmetric.
* Theorem 6.1: `T E + E T = (tᵢ + tⱼ) E` for the symmetrised elementary matrix `E`.
* Theorem 6.2 (eigenvectors): every root `μ ∉ {tᵢ}` of the secular equation
  `Σ gᵢ tᵢ/(tᵢ − μ) = 1` gives the eigenvector `vᵢ = gᵢ/(tᵢ − μ)` of `D_t − g tᵀ` with
  eigenvalue `μ`, and for `μ ≠ 0` and `Σ g = 1` that eigenvector is traceless.
-/
import Mathlib

namespace SquareCase.Transport

open Matrix Finset

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Proposition 2.1 -/

/-- The Gram matrix is invariant under an orthogonal change of frame. -/
theorem gram_invariant (R X : Matrix n n ℝ) (hR : Rᵀ * R = 1) :
    (R * X)ᵀ * (R * X) = Xᵀ * X := by
  rw [transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Rᵀ, hR, Matrix.one_mul]

/-- The Gram matrix determines an invertible configuration up to an orthogonal factor. -/
theorem gram_determines (X Y : Matrix n n ℝ) (hX : IsUnit X.det) (h : Yᵀ * Y = Xᵀ * X) :
    ∃ Q : Matrix n n ℝ, Qᵀ * Q = 1 ∧ Y = Q * X := by
  have hXt : IsUnit Xᵀ.det := by rwa [det_transpose]
  refine ⟨Y * X⁻¹, ?_, ?_⟩
  · rw [transpose_mul, transpose_nonsing_inv, Matrix.mul_assoc, ← Matrix.mul_assoc Yᵀ, h,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, nonsing_inv_mul _ hXt, Matrix.one_mul,
      mul_nonsing_inv _ hX]
  · rw [Matrix.mul_assoc, nonsing_inv_mul _ hX, Matrix.mul_one]

/-! ## Lemma 5.2 -/

/-- The trace of the transport image is `(2 − c) tr(TH)`. -/
theorem trace_transport (T H G : Matrix n n ℝ) (c : ℝ) (hG : trace G = 1) :
    trace (T * H + H * T - (c * trace (T * H)) • G) = (2 - c) * trace (T * H) := by
  rw [trace_sub, trace_add, trace_smul, hG, trace_mul_comm H T, smul_eq_mul]
  ring

/-- **Lemma 5.2**: when `tr(TH) ≠ 0`, the image is traceless exactly when `c = 2`. -/
theorem coefficient_forced (T H G : Matrix n n ℝ) (c : ℝ) (hG : trace G = 1)
    (hTH : trace (T * H) ≠ 0) :
    trace (T * H + H * T - (c * trace (T * H)) • G) = 0 ↔ c = 2 := by
  rw [trace_transport T H G c hG, mul_eq_zero, sub_eq_zero]
  constructor
  · rintro (h | h)
    · exact h.symm
    · exact absurd h hTH
  · intro h
    exact Or.inl h.symm

/-! ## Proposition 5.4 and Theorem 5.6 -/

/-- The eigenvalue-block matrix `D_t − g tᵀ`. -/
def blockMatrix (t g : n → ℝ) : Matrix n n ℝ := diagonal t - vecMulVec g t

/-- **Proposition 5.4**: on diagonal `H = diag h`, `A(H) = 2 diag((D_t − g tᵀ) h)`. -/
theorem transport_on_diagonal (t g h : n → ℝ) :
    diagonal t * diagonal h + diagonal h * diagonal t -
        (2 * trace (diagonal t * diagonal h)) • diagonal g =
      diagonal (fun i => 2 * (blockMatrix t g *ᵥ h) i) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    have htr : trace (diagonal t * diagonal h) = ∑ j, t j * h j := by
      simp [Matrix.trace, diagonal_mul_diagonal]
    have hrow : (vecMulVec g t *ᵥ h) i = g i * ∑ j, t j * h j := by
      simp only [mulVec, dotProduct, vecMulVec_apply, mul_sum, mul_assoc]
    rw [htr]
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, diagonal_mul_diagonal,
      diagonal_apply_eq, smul_eq_mul]
    rw [blockMatrix, sub_mulVec, Pi.sub_apply, mulVec_diagonal, hrow]
    ring
  · simp [hij, diagonal_apply]

/-- **Theorem 5.6**: the eigenvalue block is diagonally similar to a symmetric rank-one
modification: `S (D_t − u uᵀ) S⁻¹ = D_t − g tᵀ`. -/
theorem symmetrisation (t g : n → ℝ) (ht : ∀ i, 0 < t i) (hg : ∀ i, 0 < g i) :
    diagonal (fun i => Real.sqrt (g i / t i)) *
        (diagonal t - vecMulVec (fun i => Real.sqrt (g i * t i))
          (fun i => Real.sqrt (g i * t i))) *
        diagonal (fun i => Real.sqrt (t i / g i)) = blockMatrix t g := by
  have su : ∀ i, Real.sqrt (g i / t i) * Real.sqrt (g i * t i) = g i := by
    intro i
    have h1 := (ht i).ne'
    have h2 := (hg i).ne'
    rw [← Real.sqrt_mul (div_nonneg (hg i).le (ht i).le),
      show g i / t i * (g i * t i) = g i ^ 2 by field_simp <;> ring, Real.sqrt_sq (hg i).le]
  have us : ∀ i, Real.sqrt (g i * t i) * Real.sqrt (t i / g i) = t i := by
    intro i
    have h1 := (ht i).ne'
    have h2 := (hg i).ne'
    rw [← Real.sqrt_mul (mul_nonneg (hg i).le (ht i).le),
      show g i * t i * (t i / g i) = t i ^ 2 by field_simp <;> ring, Real.sqrt_sq (ht i).le]
  have ss : ∀ i, Real.sqrt (g i / t i) * Real.sqrt (t i / g i) = 1 := by
    intro i
    have h1 := (ht i).ne'
    have h2 := (hg i).ne'
    rw [← Real.sqrt_mul (div_nonneg (hg i).le (ht i).le),
      show g i / t i * (t i / g i) = 1 by field_simp <;> ring, Real.sqrt_one]
  ext i j
  rw [mul_diagonal, diagonal_mul]
  by_cases hij : i = j
  · subst hij
    simp only [blockMatrix, Matrix.sub_apply, diagonal_apply_eq, vecMulVec_apply]
    have e1 := su i
    have e2 := us i
    have e3 := ss i
    calc Real.sqrt (g i / t i) * (t i - Real.sqrt (g i * t i) * Real.sqrt (g i * t i)) *
          Real.sqrt (t i / g i)
        = t i * (Real.sqrt (g i / t i) * Real.sqrt (t i / g i)) -
            (Real.sqrt (g i / t i) * Real.sqrt (g i * t i)) *
              (Real.sqrt (g i * t i) * Real.sqrt (t i / g i)) := by ring
      _ = t i - g i * t i := by rw [e1, e2, e3, mul_one]
  · simp only [blockMatrix, Matrix.sub_apply, diagonal_apply_ne _ hij, vecMulVec_apply, zero_sub]
    calc Real.sqrt (g i / t i) * -(Real.sqrt (g i * t i) * Real.sqrt (g j * t j)) *
          Real.sqrt (t j / g j)
        = -((Real.sqrt (g i / t i) * Real.sqrt (g i * t i)) *
            (Real.sqrt (g j * t j) * Real.sqrt (t j / g j))) := by ring
      _ = -(g i * t j) := by rw [su i, us j]

/-- **Theorem 5.6**: `D_t − g tᵀ` is self-adjoint for the weight `diag(t/g)`. -/
theorem weighted_symmetric (t g : n → ℝ) (hg : ∀ i, g i ≠ 0) :
    (diagonal (fun i => t i / g i) * blockMatrix t g)ᵀ =
      diagonal (fun i => t i / g i) * blockMatrix t g := by
  ext i j
  simp only [transpose_apply, diagonal_mul, blockMatrix, Matrix.sub_apply, vecMulVec_apply]
  by_cases hij : i = j
  · subst hij
    rfl
  · rw [diagonal_apply_ne _ hij, diagonal_apply_ne _ (Ne.symm hij)]
    field_simp [hg i, hg j] <;> ring

/-! ## Theorems 6.1 and 6.2 -/

/-- The symmetrised elementary matrix `E_ij`. -/
def symElem (i j : n) : Matrix n n ℝ :=
  fun k l => if (k = i ∧ l = j) ∨ (k = j ∧ l = i) then 1 else 0

/-- **Theorem 6.1**: `T E_ij + E_ij T = (tᵢ + tⱼ) E_ij` for diagonal `T`. -/
theorem eigenframe_spectrum (t : n → ℝ) (i j : n) :
    diagonal t * symElem i j + symElem i j * diagonal t = (t i + t j) • symElem i j := by
  ext k l
  simp only [Matrix.add_apply, diagonal_mul, mul_diagonal, Matrix.smul_apply, smul_eq_mul, symElem]
  by_cases h : (k = i ∧ l = j) ∨ (k = j ∧ l = i)
  · rw [if_pos h]
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> ring
  · rw [if_neg h]
    ring

/-- **Theorem 6.2 (eigenvectors)**: a root `μ` of the secular equation gives the eigenvector
`vᵢ = gᵢ / (tᵢ − μ)` of `D_t − g tᵀ` with eigenvalue `μ`. -/
theorem secular_eigenvector (t g : n → ℝ) (μ : ℝ) (hne : ∀ i, t i ≠ μ)
    (hsec : ∑ i, g i * t i / (t i - μ) = 1) :
    blockMatrix t g *ᵥ (fun i => g i / (t i - μ)) = μ • (fun i => g i / (t i - μ)) := by
  have hs2 : ∑ j, t j * (g j / (t j - μ)) = 1 := by
    rw [← hsec]
    apply sum_congr rfl
    intro j _
    ring
  ext i
  have hrow : (vecMulVec g t *ᵥ fun i => g i / (t i - μ)) i =
      g i * ∑ j, t j * (g j / (t j - μ)) := by
    simp only [mulVec, dotProduct, vecMulVec_apply, mul_sum, mul_assoc]
  rw [blockMatrix, sub_mulVec, Pi.sub_apply, mulVec_diagonal, hrow, hs2, Pi.smul_apply,
    smul_eq_mul]
  have h := sub_ne_zero.mpr (hne i)
  field_simp <;> ring

/-- For `μ ≠ 0` and `Σ g = 1` the secular eigenvector is traceless, so it lies in the
tangent space of the trace-one slice. -/
theorem secular_eigenvector_traceless (t g : n → ℝ) (μ : ℝ) (hμ : μ ≠ 0)
    (hne : ∀ i, t i ≠ μ) (hg : ∑ i, g i = 1) (hsec : ∑ i, g i * t i / (t i - μ) = 1) :
    ∑ i, g i / (t i - μ) = 0 := by
  have key : ∀ i, g i * t i / (t i - μ) - g i = μ * (g i / (t i - μ)) := by
    intro i
    have h := sub_ne_zero.mpr (hne i)
    field_simp <;> ring
  have hsum : μ * ∑ i, g i / (t i - μ) = 0 := by
    rw [mul_sum]
    simp_rw [← key]
    rw [sum_sub_distrib, hsec, hg, sub_self]
  rcases mul_eq_zero.mp hsum with h | h
  · exact absurd h hμ
  · exact h

end SquareCase.Transport
