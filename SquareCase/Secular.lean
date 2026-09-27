/-
Theorem 6.2 of *The Square Case* (Jeromie Beasley, DOI 10.5281/zenodo.21855590): the
eigenvalue block `D_t − g tᵀ` and its secular equation `Σ gᵢ tᵢ/(tᵢ − μ) = 1`.

Proved here:
* every eigenvalue `μ` that is not one of the `tᵢ` is a root of the secular equation;
* the secular function strictly increases across any interval that contains no `tᵢ`, when
  every `gᵢ tᵢ > 0`;
* hence each gap between consecutive `tᵢ` holds at most one eigenvalue: the eigenvalues are
  separated by the `tᵢ`.
-/
import SquareCase.Transport

namespace SquareCase.Secular

open Matrix Finset Set SquareCase.Transport

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The secular function `f(x) = Σ gᵢ tᵢ/(tᵢ − x)`. -/
noncomputable def secular (t g : n → ℝ) (x : ℝ) : ℝ := ∑ i, g i * t i / (t i - x)

/-- **Eigenvalues solve the secular equation.** -/
theorem eigenvalue_secular (t g v : n → ℝ) (μ : ℝ) (hne : ∀ i, t i ≠ μ)
    (hv : blockMatrix t g *ᵥ v = μ • v) (hv0 : v ≠ 0) : secular t g μ = 1 := by
  set S := ∑ j, t j * v j with hSdef
  have hrow : ∀ i, t i * v i - g i * S = μ * v i := by
    intro i
    have h := congrFun hv i
    have hvm : (vecMulVec g t *ᵥ v) i = g i * S := by
      simp only [mulVec, dotProduct, vecMulVec_apply, hSdef, mul_sum, mul_assoc]
    rw [blockMatrix, sub_mulVec, Pi.sub_apply, mulVec_diagonal, hvm, Pi.smul_apply,
      smul_eq_mul] at h
    exact h
  have hvi : ∀ i, v i = g i * S / (t i - μ) := by
    intro i
    have h := sub_ne_zero.mpr (hne i)
    rw [eq_div_iff h]
    linarith [hrow i]
  have hS : S ≠ 0 := by
    intro h0
    apply hv0
    funext i
    rw [hvi i, h0]
    simp
  have hsum : S * secular t g μ = S * 1 := by
    rw [mul_one]
    unfold secular
    calc S * ∑ i, g i * t i / (t i - μ) = ∑ i, t i * (g i * S / (t i - μ)) := by
          rw [mul_sum]
          apply sum_congr rfl
          intro i _
          ring
      _ = ∑ i, t i * v i := by
          apply sum_congr rfl
          intro i _
          rw [← hvi i]
      _ = S := rfl
  exact mul_left_cancel₀ hS hsum

/-- One term of the secular function strictly increases across an interval free of its pole. -/
theorem secular_term_lt (c t x y : ℝ) (hc : 0 < c) (hxy : x < y) (ht : t ∉ Icc x y) :
    c / (t - x) < c / (t - y) := by
  have hout : t < x ∨ y < t := by
    by_contra h
    push_neg at h
    exact ht ⟨h.1, h.2⟩
  have hden : 0 < (t - x) * (t - y) := by
    rcases hout with h | h
    · exact mul_pos_of_neg_of_neg (by linarith) (by linarith)
    · exact mul_pos (by linarith) (by linarith)
  have h1 : t - x ≠ 0 := by rcases hout with h | h <;> intro h' <;> linarith
  have h2 : t - y ≠ 0 := by rcases hout with h | h <;> intro h' <;> linarith
  have key : c / (t - x) - c / (t - y) = c * (x - y) / ((t - x) * (t - y)) := by
    field_simp
    ring
  have hneg : c * (x - y) / ((t - x) * (t - y)) < 0 :=
    div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hc (by linarith)) hden
  linarith

/-- **The secular function strictly increases** on any interval that contains no `tᵢ`. -/
theorem secular_strict (t g : n → ℝ) [Nonempty n] (hgt : ∀ i, 0 < g i * t i) (x y : ℝ)
    (hxy : x < y) (hgap : ∀ i, t i ∉ Icc x y) : secular t g x < secular t g y := by
  unfold secular
  exact sum_lt_sum_of_nonempty univ_nonempty
    (fun i _ => secular_term_lt (g i * t i) (t i) x y (hgt i) hxy (hgap i))

/-- **Separation (Theorem 6.2).** Two distinct eigenvalues of `D_t − g tᵀ` never share a gap:
some `tᵢ` lies between them. -/
theorem eigenvalues_separated (t g : n → ℝ) [Nonempty n] (hgt : ∀ i, 0 < g i * t i)
    (x y : ℝ) (hxy : x < y) (v w : n → ℝ) (hv0 : v ≠ 0) (hw0 : w ≠ 0)
    (hv : blockMatrix t g *ᵥ v = x • v) (hw : blockMatrix t g *ᵥ w = y • w)
    (hx : ∀ i, t i ≠ x) (hy : ∀ i, t i ≠ y) : ∃ i, t i ∈ Icc x y := by
  by_contra h
  push_neg at h
  have h1 := eigenvalue_secular t g v x hx hv hv0
  have h2 := eigenvalue_secular t g w y hy hw hw0
  have := secular_strict t g hgt x y hxy h
  linarith

end SquareCase.Secular
