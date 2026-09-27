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

/-! ## Existence: every gap holds an eigenvalue -/

theorem secular_split (t g : n → ℝ) (a : n) (x : ℝ) :
    secular t g x = g a * t a / (t a - x) + ∑ i ∈ univ.erase a, g i * t i / (t i - x) := by
  unfold secular
  exact (add_sum_erase _ _ (mem_univ a)).symm

/-- Away from the pole at `t a`, the other terms of the secular function are continuous. -/
theorem rest_tendsto (t g : n → ℝ) (hinj : Function.Injective t) (a : n) (l : Filter ℝ)
    (hl : l ≤ nhds (t a)) :
    Filter.Tendsto (fun x => ∑ i ∈ univ.erase a, g i * t i / (t i - x)) l
      (nhds (∑ i ∈ univ.erase a, g i * t i / (t i - t a))) := by
  apply Filter.Tendsto.mono_left _ hl
  apply tendsto_finset_sum
  intro i hi
  have hne : t i - t a ≠ 0 := sub_ne_zero.mpr (fun h => (mem_erase.mp hi).1 (hinj h))
  exact tendsto_const_nhds.div (tendsto_const_nhds.sub Filter.tendsto_id) hne

/-- Just above a pole `t a` the secular function falls below `1`. -/
theorem secular_below_one_near_left (t g : n → ℝ) (hinj : Function.Injective t)
    (hgt : ∀ i, 0 < g i * t i) (a : n) :
    ∀ᶠ x in nhdsWithin (t a) (Ioi (t a)), secular t g x < 1 := by
  set R := ∑ i ∈ univ.erase a, g i * t i / (t i - t a)
  have hrest := rest_tendsto t g hinj a (nhdsWithin (t a) (Ioi (t a))) nhdsWithin_le_nhds
  have hden : Filter.Tendsto (fun x => t a - x) (nhdsWithin (t a) (Ioi (t a)))
      (nhdsWithin 0 (Iio 0)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have : Filter.Tendsto (fun x => t a - x) (nhds (t a)) (nhds (t a - t a)) :=
        tendsto_const_nhds.sub Filter.tendsto_id
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact sub_neg.mpr (Set.mem_Ioi.mp hx)
  have hterm : Filter.Tendsto (fun x => g a * t a / (t a - x))
      (nhdsWithin (t a) (Ioi (t a))) Filter.atBot := by
    have := (tendsto_inv_nhdsLT_zero.comp hden).const_mul_atBot (hgt a)
    refine this.congr (fun x => ?_)
    simp [div_eq_mul_inv]
  filter_upwards [hterm.eventually (Filter.eventually_lt_atBot (-R)),
    hrest.eventually (Iio_mem_nhds (lt_add_one R))] with x h1 h2
  rw [secular_split t g a x]
  simp only [Set.mem_Iio] at h2
  linarith

/-- Just below a pole `t b` the secular function rises above `1`. -/
theorem secular_above_one_near_right (t g : n → ℝ) (hinj : Function.Injective t)
    (hgt : ∀ i, 0 < g i * t i) (b : n) :
    ∀ᶠ x in nhdsWithin (t b) (Iio (t b)), 1 < secular t g x := by
  set R := ∑ i ∈ univ.erase b, g i * t i / (t i - t b)
  have hrest := rest_tendsto t g hinj b (nhdsWithin (t b) (Iio (t b))) nhdsWithin_le_nhds
  have hden : Filter.Tendsto (fun x => t b - x) (nhdsWithin (t b) (Iio (t b)))
      (nhdsWithin 0 (Ioi 0)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have : Filter.Tendsto (fun x => t b - x) (nhds (t b)) (nhds (t b - t b)) :=
        tendsto_const_nhds.sub Filter.tendsto_id
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact sub_pos.mpr (Set.mem_Iio.mp hx)
  have hterm : Filter.Tendsto (fun x => g b * t b / (t b - x))
      (nhdsWithin (t b) (Iio (t b))) Filter.atTop := by
    have := (tendsto_inv_nhdsGT_zero.comp hden).const_mul_atTop (hgt b)
    refine this.congr (fun x => ?_)
    simp [div_eq_mul_inv]
  filter_upwards [hterm.eventually (Filter.eventually_gt_atTop (2 - R)),
    hrest.eventually (Ioi_mem_nhds (sub_one_lt R))] with x h1 h2
  rw [secular_split t g b x]
  simp only [Set.mem_Ioi] at h2
  linarith

/-- **Existence (Theorem 6.2).** Between two poles `t a < t b` with no other `tᵢ` in between,
the secular equation has a root. -/
theorem secular_root_in_gap (t g : n → ℝ) (hinj : Function.Injective t)
    (hgt : ∀ i, 0 < g i * t i) (a b : n) (hab : t a < t b)
    (hgap : ∀ i, t i ∉ Ioo (t a) (t b)) :
    ∃ μ ∈ Ioo (t a) (t b), secular t g μ = 1 := by
  obtain ⟨x₀, hx₀, hx₀b, hx₀a⟩ := ((secular_below_one_near_left t g hinj hgt a).and
    ((eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hab)).and
      eventually_mem_nhdsWithin)).exists
  simp only [Set.mem_Ioi] at hx₀a
  obtain ⟨y₀, hy₀, hy₀x, hy₀b⟩ := ((secular_above_one_near_right t g hinj hgt b).and
    ((eventually_nhdsWithin_of_eventually_nhds (eventually_gt_nhds hx₀b)).and
      eventually_mem_nhdsWithin)).exists
  simp only [Set.mem_Iio] at hy₀b
  have hsub : Icc x₀ y₀ ⊆ Ioo (t a) (t b) := fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hcont : ContinuousOn (secular t g) (Icc x₀ y₀) := by
    unfold secular
    apply continuousOn_finset_sum
    intro i _
    apply continuousOn_const.div (continuousOn_const.sub continuousOn_id)
    intro x hx h0
    exact hgap i (by rw [sub_eq_zero.mp h0]; exact hsub hx)
  obtain ⟨μ, hμ, hfμ⟩ := intermediate_value_Icc hy₀x.le hcont ⟨hx₀.le, hy₀.le⟩
  exact ⟨μ, hsub hμ, hfμ⟩

/-- **Every gap holds exactly one eigenvalue (Theorem 6.2).** Between consecutive `tᵢ` there
is an eigenvalue of `D_t − g tᵀ`, with eigenvector `vᵢ = gᵢ/(tᵢ − μ)`. -/
theorem eigenvalue_in_gap (t g : n → ℝ) (hinj : Function.Injective t)
    (hgt : ∀ i, 0 < g i * t i) (a b : n) (hab : t a < t b)
    (hgap : ∀ i, t i ∉ Ioo (t a) (t b)) :
    ∃ μ ∈ Ioo (t a) (t b),
      blockMatrix t g *ᵥ (fun i => g i / (t i - μ)) = μ • (fun i => g i / (t i - μ)) := by
  obtain ⟨μ, hμ, hf⟩ := secular_root_in_gap t g hinj hgt a b hab hgap
  refine ⟨μ, hμ, secular_eigenvector t g μ ?_ hf⟩
  intro i h
  exact hgap i (h ▸ hμ)

end SquareCase.Secular
