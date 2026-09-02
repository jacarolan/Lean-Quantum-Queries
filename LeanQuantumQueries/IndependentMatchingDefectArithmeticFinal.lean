import Mathlib

open scoped BigOperators

namespace IndependentMatchingBlockOccupancy

/-- Pure numerical estimate for the common-direction equations of complete
rooting families. -/
theorem weighted_complete_defect_boundF
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Finset ι) (m : ι → ℝ)
    (q t a b lam V : ℝ)
    (ht : 1 ≤ t) (hq : 0 ≤ q) (hV : 0 ≤ V)
    (hcard : (C.card : ℝ) ≤ t)
    (hmpos : ∀ i ∈ C, 0 < m i)
    (hlower : ∀ i ∈ C, q ≤ 8 * m i)
    (heq : (∑ i ∈ C, m i) * lam = ((C.card : ℝ) - 1) * a + b)
    (hb : b ^ 2 ≤ 8 * t * V) :
    q * ∑ i ∈ C, ((m i * lam) ^ 2 / m i) ≤
      200 * t * (a ^ 2 + V) := by
  classical
  by_cases hC : C = ∅
  · subst C
    simp [ht, hV]
  let r : ℝ := C.card
  let M : ℝ := ∑ i ∈ C, m i
  have hCne : C.Nonempty := Finset.nonempty_iff_ne_empty.2 hC
  have hr : 1 ≤ r := by
    unfold r
    exact_mod_cast Finset.one_le_card.2 hCne
  have hrpos : 0 < r := lt_of_lt_of_le (by norm_num) hr
  have hMpos : 0 < M := by
    unfold M
    exact Finset.sum_pos (fun i hi => (hmpos i hi).le) hCne
  have hqr : q * r ≤ 8 * M := by
    unfold r M
    have hs : ∑ i ∈ C, q ≤ ∑ i ∈ C, 8 * m i :=
      Finset.sum_le_sum fun i hi => hlower i hi
    simpa [Finset.sum_const, nsmul_eq_mul, Finset.mul_sum,
      mul_comm, mul_left_comm, mul_assoc] using hs
  have hratio : q / M ≤ 8 / r := by
    exact (div_le_div_iff₀ hMpos hrpos).2 hqr
  have hsumCancel :
      (∑ i ∈ C, ((m i * lam) ^ 2 / m i)) = M * lam ^ 2 := by
    unfold M
    calc
      (∑ i ∈ C, ((m i * lam) ^ 2 / m i)) =
          ∑ i ∈ C, m i * lam ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        have hmi : m i ≠ 0 := ne_of_gt (hmpos i hi)
        field_simp [hmi]
        ring
      _ = (∑ i ∈ C, m i) * lam ^ 2 := by
        rw [Finset.sum_mul]
  rw [hsumCancel]
  have hrewrite : q * (M * lam ^ 2) =
      (q / M) * (M * lam) ^ 2 := by
    field_simp [ne_of_gt hMpos]
    ring
  rw [hrewrite, heq]
  have hratio0 : 0 ≤ q / M := div_nonneg hq hMpos.le
  have hsq : ((r - 1) * a + b) ^ 2 ≤
      2 * (r - 1) ^ 2 * a ^ 2 + 2 * b ^ 2 := by
    nlinarith [sq_nonneg ((r - 1) * a - b)]
  have hstep1 :
      (q / M) * (((r - 1) * a + b) ^ 2) ≤
        (8 / r) * (((r - 1) * a + b) ^ 2) :=
    mul_le_mul_of_nonneg_right hratio (sq_nonneg _)
  have hstep2 :
      (8 / r) * (((r - 1) * a + b) ^ 2) ≤
        (8 / r) * (2 * (r - 1) ^ 2 * a ^ 2 + 2 * b ^ 2) :=
    mul_le_mul_of_nonneg_left hsq
      (div_nonneg (by norm_num) hrpos.le)
  have hrminus0 : 0 ≤ r - 1 := sub_nonneg.mpr hr
  have hrminus_le : r - 1 ≤ r := by linarith
  have hrminus_sq : (r - 1) ^ 2 ≤ r ^ 2 := by
    have hmul := mul_le_mul hrminus_le hrminus_le hrminus0 hrpos.le
    simpa [pow_two] using hmul
  have ha0 : 0 ≤ a ^ 2 := sq_nonneg _
  have hb0 : 0 ≤ b ^ 2 := sq_nonneg _
  have hfirst :
      (8 / r) * (2 * (r - 1) ^ 2 * a ^ 2) ≤
        16 * r * a ^ 2 := by
    apply (div_le_iff₀ hrpos).2
    have hmul := mul_le_mul_of_nonneg_right hrminus_sq ha0
    nlinarith
  have hsecond :
      (8 / r) * (2 * b ^ 2) ≤ 16 * b ^ 2 := by
    apply (div_le_iff₀ hrpos).2
    nlinarith
  have hbasic :
      (q / M) * (((r - 1) * a + b) ^ 2) ≤
        16 * r * a ^ 2 + 16 * b ^ 2 := by
    calc
      _ ≤ (8 / r) * (((r - 1) * a + b) ^ 2) := hstep1
      _ ≤ (8 / r) *
          (2 * (r - 1) ^ 2 * a ^ 2 + 2 * b ^ 2) := hstep2
      _ = (8 / r) * (2 * (r - 1) ^ 2 * a ^ 2) +
          (8 / r) * (2 * b ^ 2) := by ring
      _ ≤ 16 * r * a ^ 2 + 16 * b ^ 2 := add_le_add hfirst hsecond
  have hrle : r ≤ t := by simpa [r] using hcard
  have ht0 : 0 ≤ t := le_trans (by norm_num) ht
  have hra : 16 * r * a ^ 2 ≤ 16 * t * a ^ 2 :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hrle (by norm_num)) ha0
  have hbV : 16 * b ^ 2 ≤ 128 * t * V := by
    nlinarith
  have hfinal :
      16 * r * a ^ 2 + 16 * b ^ 2 ≤
        200 * t * (a ^ 2 + V) := by
    have hleft := add_le_add hra hbV
    nlinarith
  exact le_trans hbasic hfinal

end IndependentMatchingBlockOccupancy
