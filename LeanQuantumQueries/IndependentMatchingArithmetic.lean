import Mathlib

open scoped BigOperators

namespace IndependentMatchingBlockOccupancy

/-- A numerical estimate used for the means of complete rooting families.
The hypotheses are exactly the identities and cardinality inequalities later
proved from the sector construction. -/
theorem weighted_complete_mean_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Finset ι) (m μ : ι → ℝ)
    (q t a b lam V : ℝ)
    (ht : 1 ≤ t)
    (hq : 0 ≤ q)
    (hV : 0 ≤ V)
    (hcard : (C.card : ℝ) ≤ t)
    (hmpos : ∀ i ∈ C, 0 < m i)
    (hlower : ∀ i ∈ C, q ≤ 8 * m i)
    (hupper : ∀ i ∈ C, m i ≤ q)
    (hrel : ∀ i ∈ C, μ i = a - m i * lam)
    (heq : (∑ i ∈ C, m i) * lam = ((C.card : ℝ) - 1) * a + b)
    (hb : b ^ 2 ≤ 8 * t * V) :
    q * ∑ i ∈ C, (μ i) ^ 2 / m i ≤
      20000 * t * (a ^ 2 + V) := by
  classical
  by_cases hC : C = ∅
  · subst C
    simp only [Finset.sum_empty, mul_zero]
    have ht0 : 0 ≤ t := le_trans (by norm_num) ht
    positivity
  have hCne : C.Nonempty := Finset.nonempty_iff_ne_empty.2 hC
  have hrNat : 1 ≤ C.card := Finset.one_le_card.2 hCne
  have hr : (1 : ℝ) ≤ (C.card : ℝ) := by exact_mod_cast hrNat
  have hr0 : 0 ≤ (C.card : ℝ) := by positivity
  have hM0 : 0 ≤ ∑ i ∈ C, m i := by
    apply Finset.sum_nonneg
    intro i hi
    exact (hmpos i hi).le
  have hqr : q * (C.card : ℝ) ≤ 8 * ∑ i ∈ C, m i := by
    have hs : ∑ i ∈ C, q ≤ ∑ i ∈ C, 8 * m i := by
      apply Finset.sum_le_sum
      intro i hi
      exact hlower i hi
    calc
      q * (C.card : ℝ) = ∑ i ∈ C, q := by
        simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ i ∈ C, 8 * m i := hs
      _ = 8 * ∑ i ∈ C, m i := by
        rw [Finset.mul_sum]
  have hterm : ∀ i ∈ C,
      q * ((μ i) ^ 2 / m i) ≤ 8 * (μ i) ^ 2 := by
    intro i hi
    have hmi := hmpos i hi
    have hdiv : q / m i ≤ 8 := (div_le_iff₀ hmi).2 (hlower i hi)
    calc
      q * ((μ i) ^ 2 / m i) = (q / m i) * (μ i) ^ 2 := by ring
      _ ≤ 8 * (μ i) ^ 2 :=
        mul_le_mul_of_nonneg_right hdiv (sq_nonneg _)
  have hsumTerm :
      q * ∑ i ∈ C, (μ i) ^ 2 / m i ≤
        8 * ∑ i ∈ C, (μ i) ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi => hterm i hi
  have hpoint : ∀ i ∈ C,
      ((C.card : ℝ) ^ 2) * (μ i) ^ 2 ≤
        258 * ((C.card : ℝ) ^ 2) * a ^ 2 + 256 * b ^ 2 := by
    intro i hi
    have hmi0 := (hmpos i hi).le
    have hmiq := hupper i hi
    have hrmi : (C.card : ℝ) * m i ≤ 8 * ∑ j ∈ C, m j := by
      calc
        (C.card : ℝ) * m i ≤ (C.card : ℝ) * q :=
          mul_le_mul_of_nonneg_left hmiq hr0
        _ = q * (C.card : ℝ) := by ring
        _ ≤ 8 * ∑ j ∈ C, m j := hqr
    have hrmi0 : 0 ≤ (C.card : ℝ) * m i := mul_nonneg hr0 hmi0
    have h8M0 : 0 ≤ 8 * ∑ j ∈ C, m j := mul_nonneg (by norm_num) hM0
    have hsquare :
        ((C.card : ℝ) * m i) ^ 2 ≤
          (8 * ∑ j ∈ C, m j) ^ 2 := by
      exact (sq_le_sq₀ hrmi0 h8M0).2 hrmi
    have hlam2 : 0 ≤ lam ^ 2 := sq_nonneg _
    have hsquareLam := mul_le_mul_of_nonneg_right hsquare hlam2
    have htransport :
        ((C.card : ℝ) ^ 2) * (m i * lam) ^ 2 ≤
          64 * ((((C.card : ℝ) - 1) * a + b) ^ 2) := by
      rw [← heq]
      nlinarith
    have hsumSq :
        ((((C.card : ℝ) - 1) * a + b) ^ 2) ≤
          2 * (((C.card : ℝ) - 1) ^ 2) * a ^ 2 + 2 * b ^ 2 := by
      nlinarith [sq_nonneg (((C.card : ℝ) - 1) * a - b)]
    have hrminus : ((C.card : ℝ) - 1) ^ 2 ≤ (C.card : ℝ) ^ 2 := by
      nlinarith
    have ha2 : 0 ≤ a ^ 2 := sq_nonneg _
    have htransport' :
        ((C.card : ℝ) ^ 2) * (m i * lam) ^ 2 ≤
          128 * ((C.card : ℝ) ^ 2) * a ^ 2 + 128 * b ^ 2 := by
      nlinarith
    rw [hrel i hi]
    nlinarith [sq_nonneg (a + m i * lam)]
  have hsumPoint :
      ((C.card : ℝ) ^ 2) * ∑ i ∈ C, (μ i) ^ 2 ≤
        (C.card : ℝ) *
          (258 * ((C.card : ℝ) ^ 2) * a ^ 2 + 256 * b ^ 2) := by
    rw [Finset.mul_sum]
    calc
      ∑ i ∈ C, ((C.card : ℝ) ^ 2) * (μ i) ^ 2 ≤
          ∑ _i ∈ C,
            (258 * ((C.card : ℝ) ^ 2) * a ^ 2 + 256 * b ^ 2) := by
        exact Finset.sum_le_sum fun i hi => hpoint i hi
      _ = (C.card : ℝ) *
          (258 * ((C.card : ℝ) ^ 2) * a ^ 2 + 256 * b ^ 2) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
  have hscaled :
      ((C.card : ℝ) ^ 2) *
          (q * ∑ i ∈ C, (μ i) ^ 2 / m i) ≤
        2064 * (C.card : ℝ) ^ 3 * a ^ 2 +
          2048 * (C.card : ℝ) * b ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hsumTerm
      (sq_nonneg (C.card : ℝ))
    nlinarith
  have ha2 : 0 ≤ a ^ 2 := sq_nonneg _
  have hb2 : 0 ≤ b ^ 2 := sq_nonneg _
  have ht0 : 0 ≤ t := le_trans (by norm_num) ht
  have hr_le_sq : (C.card : ℝ) ≤ (C.card : ℝ) ^ 2 := by
    nlinarith
  have hfirst :
      2064 * (C.card : ℝ) ^ 3 * a ^ 2 ≤
        2064 * (C.card : ℝ) ^ 2 * t * a ^ 2 := by
    have hnon : 0 ≤ 2064 * (C.card : ℝ) ^ 2 * a ^ 2 := by positivity
    calc
      2064 * (C.card : ℝ) ^ 3 * a ^ 2 =
          (2064 * (C.card : ℝ) ^ 2 * a ^ 2) * (C.card : ℝ) := by ring
      _ ≤ (2064 * (C.card : ℝ) ^ 2 * a ^ 2) * t :=
        mul_le_mul_of_nonneg_left hcard hnon
      _ = 2064 * (C.card : ℝ) ^ 2 * t * a ^ 2 := by ring
  have hsecondBase :
      2048 * (C.card : ℝ) * b ^ 2 ≤
        2048 * (C.card : ℝ) * (8 * t * V) := by
    exact mul_le_mul_of_nonneg_left hb (by positivity)
  have hsecondGrow :
      2048 * (C.card : ℝ) * (8 * t * V) ≤
        16384 * (C.card : ℝ) ^ 2 * t * V := by
    have hnon : 0 ≤ 16384 * t * V := by positivity
    calc
      2048 * (C.card : ℝ) * (8 * t * V) =
          (16384 * t * V) * (C.card : ℝ) := by ring
      _ ≤ (16384 * t * V) * (C.card : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hr_le_sq hnon
      _ = 16384 * (C.card : ℝ) ^ 2 * t * V := by ring
  have hsecond :
      2048 * (C.card : ℝ) * b ^ 2 ≤
        16384 * (C.card : ℝ) ^ 2 * t * V :=
    le_trans hsecondBase hsecondGrow
  have haCoeff :
      2064 * (C.card : ℝ) ^ 2 * t * a ^ 2 ≤
        20000 * (C.card : ℝ) ^ 2 * t * a ^ 2 := by
    have hnon : 0 ≤ (C.card : ℝ) ^ 2 * t * a ^ 2 := by positivity
    nlinarith
  have hVCoeff :
      16384 * (C.card : ℝ) ^ 2 * t * V ≤
        20000 * (C.card : ℝ) ^ 2 * t * V := by
    have hnon : 0 ≤ (C.card : ℝ) ^ 2 * t * V := by positivity
    nlinarith
  have hmainScaled :
      2064 * (C.card : ℝ) ^ 3 * a ^ 2 +
          2048 * (C.card : ℝ) * b ^ 2 ≤
        ((C.card : ℝ) ^ 2) * (20000 * t * (a ^ 2 + V)) := by
    calc
      2064 * (C.card : ℝ) ^ 3 * a ^ 2 +
          2048 * (C.card : ℝ) * b ^ 2 ≤
        2064 * (C.card : ℝ) ^ 2 * t * a ^ 2 +
          16384 * (C.card : ℝ) ^ 2 * t * V := add_le_add hfirst hsecond
      _ ≤ 20000 * (C.card : ℝ) ^ 2 * t * a ^ 2 +
          20000 * (C.card : ℝ) ^ 2 * t * V := add_le_add haCoeff hVCoeff
      _ = ((C.card : ℝ) ^ 2) * (20000 * t * (a ^ 2 + V)) := by ring
  have hmul := le_trans hscaled hmainScaled
  have hrpos : 0 < (C.card : ℝ) := lt_of_lt_of_le zero_lt_one hr
  have hr2pos : 0 < (C.card : ℝ) ^ 2 := by positivity
  exact le_of_mul_le_mul_left hmul hr2pos

end IndependentMatchingBlockOccupancy
