import Mathlib

namespace LeanQuantumQueries.Compression

open scoped BigOperators

/-- The squared norm of a sum of at most three vectors is at most three times
the sum of their squared norms. -/
theorem norm_sum_sq_le_three_mul_sum_norm_sq
    {ι E : Type*} [DecidableEq ι] [NormedAddCommGroup E]
    (s : Finset ι) (f : ι → E) (hs : s.card ≤ 3) :
    ‖∑ i ∈ s, f i‖ ^ 2 ≤ 3 * ∑ i ∈ s, ‖f i‖ ^ 2 := by
  have htriangle : ‖∑ i ∈ s, f i‖ ≤ ∑ i ∈ s, ‖f i‖ :=
    norm_sum_le _ _
  have hleft : 0 ≤ ‖∑ i ∈ s, f i‖ := norm_nonneg _
  have hright : 0 ≤ ∑ i ∈ s, ‖f i‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hsquare : ‖∑ i ∈ s, f i‖ ^ 2 ≤ (∑ i ∈ s, ‖f i‖) ^ 2 := by
    nlinarith
  calc
    ‖∑ i ∈ s, f i‖ ^ 2
        ≤ (∑ i ∈ s, ‖f i‖) ^ 2 := hsquare
    _ ≤ (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    _ ≤ 3 * ∑ i ∈ s, ‖f i‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast hs
      · exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Vector-valued version of the three-band estimate.  The fiber type may
depend on the output coordinate. -/
theorem three_sparse_norm_sum_bound
    {κ ι : Type*} [Fintype κ] [DecidableEq κ] [DecidableEq ι]
    (E : κ → Type*) [∀ k, NormedAddCommGroup (E k)]
    (support : κ → Finset ι) (f : ∀ k, ι → E k)
    (hcard : ∀ k, (support k).card ≤ 3) :
    ∑ k, ‖∑ i ∈ support k, f k i‖ ^ 2
      ≤ 3 * ∑ k, ∑ i ∈ support k, ‖f k i‖ ^ 2 := by
  calc
    ∑ k, ‖∑ i ∈ support k, f k i‖ ^ 2
        ≤ ∑ k, 3 * ∑ i ∈ support k, ‖f k i‖ ^ 2 := by
      gcongr with k
      exact norm_sum_sq_le_three_mul_sum_norm_sq
        (support k) (f k) (hcard k)
    _ = 3 * ∑ k, ∑ i ∈ support k, ‖f k i‖ ^ 2 := by
      simp [Finset.mul_sum]

/-- Combining the three-band overlap estimate with an aggregate one-level
bound.  This is the direct-sum Hilbert-space endgame before taking square
roots. -/
theorem three_band_from_aggregate_level_bound
    {κ ι : Type*} [Fintype κ] [DecidableEq κ] [DecidableEq ι]
    (E : κ → Type*) [∀ k, NormedAddCommGroup (E k)]
    (support : κ → Finset ι) (f : ∀ k, ι → E k)
    (hcard : ∀ k, (support k).card ≤ 3)
    (c inputNormSq : ℝ)
    (haggregate : ∑ k, ∑ i ∈ support k, ‖f k i‖ ^ 2 ≤ c * inputNormSq) :
    ∑ k, ‖∑ i ∈ support k, f k i‖ ^ 2
      ≤ 3 * c * inputNormSq := by
  calc
    ∑ k, ‖∑ i ∈ support k, f k i‖ ^ 2
        ≤ 3 * ∑ k, ∑ i ∈ support k, ‖f k i‖ ^ 2 :=
      three_sparse_norm_sum_bound E support f hcard
    _ ≤ 3 * (c * inputNormSq) := by gcongr
    _ = 3 * c * inputNormSq := by ring

end LeanQuantumQueries.Compression
