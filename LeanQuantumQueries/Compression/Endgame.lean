import Mathlib

namespace LeanQuantumQueries.Compression

open Real
open scoped BigOperators

/-- Cauchy--Schwarz for a sum with at most three summands. -/
theorem sq_sum_le_three_mul_sum_sq
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℝ) (hs : s.card ≤ 3) :
    (∑ i ∈ s, f i) ^ 2 ≤ 3 * ∑ i ∈ s, (f i) ^ 2 := by
  calc
    (∑ i ∈ s, f i) ^ 2
        ≤ (s.card : ℝ) * ∑ i ∈ s, (f i) ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    _ ≤ 3 * ∑ i ∈ s, (f i) ^ 2 := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast hs
      · exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- If each output coordinate receives at most three level contributions,
then the squared Euclidean norm of the sum is at most three times the sum of
the squared norms.  This is the scalar core of the three-band argument. -/
theorem three_sparse_sum_bound
    {κ ι : Type*} [Fintype κ] [DecidableEq κ] [DecidableEq ι]
    (support : κ → Finset ι) (f : κ → ι → ℝ)
    (hcard : ∀ k, (support k).card ≤ 3) :
    ∑ k, (∑ i ∈ support k, f k i) ^ 2
      ≤ 3 * ∑ k, ∑ i ∈ support k, (f k i) ^ 2 := by
  calc
    ∑ k, (∑ i ∈ support k, f k i) ^ 2
        ≤ ∑ k, 3 * ∑ i ∈ support k, (f k i) ^ 2 := by
      gcongr with k
      exact sq_sum_le_three_mul_sum_sq (support k) (f k) (hcard k)
    _ = 3 * ∑ k, ∑ i ∈ support k, (f k i) ^ 2 := by
      simp [Finset.mul_sum]

/-- The final numerical step in the repaired compression theorem: a squared
operator-norm estimate with constant `972` implies the displayed constant `32`.
-/
theorem compression_constant
    (N t opNorm : ℝ)
    (hNt : 0 < N - t)
    (hOp : 0 ≤ opNorm)
    (hSq : opNorm ^ 2 ≤ 972 / (N - t)) :
    opNorm ≤ 32 / Real.sqrt (N - t) := by
  have hsqrt_pos : 0 < Real.sqrt (N - t) := Real.sqrt_pos.2 hNt
  have hsqrt_sq : (Real.sqrt (N - t)) ^ 2 = N - t := by
    simpa using Real.sq_sqrt (le_of_lt hNt)
  have hmul : opNorm ^ 2 * (N - t) ≤ 972 := by
    exact (le_div_iff₀ hNt).mp hSq
  have htarget_sq : (opNorm * Real.sqrt (N - t)) ^ 2 ≤ (32 : ℝ) ^ 2 := by
    rw [mul_pow, hsqrt_sq]
    nlinarith
  have htarget_nonneg : 0 ≤ opNorm * Real.sqrt (N - t) :=
    mul_nonneg hOp (le_of_lt hsqrt_pos)
  have htarget : opNorm * Real.sqrt (N - t) ≤ 32 := by
    nlinarith
  exact (le_div_iff₀ hsqrt_pos).2 (by simpa [mul_comm] using htarget)

/-- The checked endgame of the compression theorem.  `inputSq r` is the
squared norm of the level-`r` input, `outputSq r` is the squared norm of its
image, `hlevel` is the one-level `324/(N-t)` estimate, and `hband` is the
three-band overlap estimate. -/
theorem compression_from_one_level_bounds
    {ι : Type*} [Fintype ι]
    (N t opNorm : ℝ) (inputSq outputSq : ι → ℝ)
    (hNt : 0 < N - t)
    (hOp : 0 ≤ opNorm)
    (hInput : ∑ r, inputSq r ≤ 1)
    (hLevel : ∀ r, outputSq r ≤ (324 / (N - t)) * inputSq r)
    (hBand : opNorm ^ 2 ≤ 3 * ∑ r, outputSq r) :
    opNorm ≤ 32 / Real.sqrt (N - t) := by
  have hsum : ∑ r, outputSq r ≤ (324 / (N - t)) * ∑ r, inputSq r := by
    calc
      ∑ r, outputSq r
          ≤ ∑ r, (324 / (N - t)) * inputSq r := by
        gcongr with r
        exact hLevel r
      _ = (324 / (N - t)) * ∑ r, inputSq r := by
        simp [Finset.mul_sum]
  have hcoef : 0 ≤ 324 / (N - t) := by positivity
  have hsum' : ∑ r, outputSq r ≤ 324 / (N - t) := by
    calc
      ∑ r, outputSq r
          ≤ (324 / (N - t)) * ∑ r, inputSq r := hsum
      _ ≤ (324 / (N - t)) * 1 :=
        mul_le_mul_of_nonneg_left hInput hcoef
      _ = 324 / (N - t) := by ring
  have hSq : opNorm ^ 2 ≤ 972 / (N - t) := by
    calc
      opNorm ^ 2 ≤ 3 * ∑ r, outputSq r := hBand
      _ ≤ 3 * (324 / (N - t)) := by gcongr
      _ = 972 / (N - t) := by ring
  exact compression_constant N t opNorm hNt hOp hSq

/-- A sequence satisfying `δ (k+1) ≤ δ k + c` grows by at most `q*c` in
`q` steps. -/
theorem recurrence_bound
    (δ : ℕ → ℝ) (c : ℝ) (q : ℕ)
    (h0 : δ 0 ≤ 0)
    (hstep : ∀ k < q, δ (k + 1) ≤ δ k + c) :
    δ q ≤ q * c := by
  induction q with
  | zero => simpa using h0
  | succ q ih =>
      have hq : δ (q + 1) ≤ δ q + c := hstep q (Nat.lt_succ_self q)
      have ih' : δ q ≤ q * c :=
        ih (fun k hk => hstep k (Nat.lt_trans hk (Nat.lt_succ_self q)))
      calc
        δ (q + 1) ≤ δ q + c := hq
        _ ≤ q * c + c := by gcongr
        _ = ((q : ℝ) + 1) * c := by ring
        _ = ((q + 1 : ℕ) : ℝ) * c := by rw [Nat.cast_succ]

/-- The arithmetic conclusion used after the acceptance-gap estimate. -/
theorem query_lower_bound_arithmetic
    (N q : ℝ) (_hN : 0 < N)
    (hgap : Real.sqrt N ≤ 384 * Real.sqrt 2 * q) :
    Real.sqrt N / (384 * Real.sqrt 2) ≤ q := by
  have hden : 0 < 384 * Real.sqrt 2 := by positivity
  exact (div_le_iff₀ hden).2
    (by simpa [mul_assoc, mul_comm, mul_left_comm] using hgap)

end LeanQuantumQueries.Compression
