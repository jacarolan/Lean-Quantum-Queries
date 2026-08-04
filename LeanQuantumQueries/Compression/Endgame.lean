import Mathlib

namespace LeanQuantumQueries.Compression

open Real

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
  have hsqrt_ne : Real.sqrt (N - t) ≠ 0 := ne_of_gt hsqrt_pos
  have hsqrt_sq : (Real.sqrt (N - t)) ^ 2 = N - t := by
    simpa using Real.sq_sqrt (le_of_lt hNt)
  have hmul : opNorm ^ 2 * (N - t) ≤ 972 := by
    apply (le_div_iff₀ hNt).mp
    simpa [mul_comm] using hSq
  have htarget_sq : (opNorm * Real.sqrt (N - t)) ^ 2 ≤ (32 : ℝ) ^ 2 := by
    rw [mul_pow, hsqrt_sq]
    nlinarith
  have htarget_nonneg : 0 ≤ opNorm * Real.sqrt (N - t) :=
    mul_nonneg hOp (le_of_lt hsqrt_pos)
  have htarget : opNorm * Real.sqrt (N - t) ≤ 32 := by
    nlinarith
  exact (le_div_iff₀ hsqrt_pos).2 (by simpa [mul_comm] using htarget)

end LeanQuantumQueries.Compression
