import LeanQuantumQueries.Permutation.CollisionFreePurityClosed
import Mathlib.Data.Nat.Choose.Sum

/-!
# Exponential bound on the residual overlap factor

The exact collision-free purity contains

  overlapFactor q = ∑_{j=0}^q q.choose j / (q-j)!.

The elementary estimate `2^a ≤ 2 a!` gives

  overlapFactor q ≤ 2 * 3^q / 2^q.

Together with the standard central-binomial lower bound, this is enough for a
polynomial-query distinguisher.
-/

namespace LeanQuantumQueries.Permutation
namespace PartialPerm

open scoped BigOperators

/-- The elementary factorial bound used term by term. -/
theorem pow_two_le_two_mul_factorial :
    ∀ a : ℕ, 2 ^ a ≤ 2 * Nat.factorial a := by
  intro a
  induction a with
  | zero => norm_num
  | succ a ih =>
      cases a with
      | zero => norm_num
      | succ b =>
          rw [pow_succ, Nat.factorial_succ]
          calc
            2 ^ (b + 1) * 2 ≤
                (2 * Nat.factorial (b + 1)) * 2 :=
              Nat.mul_le_mul_right 2 ih
            _ ≤ 2 * ((b + 2) * Nat.factorial (b + 1)) := by
              have hfac := Nat.factorial_pos (b + 1)
              nlinarith

/-- Termwise comparison with the binomial expansion of `3^q`. -/
theorem overlapTerm_le
    (q j : ℕ) (hj : j ≤ q) :
    (Nat.choose q j : ℚ) / Nat.factorial (q - j) ≤
      2 * (Nat.choose q j : ℚ) * (2 : ℚ) ^ j /
        (2 : ℚ) ^ q := by
  let a := q - j
  have hpowNat : 2 ^ a ≤ 2 * Nat.factorial a :=
    pow_two_le_two_mul_factorial a
  have hpow : (2 : ℚ) ^ a ≤ 2 * (Nat.factorial a : ℚ) := by
    exact_mod_cast hpowNat
  have hfacpos : (0 : ℚ) < Nat.factorial a := by positivity
  have hpowpos : (0 : ℚ) < (2 : ℚ) ^ a := by positivity
  have hinv :
      1 / (Nat.factorial a : ℚ) ≤ 2 / (2 : ℚ) ^ a := by
    apply (div_le_div_iff₀ hfacpos hpowpos).2
    simpa using hpow
  have hchoose : (0 : ℚ) ≤ Nat.choose q j := by positivity
  calc
    (Nat.choose q j : ℚ) / Nat.factorial (q - j) =
        (Nat.choose q j : ℚ) *
          (1 / (Nat.factorial a : ℚ)) := by
      simp [a]
      ring
    _ ≤ (Nat.choose q j : ℚ) *
          (2 / (2 : ℚ) ^ a) :=
      mul_le_mul_of_nonneg_left hinv hchoose
    _ = 2 * (Nat.choose q j : ℚ) * (2 : ℚ) ^ j /
          (2 : ℚ) ^ q := by
      have hadd : a + j = q := by
        simp [a, Nat.sub_add_cancel hj]
      have hpa : (2 : ℚ) ^ a ≠ 0 := by positivity
      have hpj : (2 : ℚ) ^ j ≠ 0 := by positivity
      rw [← hadd, pow_add]
      field_simp [hpa, hpj]
      ring

/-- The binomial sum needed after applying the termwise estimate. -/
theorem sum_choose_mul_two_pow (q : ℕ) :
    (∑ j : Fin (q + 1),
        (Nat.choose q j.1 : ℚ) * (2 : ℚ) ^ j.1) =
      (3 : ℚ) ^ q := by
  have h := (add_pow (2 : ℚ) 1 q).symm
  simpa [← Fin.sum_univ_eq_sum_range, mul_comm, mul_left_comm, mul_assoc] using h

/-- Exponential upper bound on the residual factor in the exact purity. -/
theorem overlapFactor_le (q : ℕ) :
    overlapFactor q ≤
      2 * (3 : ℚ) ^ q / (2 : ℚ) ^ q := by
  rw [overlapFactor]
  calc
    (∑ j : Fin (q + 1),
        (Nat.choose q j.1 : ℚ) /
          Nat.factorial (q - j.1)) ≤
      ∑ j : Fin (q + 1),
        2 * (Nat.choose q j.1 : ℚ) * (2 : ℚ) ^ j.1 /
          (2 : ℚ) ^ q := by
        apply Finset.sum_le_sum
        intro j _
        exact overlapTerm_le q j.1 (Nat.le_of_lt_succ j.2)
    _ = (2 / (2 : ℚ) ^ q) *
          ∑ j : Fin (q + 1),
            (Nat.choose q j.1 : ℚ) * (2 : ℚ) ^ j.1 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
    _ = 2 * (3 : ℚ) ^ q / (2 : ℚ) ^ q := by
        rw [sum_choose_mul_two_pow]
        ring

/-- The overlap factor is strictly positive. -/
theorem overlapFactor_pos (q : ℕ) : 0 < overlapFactor q := by
  rw [overlapFactor]
  let jq : Fin (q + 1) := ⟨q, Nat.lt_succ_self q⟩
  have hterm :
      (0 : ℚ) <
        (Nat.choose q jq.1 : ℚ) /
          Nat.factorial (q - jq.1) := by
    simp [jq]
  have hle :
      (Nat.choose q jq.1 : ℚ) /
          Nat.factorial (q - jq.1) ≤
        ∑ j : Fin (q + 1),
          (Nat.choose q j.1 : ℚ) /
            Nat.factorial (q - j.1) := by
    exact Finset.single_le_sum
      (f := fun j : Fin (q + 1) =>
        (Nat.choose q j.1 : ℚ) /
          Nat.factorial (q - j.1))
      (fun j _ => by positivity)
      (Finset.mem_univ jq)
  exact hterm.trans_le hle

end PartialPerm
end LeanQuantumQueries.Permutation
