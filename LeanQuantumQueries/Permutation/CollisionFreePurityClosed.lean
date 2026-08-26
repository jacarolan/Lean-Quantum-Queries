import LeanQuantumQueries.Permutation.CollisionFreePurityFormula

/-!
# Exact collision-free purity

The scalar `collisionFreePurity N q` is the purity of the collision-free
`q`-query moment state.  This file proves the closed formula

  q! * overlapFactor q / (N.descFactorial q)^2.
-/

namespace LeanQuantumQueries.Permutation
namespace PartialPerm

open scoped BigOperators

variable {N q : ℕ}

/-- Cancel the fresh-subset factor against the corresponding part of a longer
descending factorial. -/
theorem choose_div_descFactorial_add
    {a : ℕ} (hqN : q ≤ N) (ha : a ≤ N - q) :
    (Nat.choose (N - q) a : ℚ) /
        (N.descFactorial (q + a) : ℚ) =
      1 /
        ((Nat.factorial a : ℚ) *
          (N.descFactorial q : ℚ)) := by
  have hqa : q ≤ q + a := by omega
  have hprodNat :
      (N - q).descFactorial a * N.descFactorial q =
        N.descFactorial (q + a) := by
    simpa using
      (Nat.descFactorial_mul_descFactorial
        (n := N) (k := q) (m := q + a) hqa)
  have hfreshNat :
      (N - q).descFactorial a =
        Nat.factorial a * Nat.choose (N - q) a :=
    Nat.descFactorial_eq_factorial_mul_choose _ _
  have hprodRat :
      ((N - q).descFactorial a : ℚ) *
          (N.descFactorial q : ℚ) =
        (N.descFactorial (q + a) : ℚ) := by
    exact_mod_cast hprodNat
  have hfreshRat :
      ((N - q).descFactorial a : ℚ) =
        (Nat.factorial a : ℚ) *
          (Nat.choose (N - q) a : ℚ) := by
    exact_mod_cast hfreshNat
  have hchoose : (Nat.choose (N - q) a : ℚ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero ha
  have hfac : (Nat.factorial a : ℚ) ≠ 0 := by positivity
  have hdesc : (N.descFactorial q : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt ((Nat.descFactorial_pos).2 hqN)
  rw [← hprodRat, hfreshRat]
  field_simp [hchoose, hfac, hdesc]

/-- After cancellation, every kernel row is the same multiple of
`overlapFactor q`. -/
theorem sum_collisionKernel_row_eq
    (S : QSubset N q) (h2qN : 2 * q ≤ N) :
    ∑ T : QSubset N q, collisionKernel S T =
      overlapFactor q / (N.descFactorial q : ℚ) := by
  rw [sum_collisionKernel_row_grouped]
  rw [overlapFactor, Finset.sum_div]
  apply Fintype.sum_congr
  intro j
  have hjq : j.1 ≤ q := Nat.le_of_lt_succ j.2
  have hqN : q ≤ N := by omega
  have ha : q - j.1 ≤ N - q := by omega
  calc
    (Nat.choose q j.1 : ℚ) *
          Nat.choose (N - q) (q - j.1) /
        (N.descFactorial (q + (q - j.1)) : ℚ) =
      (Nat.choose q j.1 : ℚ) *
        ((Nat.choose (N - q) (q - j.1) : ℚ) /
          (N.descFactorial (q + (q - j.1)) : ℚ)) := by ring
    _ = (Nat.choose q j.1 : ℚ) *
        (1 / ((Nat.factorial (q - j.1) : ℚ) *
          (N.descFactorial q : ℚ))) := by
      rw [choose_div_descFactorial_add hqN ha]
    _ = ((Nat.choose q j.1 : ℚ) /
          Nat.factorial (q - j.1)) /
        (N.descFactorial q : ℚ) := by ring

/-- The normalized double kernel sum, i.e. the purity of the collision-free
random-permutation moment. -/
noncomputable def collisionFreePurity (N q : ℕ) : ℚ :=
  (∑ S : QSubset N q, ∑ T : QSubset N q, collisionKernel S T) /
    (Nat.choose N q : ℚ) ^ 2

/-- Exact purity formula. -/
theorem collisionFreePurity_eq
    (h2qN : 2 * q ≤ N) :
    collisionFreePurity N q =
      (Nat.factorial q : ℚ) * overlapFactor q /
        (N.descFactorial q : ℚ) ^ 2 := by
  have hqN : q ≤ N := by omega
  have hchooseNat : Nat.choose N q ≠ 0 := Nat.choose_ne_zero hqN
  have hchoose : (Nat.choose N q : ℚ) ≠ 0 := by
    exact_mod_cast hchooseNat
  have hfac : (Nat.factorial q : ℚ) ≠ 0 := by positivity
  have hdescNat :
      N.descFactorial q = Nat.factorial q * Nat.choose N q :=
    Nat.descFactorial_eq_factorial_mul_choose _ _
  have hdesc :
      (N.descFactorial q : ℚ) =
        (Nat.factorial q : ℚ) * (Nat.choose N q : ℚ) := by
    exact_mod_cast hdescNat
  rw [collisionFreePurity]
  simp_rw [sum_collisionKernel_row_eq (h2qN := h2qN)]
  rw [Finset.sum_const, Finset.card_univ, card_qSubset]
  simp only [nsmul_eq_mul]
  rw [hdesc]
  field_simp [hchoose, hfac]
  ring

end PartialPerm
end LeanQuantumQueries.Permutation
