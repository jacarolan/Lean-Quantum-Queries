import LeanQuantumQueries.IndependentMatchingCollisionEnergyVerified

open scoped BigOperators

namespace IndependentMatchingBlockOccupancy
namespace SectorData

variable {d B : ℕ} (S : SectorData d B)

/-- Product-normalized energy on noninjective placements. -/
noncomputable def rawBadEnergy (f : S.RawVector) : ℝ :=
  S.rawAvg (fun x => if S.Legal x then 0 else (f x) ^ 2)

/-- Product-normalized energy on injective placements. -/
noncomputable def rawGoodEnergy (f : S.RawVector) : ℝ :=
  S.rawAvg (fun x => if S.Legal x then (f x) ^ 2 else 0)

/-- Good and bad energies are nonnegative. -/
theorem rawBadEnergy_nonneg (f : S.RawVector) :
    0 ≤ S.rawBadEnergy f := by
  unfold rawBadEnergy rawAvg
  apply div_nonneg
  · exact Finset.sum_nonneg fun x _ => by
      split_ifs <;> positivity
  · positivity

theorem rawGoodEnergy_nonneg (f : S.RawVector) :
    0 ≤ S.rawGoodEnergy f := by
  unfold rawGoodEnergy rawAvg
  apply div_nonneg
  · exact Finset.sum_nonneg fun x _ => by
      split_ifs <;> positivity
  · positivity

/-- Total product norm splits into injective and noninjective energies. -/
theorem rawNormSq_eq_good_add_bad (f : S.RawVector) :
    S.rawNormSq f = S.rawGoodEnergy f + S.rawBadEnergy f := by
  unfold rawNormSq rawInner rawGoodEnergy rawBadEnergy
  rw [← S.rawAvg_add]
  congr 1
  funext x
  by_cases hx : S.Legal x <;> simp [hx, pow_two]

/-- Every noninjective placement contains an ordered colliding pair. -/
theorem exists_collision_of_not_legal (x : S.RawPlacement)
    (hx : ¬ S.Legal x) :
    ∃ i j : Fin d, j ≠ i ∧ S.block x i = S.block x j := by
  unfold Legal at hx
  rw [Function.Injective] at hx
  push_neg at hx
  rcases hx with ⟨i, j, hij, hne⟩
  exact ⟨i, j, Ne.symm hne, hij⟩

/-- Pointwise bad energy is dominated by the ordered-pair collision sum. -/
theorem bad_pointwise_le_collision_sum (f : S.RawVector)
    (x : S.RawPlacement) :
    (if S.Legal x then 0 else (f x) ^ 2) ≤
      ∑ i, ∑ j ∈ (Finset.univ.erase i),
        S.collisionIndicatorV i j x * (f x) ^ 2 := by
  classical
  by_cases hx : S.Legal x
  · simp only [hx, ↓reduceIte]
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (by simp [collisionIndicatorV]) (sq_nonneg _)
  · simp only [hx, ↓reduceIte]
    rcases S.exists_collision_of_not_legal x hx with
      ⟨i, j, hji, hij⟩
    have hj : j ∈ (Finset.univ.erase i) := by simp [hji]
    have hterm :
        (f x) ^ 2 = S.collisionIndicatorV i j x * (f x) ^ 2 := by
      simp [collisionIndicatorV, hij]
    rw [hterm]
    have hinner :
        S.collisionIndicatorV i j x * (f x) ^ 2 ≤
          ∑ j' ∈ (Finset.univ.erase i),
            S.collisionIndicatorV i j' x * (f x) ^ 2 := by
      exact Finset.single_le_sum
        (fun j' _ => mul_nonneg
          (by simp [collisionIndicatorV]) (sq_nonneg _)) hj
    have houter :
        (∑ j' ∈ (Finset.univ.erase i),
            S.collisionIndicatorV i j' x * (f x) ^ 2) ≤
          ∑ i', ∑ j' ∈ (Finset.univ.erase i'),
            S.collisionIndicatorV i' j' x * (f x) ^ 2 := by
      exact Finset.single_le_sum
        (fun i' _ => Finset.sum_nonneg fun j' _ =>
          mul_nonneg (by simp [collisionIndicatorV]) (sq_nonneg _))
        (Finset.mem_univ i)
    exact le_trans hinner houter

/-- Product averaging commutes with the ordered-pair sum. -/
theorem rawAvg_nested_sum
    (F : Fin d → Fin d → S.RawVector) :
    S.rawAvg (fun x =>
      ∑ i, ∑ j ∈ (Finset.univ.erase i), F i j x) =
      ∑ i, ∑ j ∈ (Finset.univ.erase i), S.rawAvg (F i j) := by
  classical
  unfold rawAvg
  simp only [Finset.sum_div, Finset.sum_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]

/-- Bad energy is at most the ordered-pair collision upper energy. -/
theorem rawBadEnergy_le_collisionUpper (f : S.RawVector) :
    S.rawBadEnergy f ≤ S.rawCollisionUpper f := by
  unfold rawBadEnergy rawCollisionUpper
  calc
    S.rawAvg (fun x => if S.Legal x then 0 else (f x) ^ 2) ≤
        S.rawAvg (fun x =>
          ∑ i, ∑ j ∈ (Finset.univ.erase i),
            S.collisionIndicatorV i j x * (f x) ^ 2) :=
      S.rawAvg_mono (S.bad_pointwise_le_collision_sum f)
    _ = _ := S.rawAvg_nested_sum fun i j x =>
      S.collisionIndicatorV i j x * (f x) ^ 2

/-- Bad energy bound for every additive vector. -/
theorem rawBadEnergy_bound
    {q t : ℕ} (g : S.Coeff) (H : S.SectorNumerics q t) :
    (q : ℝ) * S.rawBadEnergy (S.synth g) ≤
      16 * (t : ℝ) ^ 3 * S.rawNormSq (S.synth g) := by
  have hbad := S.rawBadEnergy_le_collisionUpper (S.synth g)
  have hq : 0 ≤ (q : ℝ) := by positivity
  exact le_trans (mul_le_mul_of_nonneg_left hbad hq)
    (S.rawCollisionUpper_bound g H)

/-- In the large-orbit regime at least half of an additive vector's product
norm remains on injective placements. -/
theorem half_rawNormSq_le_rawGoodEnergy
    {q t : ℕ} (g : S.Coeff) (H : S.SectorNumerics q t)
    (hlarge : 32 * t ^ 3 ≤ q) :
    (1 / 2 : ℝ) * S.rawNormSq (S.synth g) ≤
      S.rawGoodEnergy (S.synth g) := by
  have hbad := S.rawBadEnergy_bound g H
  have hsplit := S.rawNormSq_eq_good_add_bad (S.synth g)
  have hqR : 32 * (t : ℝ) ^ 3 ≤ (q : ℝ) := by
    exact_mod_cast hlarge
  have hnorm : 0 ≤ S.rawNormSq (S.synth g) := by
    unfold rawNormSq rawInner rawAvg
    positivity
  have hbad0 := S.rawBadEnergy_nonneg (S.synth g)
  have hgood0 := S.rawGoodEnergy_nonneg (S.synth g)
  nlinarith

/-- Equivalent upper bound on the full product norm. -/
theorem rawNormSq_le_two_rawGoodEnergy
    {q t : ℕ} (g : S.Coeff) (H : S.SectorNumerics q t)
    (hlarge : 32 * t ^ 3 ≤ q) :
    S.rawNormSq (S.synth g) ≤
      2 * S.rawGoodEnergy (S.synth g) := by
  nlinarith [S.half_rawNormSq_le_rawGoodEnergy g H hlarge]

end SectorData
end IndependentMatchingBlockOccupancy
