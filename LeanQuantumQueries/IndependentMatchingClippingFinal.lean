import LeanQuantumQueries.IndependentMatchingCollisionEnergyFinal

open scoped BigOperators

namespace IndependentMatchingBlockOccupancy
namespace SectorData

variable {d B : ℕ} (S : SectorData d B)

/-- Product-normalized energy on noninjective placements. -/
noncomputable def rawBadEnergyF (f : S.RawVector) : ℝ :=
  S.rawAvg (fun x => if S.Legal x then 0 else (f x) ^ 2)

/-- Product-normalized energy on injective placements. -/
noncomputable def rawGoodEnergyF (f : S.RawVector) : ℝ :=
  S.rawAvg (fun x => if S.Legal x then (f x) ^ 2 else 0)

/-- Good and bad energies are nonnegative. -/
theorem rawBadEnergyF_nonneg (f : S.RawVector) :
    0 ≤ S.rawBadEnergyF f := by
  unfold rawBadEnergyF rawAvg
  apply div_nonneg
  · exact Finset.sum_nonneg fun x _ => by
      split_ifs <;> positivity
  · positivity

theorem rawGoodEnergyF_nonneg (f : S.RawVector) :
    0 ≤ S.rawGoodEnergyF f := by
  unfold rawGoodEnergyF rawAvg
  apply div_nonneg
  · exact Finset.sum_nonneg fun x _ => by
      split_ifs <;> positivity
  · positivity

/-- Total raw norm splits into good and bad energy. -/
theorem rawNormSq_eq_good_add_badF (f : S.RawVector) :
    S.rawNormSq f = S.rawGoodEnergyF f + S.rawBadEnergyF f := by
  unfold rawNormSq rawInner rawGoodEnergyF rawBadEnergyF
  rw [← S.rawAvg_add]
  congr 1
  funext x
  by_cases hx : S.Legal x <;> simp [hx, pow_two]

/-- A noninjective placement contains two distinct equal block coordinates. -/
theorem exists_collision_of_not_legalF (x : S.RawPlacement)
    (hx : ¬ S.Legal x) :
    ∃ i j : Fin d, j ≠ i ∧ S.block x i = S.block x j := by
  unfold Legal at hx
  rw [Function.Injective] at hx
  push_neg at hx
  rcases hx with ⟨i, j, hij, hne⟩
  exact ⟨i, j, Ne.symm hne, hij⟩

/-- Pointwise bad energy is dominated by the ordered-pair collision sum. -/
theorem bad_pointwise_le_collision_sumF (f : S.RawVector)
    (x : S.RawPlacement) :
    (if S.Legal x then 0 else (f x) ^ 2) ≤
      ∑ i, ∑ j ∈ (Finset.univ.erase i),
        S.collisionIndicatorF i j x * (f x) ^ 2 := by
  classical
  by_cases hx : S.Legal x
  · simp only [hx, ↓reduceIte]
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (by simp [collisionIndicatorF]) (sq_nonneg _)
  · simp only [hx, ↓reduceIte]
    rcases S.exists_collision_of_not_legalF x hx with
      ⟨i, j, hji, hij⟩
    have hj : j ∈ (Finset.univ.erase i) := by simp [hji]
    have hterm :
        (f x) ^ 2 = S.collisionIndicatorF i j x * (f x) ^ 2 := by
      simp [collisionIndicatorF, hij]
    rw [hterm]
    have hinner :
        S.collisionIndicatorF i j x * (f x) ^ 2 ≤
          ∑ j' ∈ (Finset.univ.erase i),
            S.collisionIndicatorF i j' x * (f x) ^ 2 := by
      exact Finset.single_le_sum
        (fun j' _ => mul_nonneg
          (by simp [collisionIndicatorF]) (sq_nonneg _)) hj
    have houter :
        (∑ j' ∈ (Finset.univ.erase i),
            S.collisionIndicatorF i j' x * (f x) ^ 2) ≤
          ∑ i', ∑ j' ∈ (Finset.univ.erase i'),
            S.collisionIndicatorF i' j' x * (f x) ^ 2 := by
      exact Finset.single_le_sum
        (fun i' _ => Finset.sum_nonneg fun j' _ =>
          mul_nonneg (by simp [collisionIndicatorF]) (sq_nonneg _))
        (Finset.mem_univ i)
    exact le_trans hinner houter

/-- Move the ordered-pair sum through product averaging. -/
theorem rawAvg_nested_sumF
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

/-- Bad energy is at most collision upper energy. -/
theorem rawBadEnergyF_le_collisionUpper (f : S.RawVector) :
    S.rawBadEnergyF f ≤ S.rawCollisionUpperF f := by
  unfold rawBadEnergyF rawCollisionUpperF
  calc
    S.rawAvg (fun x => if S.Legal x then 0 else (f x) ^ 2) ≤
        S.rawAvg (fun x =>
          ∑ i, ∑ j ∈ (Finset.univ.erase i),
            S.collisionIndicatorF i j x * (f x) ^ 2) :=
      S.rawAvg_monoF (S.bad_pointwise_le_collision_sumF f)
    _ = _ := S.rawAvg_nested_sumF fun i j x =>
      S.collisionIndicatorF i j x * (f x) ^ 2

/-- Bad energy bound for additive vectors. -/
theorem rawBadEnergyF_bound
    {q t : ℕ} (g : S.Coeff) (H : S.SectorNumericsF q t) :
    (q : ℝ) * S.rawBadEnergyF (S.synth g) ≤
      16 * (t : ℝ) ^ 3 * S.rawNormSq (S.synth g) := by
  have hbad := S.rawBadEnergyF_le_collisionUpper (S.synth g)
  have hq : 0 ≤ (q : ℝ) := by positivity
  exact le_trans (mul_le_mul_of_nonneg_left hbad hq)
    (S.rawCollisionUpperF_bound g H)

/-- In the large-orbit regime at least half of the raw norm survives
injectivity clipping. -/
theorem half_rawNormSq_le_rawGoodEnergyF
    {q t : ℕ} (g : S.Coeff) (H : S.SectorNumericsF q t)
    (hlarge : 32 * t ^ 3 ≤ q) :
    (1 / 2 : ℝ) * S.rawNormSq (S.synth g) ≤
      S.rawGoodEnergyF (S.synth g) := by
  let A := S.rawNormSq (S.synth g)
  let B := S.rawBadEnergyF (S.synth g)
  let G := S.rawGoodEnergyF (S.synth g)
  have hbad : (q : ℝ) * B ≤ 16 * (t : ℝ) ^ 3 * A :=
    S.rawBadEnergyF_bound g H
  have hsplit : A = G + B := S.rawNormSq_eq_good_add_badF (S.synth g)
  have hlargeR : 32 * (t : ℝ) ^ 3 ≤ (q : ℝ) := by
    exact_mod_cast hlarge
  have ht : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast H.t_pos
  have hqpos : 0 < (q : ℝ) := by
    have ht3 : 0 < (t : ℝ) ^ 3 := by positivity
    nlinarith
  have hA : 0 ≤ A := by
    unfold A rawNormSq rawInner rawAvg
    positivity
  have hB : 0 ≤ B := S.rawBadEnergyF_nonneg _
  have hG : 0 ≤ G := S.rawGoodEnergyF_nonneg _
  have hscale :
      16 * (t : ℝ) ^ 3 * A ≤
        ((q : ℝ) / 2) * A := by
    exact mul_le_mul_of_nonneg_right
      (by nlinarith [hlargeR]) hA
  have hqB : (q : ℝ) * B ≤ (q : ℝ) * (A / 2) := by
    calc
      (q : ℝ) * B ≤ 16 * (t : ℝ) ^ 3 * A := hbad
      _ ≤ ((q : ℝ) / 2) * A := hscale
      _ = (q : ℝ) * (A / 2) := by ring
  have hBhalf : B ≤ A / 2 :=
    (mul_le_mul_left hqpos).mp hqB
  unfold A G at hsplit ⊢
  nlinarith

/-- Equivalent near-isometry bound. -/
theorem rawNormSq_le_two_rawGoodEnergyF
    {q t : ℕ} (g : S.Coeff) (H : S.SectorNumericsF q t)
    (hlarge : 32 * t ^ 3 ≤ q) :
    S.rawNormSq (S.synth g) ≤
      2 * S.rawGoodEnergyF (S.synth g) := by
  nlinarith [S.half_rawNormSq_le_rawGoodEnergyF g H hlarge]

end SectorData
end IndependentMatchingBlockOccupancy
