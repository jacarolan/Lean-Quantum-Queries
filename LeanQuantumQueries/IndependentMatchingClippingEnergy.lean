import LeanQuantumQueries.IndependentMatchingCollisionEnergy

open scoped BigOperators

namespace IndependentMatchingBlockOccupancy
namespace SectorData

variable {d B : ℕ} (S : SectorData d B)

/-- Product-normalized squared energy on noninjective placements. -/
noncomputable def rawBadEnergyV (f : S.RawVector) : ℝ :=
  S.rawAvg (fun x => if S.Legal x then 0 else (f x) ^ 2)

/-- Product-normalized squared energy on injective placements. -/
noncomputable def rawGoodEnergyV (f : S.RawVector) : ℝ :=
  S.rawAvg (fun x => if S.Legal x then (f x) ^ 2 else 0)

/-- Bad and good energies are nonnegative. -/
theorem rawBadEnergyV_nonneg (f : S.RawVector) :
    0 ≤ S.rawBadEnergyV f := by
  unfold rawBadEnergyV rawAvg
  exact div_nonneg
    (Finset.sum_nonneg fun x _ => by
      split_ifs <;> positivity)
    (by positivity)

 theorem rawGoodEnergyV_nonneg (f : S.RawVector) :
    0 ≤ S.rawGoodEnergyV f := by
  unfold rawGoodEnergyV rawAvg
  exact div_nonneg
    (Finset.sum_nonneg fun x _ => by
      split_ifs <;> positivity)
    (by positivity)

/-- Total product norm splits into legal and collision energies. -/
theorem rawNormSq_eq_good_add_badV (f : S.RawVector) :
    S.rawNormSq f = S.rawGoodEnergyV f + S.rawBadEnergyV f := by
  unfold rawNormSq rawInner rawGoodEnergyV rawBadEnergyV
  rw [← S.rawAvg_add]
  congr 1
  funext x
  by_cases hx : S.Legal x <;> simp [hx, pow_two]

/-- A noninjective placement supplies two distinct coordinates carrying the
same block. -/
theorem exists_collision_of_not_legalV (x : S.RawPlacement)
    (hx : ¬ S.Legal x) :
    ∃ i j : Fin d, j ≠ i ∧ S.block x i = S.block x j := by
  unfold Legal at hx
  rw [Function.Injective] at hx
  push_neg at hx
  rcases hx with ⟨i, j, hij, hne⟩
  exact ⟨i, j, Ne.symm hne, hij⟩

/-- Pointwise bad energy is dominated by the ordered-pair collision sum. -/
theorem bad_pointwise_le_collision_sumV (f : S.RawVector)
    (x : S.RawPlacement) :
    (if S.Legal x then 0 else (f x) ^ 2) ≤
      ∑ i, ∑ j ∈ (Finset.univ.erase i),
        S.collisionIndicatorV i j x * (f x) ^ 2 := by
  classical
  by_cases hx : S.Legal x
  · simp [hx]
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (by simp [collisionIndicatorV]) (sq_nonneg _)
  · simp only [hx, ↓reduceIte]
    rcases S.exists_collision_of_not_legalV x hx with ⟨i, j, hji, hij⟩
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

/-- Product averaging commutes with a nested finite sum. -/
theorem rawAvg_nested_sumV
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
theorem rawBadEnergyV_le_collisionUpper (f : S.RawVector) :
    S.rawBadEnergyV f ≤ S.rawCollisionUpperV f := by
  unfold rawBadEnergyV rawCollisionUpperV
  calc
    S.rawAvg (fun x => if S.Legal x then 0 else (f x) ^ 2) ≤
        S.rawAvg (fun x =>
          ∑ i, ∑ j ∈ (Finset.univ.erase i),
            S.collisionIndicatorV i j x * (f x) ^ 2) :=
      S.rawAvg_monoV (S.bad_pointwise_le_collision_sumV f)
    _ = _ := S.rawAvg_nested_sumV fun i j x =>
      S.collisionIndicatorV i j x * (f x) ^ 2

/-- Collision energy bound for an additive vector. -/
theorem rawBadEnergyV_bound
    {q t : ℕ} (g : S.Coeff) (H : S.SectorNumericsV q t) :
    (q : ℝ) * S.rawBadEnergyV (S.synth g) ≤
      16 * (t : ℝ) ^ 3 * S.rawNormSq (S.synth g) := by
  have hbad := S.rawBadEnergyV_le_collisionUpper (S.synth g)
  have hq : 0 ≤ (q : ℝ) := by positivity
  exact le_trans (mul_le_mul_of_nonneg_left hbad hq)
    (S.rawCollisionUpperV_bound g H)

/-- In the large-orbit regime at least half of an additive vector's product
norm remains on injective placements. -/
theorem half_rawNormSq_le_rawGoodEnergyV
    {q t : ℕ} (g : S.Coeff) (H : S.SectorNumericsV q t)
    (hlarge : 32 * t ^ 3 ≤ q) :
    (1 / 2 : ℝ) * S.rawNormSq (S.synth g) ≤
      S.rawGoodEnergyV (S.synth g) := by
  have hbad := S.rawBadEnergyV_bound g H
  have hsplit := S.rawNormSq_eq_good_add_badV (S.synth g)
  have hqR : 32 * (t : ℝ) ^ 3 ≤ (q : ℝ) := by
    exact_mod_cast hlarge
  have ht : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast H.t_pos
  have hnorm : 0 ≤ S.rawNormSq (S.synth g) := by
    unfold rawNormSq rawInner rawAvg
    positivity
  have hbad0 := S.rawBadEnergyV_nonneg (S.synth g)
  have hgood0 := S.rawGoodEnergyV_nonneg (S.synth g)
  nlinarith

/-- Equivalent upper bound on the full product norm. -/
theorem rawNormSq_le_two_rawGoodEnergyV
    {q t : ℕ} (g : S.Coeff) (H : S.SectorNumericsV q t)
    (hlarge : 32 * t ^ 3 ≤ q) :
    S.rawNormSq (S.synth g) ≤
      2 * S.rawGoodEnergyV (S.synth g) := by
  nlinarith [S.half_rawNormSq_le_rawGoodEnergyV g H hlarge]

end SectorData
end IndependentMatchingBlockOccupancy
