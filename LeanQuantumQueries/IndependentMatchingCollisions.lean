import LeanQuantumQueries.IndependentMatchingMoments

open scoped BigOperators

namespace IndependentMatchingBlockOccupancy
namespace SectorData

variable {d B : ℕ} (S : SectorData d B)

/-- Indicator that two product coordinates carry the same actual block. -/
def collisionIndicatorV (i j : Fin d) : S.RawVector :=
  fun x => if S.block x i = S.block x j then 1 else 0

/-- A fixed actual block name occurs at most once in an orbit subtype. -/
theorem sum_eq_value_le_oneV (i j : Fin d)
    (a : {a : Fin B // a ∈ S.orbit i}) :
    (∑ b : {b : Fin B // b ∈ S.orbit j},
      if a.1 = b.1 then (1 : ℝ) else 0) ≤ 1 := by
  classical
  by_cases hex : ∃ b : {b : Fin B // b ∈ S.orbit j}, a.1 = b.1
  · let b0 := Classical.choose hex
    have hb0 : a.1 = b0.1 := Classical.choose_spec hex
    rw [Fintype.sum_eq_single b0]
    · simp [hb0]
    · intro b hb
      have hne : a.1 ≠ b.1 := by
        intro hab
        apply hb
        apply Subtype.ext
        exact hb0.symm.trans hab
      simp [hne]
  · have hne : ∀ b : {b : Fin B // b ∈ S.orbit j}, a.1 ≠ b.1 := by
      intro b hab
      exact hex ⟨b, hab⟩
    simp [hne]

/-- Weighted version of `sum_eq_value_le_oneV`. -/
theorem sum_eq_value_mul_leV (i j : Fin d)
    (a : {a : Fin B // a ∈ S.orbit i}) (w : ℝ) (hw : 0 ≤ w) :
    (∑ b : {b : Fin B // b ∈ S.orbit j},
      if a.1 = b.1 then w else 0) ≤ w := by
  classical
  by_cases hex : ∃ b : {b : Fin B // b ∈ S.orbit j}, a.1 = b.1
  · let b0 := Classical.choose hex
    have hb0 : a.1 = b0.1 := Classical.choose_spec hex
    rw [Fintype.sum_eq_single b0]
    · simp [hb0]
    · intro b hb
      have hne : a.1 ≠ b.1 := by
        intro hab
        apply hb
        apply Subtype.ext
        exact hb0.symm.trans hab
      simp [hne]
  · have hne : ∀ b : {b : Fin B // b ∈ S.orbit j}, a.1 ≠ b.1 := by
      intro b hab
      exact hex ⟨b, hab⟩
    simp [hne, hw]

/-- The unnormalized number of matching value-pairs is at most the size of
the first orbit. -/
theorem sum_pairCollision_le_cardV (i j : Fin d) :
    (∑ a : {a : Fin B // a ∈ S.orbit i},
      ∑ b : {b : Fin B // b ∈ S.orbit j},
        if a.1 = b.1 then (1 : ℝ) else 0) ≤
      ((S.orbit i).card : ℝ) := by
  calc
    _ ≤ ∑ _a : {a : Fin B // a ∈ S.orbit i}, (1 : ℝ) := by
      exact Finset.sum_le_sum fun a _ => S.sum_eq_value_le_oneV i j a
    _ = ((S.orbit i).card : ℝ) := by simp

/-- Collision probability times `q` is at most eight when every orbit has
size at least `q/8`. -/
theorem q_mul_rawAvg_collision_le_eightV
    (q : ℕ) (i j : Fin d) (hji : j ≠ i)
    (hlower : q ≤ 8 * (S.orbit j).card) :
    (q : ℝ) * S.rawAvg (S.collisionIndicatorV i j) ≤ 8 := by
  classical
  rw [show S.collisionIndicatorV i j =
      fun x => if (x i).1 = (x j).1 then (1 : ℝ) else 0 by rfl]
  rw [S.rawAvg_two_coordinatesV i j hji]
  have hnum := S.sum_pairCollision_le_cardV i j
  have hmi : 0 < ((S.orbit i).card : ℝ) := by
    exact_mod_cast (S.orbit_nonempty i).card_pos
  have hmj : 0 < ((S.orbit j).card : ℝ) := by
    exact_mod_cast (S.orbit_nonempty j).card_pos
  have hqj : (q : ℝ) ≤ 8 * ((S.orbit j).card : ℝ) := by
    exact_mod_cast hlower
  have hfrac :
      (∑ a, ∑ b,
        if a.1 = b.1 then (1 : ℝ) else 0) /
          (((S.orbit i).card : ℝ) * (S.orbit j).card) ≤
        1 / ((S.orbit j).card : ℝ) := by
    apply (div_le_iff₀ (mul_pos hmi hmj)).2
    field_simp [ne_of_gt hmj]
    nlinarith
  have hq0 : 0 ≤ (q : ℝ) := by positivity
  calc
    (q : ℝ) *
        ((∑ a, ∑ b,
          if a.1 = b.1 then (1 : ℝ) else 0) /
            (((S.orbit i).card : ℝ) * (S.orbit j).card)) ≤
        (q : ℝ) * (1 / ((S.orbit j).card : ℝ)) :=
      mul_le_mul_of_nonneg_left hfrac hq0
    _ ≤ 8 := by
      apply (div_le_iff₀ hmj).2
      simpa [div_eq_mul_inv] using hqj

/-- When the observed row is the first colliding coordinate, collision
conditioning costs at most the reciprocal size of the second orbit. -/
theorem q_mul_rawAvg_collision_mul_lift_sq_leftV
    (q : ℕ) (i j : Fin d) (hji : j ≠ i)
    (hlower : q ≤ 8 * (S.orbit j).card)
    (g : {a : Fin B // a ∈ S.orbit i} → ℝ) :
    (q : ℝ) * S.rawAvg (fun x =>
      S.collisionIndicatorV i j x * (S.lift i g x) ^ 2) ≤
      8 * S.coordAvg i (fun a => (g a) ^ 2) := by
  classical
  rw [show (fun x => S.collisionIndicatorV i j x *
        (S.lift i g x) ^ 2) =
      fun x => if (x i).1 = (x j).1 then (g (x i)) ^ 2 else 0 by
        funext x
        simp [collisionIndicatorV, lift, block]]
  rw [S.rawAvg_two_coordinatesV i j hji]
  have hnum :
      (∑ a, ∑ b,
        if a.1 = b.1 then (g a) ^ 2 else 0) ≤
        ∑ a, (g a) ^ 2 := by
    exact Finset.sum_le_sum fun a _ =>
      S.sum_eq_value_mul_leV i j a ((g a) ^ 2) (sq_nonneg _)
  have hmi : 0 < ((S.orbit i).card : ℝ) := by
    exact_mod_cast (S.orbit_nonempty i).card_pos
  have hmj : 0 < ((S.orbit j).card : ℝ) := by
    exact_mod_cast (S.orbit_nonempty j).card_pos
  have hqj : (q : ℝ) ≤ 8 * ((S.orbit j).card : ℝ) := by
    exact_mod_cast hlower
  unfold coordAvg
  have hsum0 : 0 ≤ ∑ a, (g a) ^ 2 :=
    Finset.sum_nonneg fun a _ => sq_nonneg _
  apply (le_div_iff₀ hmi).2
  apply (div_le_iff₀ (mul_pos hmi hmj)).2
  have hq0 : 0 ≤ (q : ℝ) := by positivity
  nlinarith

/-- Symmetric bound when the observed row is the second colliding
coordinate. -/
theorem q_mul_rawAvg_collision_mul_lift_sq_rightV
    (q : ℕ) (i j : Fin d) (hji : j ≠ i)
    (hlower : q ≤ 8 * (S.orbit i).card)
    (g : {b : Fin B // b ∈ S.orbit j} → ℝ) :
    (q : ℝ) * S.rawAvg (fun x =>
      S.collisionIndicatorV i j x * (S.lift j g x) ^ 2) ≤
      8 * S.coordAvg j (fun b => (g b) ^ 2) := by
  have hsym : S.collisionIndicatorV i j = S.collisionIndicatorV j i := by
    funext x
    simp [collisionIndicatorV, eq_comm]
  rw [hsym]
  exact S.q_mul_rawAvg_collision_mul_lift_sq_leftV
    q j i (Ne.symm hji) hlower g

/-- A collision of `i,j` is independent of the square of every third row. -/
theorem q_mul_rawAvg_collision_mul_lift_sq_otherV
    (q : ℕ) (i j k : Fin d)
    (hji : j ≠ i) (hki : k ≠ i) (hkj : k ≠ j)
    (hlower : q ≤ 8 * (S.orbit j).card)
    (g : {c : Fin B // c ∈ S.orbit k} → ℝ) :
    (q : ℝ) * S.rawAvg (fun x =>
      S.collisionIndicatorV i j x * (S.lift k g x) ^ 2) ≤
      8 * S.coordAvg k (fun c => (g c) ^ 2) := by
  classical
  rw [show (fun x => S.collisionIndicatorV i j x *
        (S.lift k g x) ^ 2) =
      fun x => (if (x i).1 = (x j).1 then 1 else 0) * (g (x k)) ^ 2 by
        funext x
        simp [collisionIndicatorV, lift, block]]
  rw [S.rawAvg_three_coordinatesV i j k hji hki hkj]
  have hfactor :
      (∑ a, ∑ b, ∑ c,
        (if a.1 = b.1 then (1 : ℝ) else 0) * (g c) ^ 2) =
      (∑ a, ∑ b, if a.1 = b.1 then (1 : ℝ) else 0) *
        ∑ c, (g c) ^ 2 := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_mul]
  rw [hfactor]
  have hpair := S.sum_pairCollision_le_cardV i j
  have hmi : 0 < ((S.orbit i).card : ℝ) := by
    exact_mod_cast (S.orbit_nonempty i).card_pos
  have hmj : 0 < ((S.orbit j).card : ℝ) := by
    exact_mod_cast (S.orbit_nonempty j).card_pos
  have hmk : 0 < ((S.orbit k).card : ℝ) := by
    exact_mod_cast (S.orbit_nonempty k).card_pos
  have hqj : (q : ℝ) ≤ 8 * ((S.orbit j).card : ℝ) := by
    exact_mod_cast hlower
  have hsum0 : 0 ≤ ∑ c, (g c) ^ 2 :=
    Finset.sum_nonneg fun c _ => sq_nonneg _
  unfold coordAvg
  apply (le_div_iff₀ hmk).2
  apply (div_le_iff₀ (mul_pos (mul_pos hmi hmj) hmk)).2
  have hq0 : 0 ≤ (q : ℝ) := by positivity
  nlinarith

end SectorData
end IndependentMatchingBlockOccupancy
