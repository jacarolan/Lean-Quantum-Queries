import LeanQuantumQueries.IndependentMatchingMomentsFinal

open scoped BigOperators

namespace IndependentMatchingBlockOccupancy
namespace SectorData

variable {d B : ℕ} (S : SectorData d B)

/-- Indicator that two raw coordinates carry the same actual block. -/
def collisionIndicatorF (i j : Fin d) : S.RawVector :=
  fun x => if S.block x i = S.block x j then 1 else 0

/-- For a fixed value in one orbit there is at most one equal value in another
orbit subtype. -/
theorem sum_eq_value_le_oneF (i j : Fin d)
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
        exact Subtype.ext (hb0.symm.trans hab)
      simp [hne]
  · have hne : ∀ b : {b : Fin B // b ∈ S.orbit j}, a.1 ≠ b.1 := by
      intro b hab
      exact hex ⟨b, hab⟩
    simp [hne]

/-- Weighted uniqueness form. -/
theorem sum_eq_value_mul_leF (i j : Fin d)
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
        exact Subtype.ext (hb0.symm.trans hab)
      simp [hne]
  · have hne : ∀ b : {b : Fin B // b ∈ S.orbit j}, a.1 ≠ b.1 := by
      intro b hab
      exact hex ⟨b, hab⟩
    simp [hne, hw]

/-- Number of equal-value pairs is at most the first orbit size. -/
theorem sum_pairCollision_le_cardF (i j : Fin d) :
    (∑ a : {a : Fin B // a ∈ S.orbit i},
      ∑ b : {b : Fin B // b ∈ S.orbit j},
        if a.1 = b.1 then (1 : ℝ) else 0) ≤
      ((S.orbit i).card : ℝ) := by
  calc
    _ ≤ ∑ _a : {a : Fin B // a ∈ S.orbit i}, (1 : ℝ) := by
      exact Finset.sum_le_sum fun a _ => S.sum_eq_value_le_oneF i j a
    _ = ((S.orbit i).card : ℝ) := by simp

private theorem fraction_pair_boundF
    {q mi mj num : ℝ}
    (hmi : 0 < mi) (hmj : 0 < mj)
    (hq : 0 ≤ q) (hqj : q ≤ 8 * mj)
    (hnum0 : 0 ≤ num) (hnum : num ≤ mi) :
    q * (num / (mi * mj)) ≤ 8 := by
  rw [show q * (num / (mi * mj)) = (q * num) / (mi * mj) by ring]
  apply (div_le_iff₀ (mul_pos hmi hmj)).2
  have h1 : q * num ≤ (8 * mj) * num :=
    mul_le_mul_of_nonneg_right hqj hnum0
  have h2 : (8 * mj) * num ≤ (8 * mj) * mi :=
    mul_le_mul_of_nonneg_left hnum (mul_nonneg (by norm_num) hmj.le)
  calc
    q * num ≤ (8 * mj) * mi := le_trans h1 h2
    _ = 8 * (mi * mj) := by ring

private theorem fraction_weight_boundF
    {q mi mj num total : ℝ}
    (hmi : 0 < mi) (hmj : 0 < mj)
    (hq : 0 ≤ q) (hqj : q ≤ 8 * mj)
    (hnum0 : 0 ≤ num) (htotal0 : 0 ≤ total)
    (hnum : num ≤ total) :
    q * (num / (mi * mj)) ≤ 8 * (total / mi) := by
  rw [show q * (num / (mi * mj)) = (q * num) / (mi * mj) by ring]
  apply (div_le_iff₀ (mul_pos hmi hmj)).2
  have h1 : q * num ≤ (8 * mj) * num :=
    mul_le_mul_of_nonneg_right hqj hnum0
  have h2 : (8 * mj) * num ≤ (8 * mj) * total :=
    mul_le_mul_of_nonneg_left hnum (mul_nonneg (by norm_num) hmj.le)
  calc
    q * num ≤ (8 * mj) * total := le_trans h1 h2
    _ = (8 * (total / mi)) * (mi * mj) := by
      field_simp [ne_of_gt hmi]
      ring

/-- Collision probability times the orbit-scale parameter is at most eight. -/
theorem q_mul_rawAvg_collision_le_eightF
    (q : ℕ) (i j : Fin d) (hji : j ≠ i)
    (hlower : q ≤ 8 * (S.orbit j).card) :
    (q : ℝ) * S.rawAvg (S.collisionIndicatorF i j) ≤ 8 := by
  classical
  rw [show S.collisionIndicatorF i j =
      fun x => if (x i).1 = (x j).1 then (1 : ℝ) else 0 by rfl]
  rw [S.rawAvg_two_coordinatesF i j hji]
  have hmi : 0 < ((S.orbit i).card : ℝ) := by
    exact_mod_cast (S.orbit_nonempty i).card_pos
  have hmj : 0 < ((S.orbit j).card : ℝ) := by
    exact_mod_cast (S.orbit_nonempty j).card_pos
  have hqj : (q : ℝ) ≤ 8 * ((S.orbit j).card : ℝ) := by
    exact_mod_cast hlower
  have hnum := S.sum_pairCollision_le_cardF i j
  have hnum0 : 0 ≤
      (∑ a, ∑ b,
        if a.1 = b.1 then (1 : ℝ) else 0) := by
    positivity
  exact fraction_pair_boundF hmi hmj (by positivity) hqj hnum0 hnum

/-- Collision conditioning when the squared row is coordinate `i`. -/
theorem q_mul_rawAvg_collision_mul_lift_sq_leftF
    (q : ℕ) (i j : Fin d) (hji : j ≠ i)
    (hlower : q ≤ 8 * (S.orbit j).card)
    (g : {a : Fin B // a ∈ S.orbit i} → ℝ) :
    (q : ℝ) * S.rawAvg (fun x =>
      S.collisionIndicatorF i j x * (S.lift i g x) ^ 2) ≤
      8 * S.coordAvg i (fun a => (g a) ^ 2) := by
  classical
  rw [show (fun x => S.collisionIndicatorF i j x *
        (S.lift i g x) ^ 2) =
      fun x => if (x i).1 = (x j).1 then (g (x i)) ^ 2 else 0 by
        funext x
        simp [collisionIndicatorF, lift, block]]
  rw [S.rawAvg_two_coordinatesF i j hji]
  have hnum :
      (∑ a, ∑ b,
        if a.1 = b.1 then (g a) ^ 2 else 0) ≤
        ∑ a, (g a) ^ 2 := by
    exact Finset.sum_le_sum fun a _ =>
      S.sum_eq_value_mul_leF i j a ((g a) ^ 2) (sq_nonneg _)
  have hnum0 : 0 ≤
      (∑ a, ∑ b,
        if a.1 = b.1 then (g a) ^ 2 else 0) := by
    positivity
  have htotal0 : 0 ≤ ∑ a, (g a) ^ 2 := by positivity
  have hmi : 0 < ((S.orbit i).card : ℝ) := by
    exact_mod_cast (S.orbit_nonempty i).card_pos
  have hmj : 0 < ((S.orbit j).card : ℝ) := by
    exact_mod_cast (S.orbit_nonempty j).card_pos
  have hqj : (q : ℝ) ≤ 8 * ((S.orbit j).card : ℝ) := by
    exact_mod_cast hlower
  unfold coordAvg
  exact fraction_weight_boundF hmi hmj (by positivity) hqj
    hnum0 htotal0 hnum

/-- Symmetric row bound. -/
theorem q_mul_rawAvg_collision_mul_lift_sq_rightF
    (q : ℕ) (i j : Fin d) (hji : j ≠ i)
    (hlower : q ≤ 8 * (S.orbit i).card)
    (g : {b : Fin B // b ∈ S.orbit j} → ℝ) :
    (q : ℝ) * S.rawAvg (fun x =>
      S.collisionIndicatorF i j x * (S.lift j g x) ^ 2) ≤
      8 * S.coordAvg j (fun b => (g b) ^ 2) := by
  have hsym : S.collisionIndicatorF i j = S.collisionIndicatorF j i := by
    funext x
    simp [collisionIndicatorF, eq_comm]
  rw [hsym]
  exact S.q_mul_rawAvg_collision_mul_lift_sq_leftF
    q j i (Ne.symm hji) hlower g

/-- Collision of `i,j` is independent of a third squared row. -/
theorem q_mul_rawAvg_collision_mul_lift_sq_otherF
    (q : ℕ) (i j k : Fin d)
    (hji : j ≠ i) (hki : k ≠ i) (hkj : k ≠ j)
    (hlower : q ≤ 8 * (S.orbit j).card)
    (g : {c : Fin B // c ∈ S.orbit k} → ℝ) :
    (q : ℝ) * S.rawAvg (fun x =>
      S.collisionIndicatorF i j x * (S.lift k g x) ^ 2) ≤
      8 * S.coordAvg k (fun c => (g c) ^ 2) := by
  classical
  rw [show (fun x => S.collisionIndicatorF i j x *
        (S.lift k g x) ^ 2) =
      fun x => (if (x i).1 = (x j).1 then 1 else 0) * (g (x k)) ^ 2 by
        funext x
        simp [collisionIndicatorF, lift, block]]
  rw [S.rawAvg_three_coordinatesF i j k hji hki hkj]
  have hfactor :
      (∑ a, ∑ b, ∑ c,
        (if a.1 = b.1 then (1 : ℝ) else 0) * (g c) ^ 2) =
      (∑ a, ∑ b, if a.1 = b.1 then (1 : ℝ) else 0) *
        ∑ c, (g c) ^ 2 := by
    calc
      _ = ∑ a, ∑ b,
          (if a.1 = b.1 then (1 : ℝ) else 0) *
            ∑ c, (g c) ^ 2 := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        rw [Finset.mul_sum]
      _ = _ := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.sum_mul]
  rw [hfactor]
  let pair : ℝ :=
    ∑ a, ∑ b, if a.1 = b.1 then (1 : ℝ) else 0
  let total : ℝ := ∑ c, (g c) ^ 2
  have hpair : pair ≤ ((S.orbit i).card : ℝ) :=
    S.sum_pairCollision_le_cardF i j
  have hpair0 : 0 ≤ pair := by
    unfold pair
    positivity
  have htotal0 : 0 ≤ total := by
    unfold total
    positivity
  have hmi : 0 < ((S.orbit i).card : ℝ) := by
    exact_mod_cast (S.orbit_nonempty i).card_pos
  have hmj : 0 < ((S.orbit j).card : ℝ) := by
    exact_mod_cast (S.orbit_nonempty j).card_pos
  have hmk : 0 < ((S.orbit k).card : ℝ) := by
    exact_mod_cast (S.orbit_nonempty k).card_pos
  have hqj : (q : ℝ) ≤ 8 * ((S.orbit j).card : ℝ) := by
    exact_mod_cast hlower
  unfold coordAvg
  change (q : ℝ) *
      ((pair * total) /
        (((S.orbit i).card : ℝ) * (S.orbit j).card *
          (S.orbit k).card)) ≤
    8 * (total / ((S.orbit k).card : ℝ))
  rw [show
      (q : ℝ) *
        ((pair * total) /
          (((S.orbit i).card : ℝ) * (S.orbit j).card *
            (S.orbit k).card)) =
      (((q : ℝ) * pair) * total) /
        (((S.orbit i).card : ℝ) * (S.orbit j).card *
          (S.orbit k).card) by ring]
  apply (div_le_iff₀ (mul_pos (mul_pos hmi hmj) hmk)).2
  have hqp : (q : ℝ) * pair ≤
      8 * ((S.orbit j).card : ℝ) * ((S.orbit i).card : ℝ) := by
    have h1 : (q : ℝ) * pair ≤
        (8 * ((S.orbit j).card : ℝ)) * pair :=
      mul_le_mul_of_nonneg_right hqj hpair0
    have h2 :
        (8 * ((S.orbit j).card : ℝ)) * pair ≤
        (8 * ((S.orbit j).card : ℝ)) * ((S.orbit i).card : ℝ) :=
      mul_le_mul_of_nonneg_left hpair
        (mul_nonneg (by norm_num) hmj.le)
    exact le_trans h1 h2
  have hqpt := mul_le_mul_of_nonneg_right hqp htotal0
  calc
    ((q : ℝ) * pair) * total ≤
        (8 * ((S.orbit j).card : ℝ) * ((S.orbit i).card : ℝ)) * total := hqpt
    _ = (8 * (total / ((S.orbit k).card : ℝ))) *
        (((S.orbit i).card : ℝ) * (S.orbit j).card *
          (S.orbit k).card) := by
      field_simp [ne_of_gt hmk]
      ring

end SectorData
end IndependentMatchingBlockOccupancy
