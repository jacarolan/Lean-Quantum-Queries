import LeanQuantumQueries.IndependentMatchingCollisionsFinal
import LeanQuantumQueries.IndependentMatchingNumericsFinal

open scoped BigOperators

namespace IndependentMatchingBlockOccupancy
namespace SectorData

variable {d B : ℕ} (S : SectorData d B)

/-- Ordered-pair collision upper energy. -/
noncomputable def rawCollisionUpperF (f : S.RawVector) : ℝ :=
  ∑ i, ∑ j ∈ (Finset.univ.erase i),
    S.rawAvg (fun x => S.collisionIndicatorF i j x * (f x) ^ 2)

private theorem rawPlacement_nonemptyF : Nonempty S.RawPlacement := by
  classical
  refine ⟨fun i => ?_⟩
  exact ⟨(S.orbit_nonempty i).choose,
    (S.orbit_nonempty i).choose_spec⟩

private theorem rawPlacement_card_posF :
    0 < (Fintype.card S.RawPlacement : ℝ) := by
  letI := S.rawPlacement_nonemptyF
  exact_mod_cast Fintype.card_pos

/-- Monotonicity of uniform product averaging. -/
theorem rawAvg_monoF {f g : S.RawVector} (h : ∀ x, f x ≤ g x) :
    S.rawAvg f ≤ S.rawAvg g := by
  unfold rawAvg
  apply div_le_div_of_nonneg_right
  · exact Finset.sum_le_sum fun x _ => h x
  · exact (S.rawPlacement_card_posF).le

/-- Move a coordinate sum through product averaging. -/
theorem rawAvg_sumF (F : Fin d → S.RawVector) :
    S.rawAvg (∑ i, F i) = ∑ i, S.rawAvg (F i) := by
  classical
  unfold rawAvg
  simp only [Finset.sum_apply, Finset.sum_div]
  rw [Finset.sum_comm]

/-- Pointwise centered decomposition. -/
theorem synth_apply_eq_mean_add_centeredF (g : S.Coeff)
    (x : S.RawPlacement) :
    S.synth g x = S.totalMean g +
      ∑ i, S.centered i (g i) (x i) := by
  have h := congrFun (S.synth_eq_const_add_centered g) x
  simpa [constVec, lift] using h

/-- Pointwise Cauchy bound for an additive vector. -/
theorem synth_sq_le_mean_variance_sumF (g : S.Coeff)
    (x : S.RawPlacement) :
    (S.synth g x) ^ 2 ≤
      2 * (S.totalMean g) ^ 2 +
        2 * (d : ℝ) *
          ∑ i, (S.centered i (g i) (x i)) ^ 2 := by
  classical
  let z : Fin d → ℝ := fun i => S.centered i (g i) (x i)
  have hcs := Finset.sq_sum_le_card_mul_sum_sq
    (s := (Finset.univ : Finset (Fin d))) (f := z)
  have hsum : (∑ i, z i) ^ 2 ≤
      (d : ℝ) * ∑ i, (z i) ^ 2 := by
    simpa using hcs
  rw [S.synth_apply_eq_mean_add_centeredF]
  nlinarith [sq_nonneg (S.totalMean g - ∑ i, z i)]

/-- One ordered collision pair has controlled additive energy. -/
theorem q_mul_pairCollisionEnergy_leF
    {q t : ℕ} (g : S.Coeff) (H : S.SectorNumericsF q t)
    (i j : Fin d) (hji : j ≠ i) :
    (q : ℝ) * S.rawAvg (fun x =>
      S.collisionIndicatorF i j x * (S.synth g x) ^ 2) ≤
      16 * (S.totalMean g) ^ 2 +
        16 * (d : ℝ) *
          ∑ k, S.rawNormSq
            (S.lift k (S.centered k (g k))) := by
  classical
  let a := S.totalMean g
  let h : ∀ k : Fin d, {b : Fin B // b ∈ S.orbit k} → ℝ :=
    fun k => S.centered k (g k)
  let C : ℝ := S.rawAvg (S.collisionIndicatorF i j)
  let W : ℝ := ∑ k,
    S.rawAvg (fun x =>
      S.collisionIndicatorF i j x * (S.lift k (h k) x) ^ 2)
  let V : ℝ := ∑ k, S.rawNormSq (S.lift k (h k))
  have hpoint : ∀ x,
      S.collisionIndicatorF i j x * (S.synth g x) ^ 2 ≤
        S.collisionIndicatorF i j x *
          (2 * a ^ 2 + 2 * (d : ℝ) * ∑ k, (h k (x k)) ^ 2) := by
    intro x
    have hcoll : 0 ≤ S.collisionIndicatorF i j x := by
      simp [collisionIndicatorF]
    exact mul_le_mul_of_nonneg_left
      (S.synth_sq_le_mean_variance_sumF g x) hcoll
  have havg := S.rawAvg_monoF hpoint
  have hrhs :
      S.rawAvg (fun x => S.collisionIndicatorF i j x *
          (2 * a ^ 2 + 2 * (d : ℝ) * ∑ k, (h k (x k)) ^ 2)) =
        2 * a ^ 2 * C + 2 * (d : ℝ) * W := by
    have hfun :
        (fun x => S.collisionIndicatorF i j x *
          (2 * a ^ 2 + 2 * (d : ℝ) * ∑ k, (h k (x k)) ^ 2)) =
        (2 * a ^ 2) • S.collisionIndicatorF i j +
          (2 * (d : ℝ)) •
            (∑ k, fun x =>
              S.collisionIndicatorF i j x * (S.lift k (h k) x) ^ 2) := by
      funext x
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Finset.sum_apply]
      unfold lift
      ring
    rw [hfun, S.rawAvg_add, S.rawAvg_smul, S.rawAvg_smul,
      S.rawAvg_sumF]
    rfl
  rw [hrhs] at havg
  have hcoll : (q : ℝ) * C ≤ 8 :=
    S.q_mul_rawAvg_collision_le_eightF q i j hji (H.orbit_lower j)
  have hrow : ∀ k,
      (q : ℝ) * S.rawAvg (fun x =>
        S.collisionIndicatorF i j x * (S.lift k (h k) x) ^ 2) ≤
        8 * S.rawNormSq (S.lift k (h k)) := by
    intro k
    by_cases hki : k = i
    · subst k
      rw [S.rawNormSq_lift]
      exact S.q_mul_rawAvg_collision_mul_lift_sq_leftF
        q i j hji (H.orbit_lower j) (h i)
    · by_cases hkj : k = j
      · subst k
        rw [S.rawNormSq_lift]
        exact S.q_mul_rawAvg_collision_mul_lift_sq_rightF
          q i j hji (H.orbit_lower i) (h j)
      · rw [S.rawNormSq_lift]
        exact S.q_mul_rawAvg_collision_mul_lift_sq_otherF
          q i j k hji hki hkj (H.orbit_lower j) (h k)
  have hsumRow : (q : ℝ) * W ≤ 8 * V := by
    unfold W V
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => hrow k
  have hq0 : 0 ≤ (q : ℝ) := by positivity
  have ha0 : 0 ≤ 2 * a ^ 2 := by positivity
  have hd0 : 0 ≤ 2 * (d : ℝ) := by positivity
  have hmeanScaled :
      (2 * a ^ 2) * ((q : ℝ) * C) ≤ (2 * a ^ 2) * 8 :=
    mul_le_mul_of_nonneg_left hcoll ha0
  have hvarScaled :
      (2 * (d : ℝ)) * ((q : ℝ) * W) ≤
        (2 * (d : ℝ)) * (8 * V) :=
    mul_le_mul_of_nonneg_left hsumRow hd0
  calc
    (q : ℝ) * S.rawAvg (fun x =>
        S.collisionIndicatorF i j x * (S.synth g x) ^ 2) ≤
        (q : ℝ) * (2 * a ^ 2 * C + 2 * (d : ℝ) * W) :=
      mul_le_mul_of_nonneg_left havg hq0
    _ = (2 * a ^ 2) * ((q : ℝ) * C) +
        (2 * (d : ℝ)) * ((q : ℝ) * W) := by ring
    _ ≤ (2 * a ^ 2) * 8 + (2 * (d : ℝ)) * (8 * V) :=
      add_le_add hmeanScaled hvarScaled
    _ = 16 * (S.totalMean g) ^ 2 +
        16 * (d : ℝ) *
          ∑ k, S.rawNormSq
            (S.lift k (S.centered k (g k))) := by
      rfl

/-- Total collision energy of an additive product-table vector. -/
theorem rawCollisionUpperF_bound
    {q t : ℕ} (g : S.Coeff) (H : S.SectorNumericsF q t) :
    (q : ℝ) * S.rawCollisionUpperF (S.synth g) ≤
      16 * (t : ℝ) ^ 3 * S.rawNormSq (S.synth g) := by
  classical
  let a2 : ℝ := (S.totalMean g) ^ 2
  let V : ℝ := ∑ k,
    S.rawNormSq (S.lift k (S.centered k (g k)))
  let K : ℝ := 16 * a2 + 16 * (d : ℝ) * V
  have hpair : ∀ i, ∀ j ∈ (Finset.univ.erase i),
      (q : ℝ) * S.rawAvg (fun x =>
        S.collisionIndicatorF i j x * (S.synth g x) ^ 2) ≤ K := by
    intro i j hj
    exact S.q_mul_pairCollisionEnergy_leF g H i j
      (Finset.ne_of_mem_erase hj)
  unfold rawCollisionUpperF
  rw [Finset.mul_sum]
  have hone : ∀ i,
      (q : ℝ) * ∑ j ∈ (Finset.univ.erase i),
          S.rawAvg (fun x =>
            S.collisionIndicatorF i j x * (S.synth g x) ^ 2) ≤
        (d : ℝ) * K := by
    intro i
    rw [Finset.mul_sum]
    calc
      ∑ j ∈ (Finset.univ.erase i),
          (q : ℝ) * S.rawAvg (fun x =>
            S.collisionIndicatorF i j x * (S.synth g x) ^ 2) ≤
          ∑ j ∈ (Finset.univ.erase i), K :=
        Finset.sum_le_sum fun j hj => hpair i j hj
      _ = ((Finset.univ.erase i).card : ℝ) * K := by
        simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (d : ℝ) * K := by
        have hc : (Finset.univ.erase i).card ≤ d := by simp
        have hcR : ((Finset.univ.erase i).card : ℝ) ≤ (d : ℝ) := by
          exact_mod_cast hc
        have hK : 0 ≤ K := by
          unfold K a2 V
          positivity
        exact mul_le_mul_of_nonneg_right hcR hK
  have hsum :
      (∑ i, (q : ℝ) * ∑ j ∈ (Finset.univ.erase i),
        S.rawAvg (fun x =>
          S.collisionIndicatorF i j x * (S.synth g x) ^ 2)) ≤
        (d : ℝ) ^ 2 * K := by
    calc
      _ ≤ ∑ _i : Fin d, (d : ℝ) * K :=
        Finset.sum_le_sum fun i _ => hone i
      _ = (d : ℝ) ^ 2 * K := by
        simp [Finset.sum_const, nsmul_eq_mul, pow_two]
        ring
  have hd : (d : ℝ) ≤ (t : ℝ) := by exact_mod_cast H.coord_le
  have ht : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast H.t_pos
  have hd0 : 0 ≤ (d : ℝ) := by positivity
  have ht0 : 0 ≤ (t : ℝ) := by positivity
  have hd2 : (d : ℝ) ^ 2 ≤ (t : ℝ) ^ 2 := by
    have hprod : 0 ≤ ((t : ℝ) - d) * ((t : ℝ) + d) :=
      mul_nonneg (sub_nonneg.mpr hd) (add_nonneg ht0 hd0)
    nlinarith
  have hd3 : (d : ℝ) ^ 3 ≤ (t : ℝ) ^ 3 := by
    have hpoly : 0 ≤ (t : ℝ) ^ 2 + (t : ℝ) * d + (d : ℝ) ^ 2 := by
      positivity
    have hprod : 0 ≤ ((t : ℝ) - d) *
        ((t : ℝ) ^ 2 + (t : ℝ) * d + (d : ℝ) ^ 2) :=
      mul_nonneg (sub_nonneg.mpr hd) hpoly
    nlinarith
  have ht2t3 : (t : ℝ) ^ 2 ≤ (t : ℝ) ^ 3 := by
    have hprod : 0 ≤ (t : ℝ) ^ 2 * ((t : ℝ) - 1) :=
      mul_nonneg (sq_nonneg _) (sub_nonneg.mpr ht)
    nlinarith
  have ha0 : 0 ≤ a2 := by unfold a2; positivity
  have hV0 : 0 ≤ V := by
    unfold V
    apply Finset.sum_nonneg
    intro k _
    rw [S.rawNormSq_lift]
    unfold coordAvg
    positivity
  have hda2 : (d : ℝ) ^ 2 * a2 ≤ (t : ℝ) ^ 3 * a2 :=
    le_trans (mul_le_mul_of_nonneg_right hd2 ha0)
      (mul_le_mul_of_nonneg_right ht2t3 ha0)
  have hdV : (d : ℝ) ^ 3 * V ≤ (t : ℝ) ^ 3 * V :=
    mul_le_mul_of_nonneg_right hd3 hV0
  have hKV :
      (d : ℝ) ^ 2 * K ≤
        16 * (t : ℝ) ^ 3 * (a2 + V) := by
    unfold K
    calc
      (d : ℝ) ^ 2 *
          (16 * a2 + 16 * (d : ℝ) * V) =
          16 * ((d : ℝ) ^ 2 * a2) +
            16 * ((d : ℝ) ^ 3 * V) := by ring
      _ ≤ 16 * ((t : ℝ) ^ 3 * a2) +
            16 * ((t : ℝ) ^ 3 * V) :=
        add_le_add
          (mul_le_mul_of_nonneg_left hda2 (by norm_num))
          (mul_le_mul_of_nonneg_left hdV (by norm_num))
      _ = 16 * (t : ℝ) ^ 3 * (a2 + V) := by ring
  have hmeanvar := S.rawNormSq_synth g
  calc
    _ ≤ (d : ℝ) ^ 2 * K := hsum
    _ ≤ 16 * (t : ℝ) ^ 3 * (a2 + V) := hKV
    _ = 16 * (t : ℝ) ^ 3 * S.rawNormSq (S.synth g) := by
      unfold a2 V
      rw [hmeanvar]

end SectorData
end IndependentMatchingBlockOccupancy
