import LeanQuantumQueries.IndependentMatchingCollisions
import LeanQuantumQueries.IndependentMatchingNumerics

open scoped BigOperators

namespace IndependentMatchingBlockOccupancy
namespace SectorData

variable {d B : ℕ} (S : SectorData d B)

/-- Ordered-pair collision upper energy. -/
noncomputable def rawCollisionUpper (f : S.RawVector) : ℝ :=
  ∑ i, ∑ j ∈ (Finset.univ.erase i),
    S.rawAvg (fun x => S.collisionIndicatorV i j x * (f x) ^ 2)

private theorem rawPlacement_nonemptyC : Nonempty S.RawPlacement := by
  classical
  refine ⟨fun i => ?_⟩
  exact ⟨(S.orbit_nonempty i).choose,
    (S.orbit_nonempty i).choose_spec⟩

private theorem rawPlacement_card_posC :
    0 < (Fintype.card S.RawPlacement : ℝ) := by
  letI := S.rawPlacement_nonemptyC
  exact_mod_cast Fintype.card_pos

/-- Monotonicity of uniform product averaging. -/
theorem rawAvg_mono {f g : S.RawVector} (h : ∀ x, f x ≤ g x) :
    S.rawAvg f ≤ S.rawAvg g := by
  unfold rawAvg
  apply div_le_div_of_nonneg_right
  · exact Finset.sum_le_sum fun x _ => h x
  · exact (S.rawPlacement_card_posC).le

/-- A finite coordinate sum can be moved through product averaging. -/
theorem rawAvg_sum (F : Fin d → S.RawVector) :
    S.rawAvg (∑ i, F i) = ∑ i, S.rawAvg (F i) := by
  classical
  unfold rawAvg
  simp only [Finset.sum_apply, Finset.sum_div]
  rw [Finset.sum_comm]

/-- Pointwise centered decomposition. -/
theorem synth_apply_eq_mean_add_centered (g : S.Coeff)
    (x : S.RawPlacement) :
    S.synth g x = S.totalMean g +
      ∑ i, S.centered i (g i) (x i) := by
  have h := congrFun (S.synth_eq_const_add_centered g) x
  simpa [constVec, lift] using h

/-- Pointwise Cauchy estimate for an additive vector. -/
theorem synth_sq_le_mean_variance_sum (g : S.Coeff)
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
  rw [S.synth_apply_eq_mean_add_centered]
  nlinarith [sq_nonneg (S.totalMean g - ∑ i, z i)]

/-- One ordered collision pair has controlled additive energy. -/
theorem q_mul_pairCollisionEnergy_le
    {q t : ℕ} (g : S.Coeff) (H : S.SectorNumerics q t)
    (i j : Fin d) (hji : j ≠ i) :
    (q : ℝ) * S.rawAvg (fun x =>
      S.collisionIndicatorV i j x * (S.synth g x) ^ 2) ≤
      16 * (S.totalMean g) ^ 2 +
        16 * (d : ℝ) *
          ∑ k, S.rawNormSq
            (S.lift k (S.centered k (g k))) := by
  classical
  let a := S.totalMean g
  let h : ∀ k : Fin d, {b : Fin B // b ∈ S.orbit k} → ℝ :=
    fun k => S.centered k (g k)
  have hpoint : ∀ x,
      S.collisionIndicatorV i j x * (S.synth g x) ^ 2 ≤
        S.collisionIndicatorV i j x *
          (2 * a ^ 2 + 2 * (d : ℝ) * ∑ k, (h k (x k)) ^ 2) := by
    intro x
    have hcoll : 0 ≤ S.collisionIndicatorV i j x := by
      simp [collisionIndicatorV]
    exact mul_le_mul_of_nonneg_left
      (S.synth_sq_le_mean_variance_sum g x) hcoll
  have havg := S.rawAvg_mono hpoint
  have hrhs :
      S.rawAvg (fun x => S.collisionIndicatorV i j x *
          (2 * a ^ 2 + 2 * (d : ℝ) * ∑ k, (h k (x k)) ^ 2)) =
        2 * a ^ 2 * S.rawAvg (S.collisionIndicatorV i j) +
          2 * (d : ℝ) * ∑ k,
            S.rawAvg (fun x =>
              S.collisionIndicatorV i j x * (S.lift k (h k) x) ^ 2) := by
    have hfun :
        (fun x => S.collisionIndicatorV i j x *
          (2 * a ^ 2 + 2 * (d : ℝ) * ∑ k, (h k (x k)) ^ 2)) =
        (2 * a ^ 2) • S.collisionIndicatorV i j +
          (2 * (d : ℝ)) •
            (∑ k, fun x =>
              S.collisionIndicatorV i j x * (S.lift k (h k) x) ^ 2) := by
      funext x
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Finset.sum_apply]
      unfold lift
      ring
    rw [hfun, S.rawAvg_add, S.rawAvg_smul, S.rawAvg_smul,
      S.rawAvg_sum]
    ring
  rw [hrhs] at havg
  have hcoll := S.q_mul_rawAvg_collision_le_eightV
    q i j hji (H.orbit_lower j)
  have hrow : ∀ k,
      (q : ℝ) * S.rawAvg (fun x =>
        S.collisionIndicatorV i j x * (S.lift k (h k) x) ^ 2) ≤
        8 * S.rawNormSq (S.lift k (h k)) := by
    intro k
    by_cases hki : k = i
    · subst k
      rw [S.rawNormSq_lift]
      exact S.q_mul_rawAvg_collision_mul_lift_sq_leftV
        q i j hji (H.orbit_lower j) (h i)
    · by_cases hkj : k = j
      · subst k
        rw [S.rawNormSq_lift]
        exact S.q_mul_rawAvg_collision_mul_lift_sq_rightV
          q i j hji (H.orbit_lower i) (h j)
      · rw [S.rawNormSq_lift]
        exact S.q_mul_rawAvg_collision_mul_lift_sq_otherV
          q i j k hji hki hkj (H.orbit_lower j) (h k)
  have hsumRow :
      (q : ℝ) * ∑ k,
          S.rawAvg (fun x =>
            S.collisionIndicatorV i j x * (S.lift k (h k) x) ^ 2) ≤
        8 * ∑ k, S.rawNormSq (S.lift k (h k)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => hrow k
  have hq0 : 0 ≤ (q : ℝ) := by positivity
  have hscaled := mul_le_mul_of_nonneg_left havg hq0
  have ha0 : 0 ≤ a ^ 2 := sq_nonneg _
  have hd0 : 0 ≤ (d : ℝ) := by positivity
  have hrow0 : 0 ≤ ∑ k, S.rawNormSq (S.lift k (h k)) := by
    apply Finset.sum_nonneg
    intro k _
    rw [S.rawNormSq_lift]
    unfold coordAvg
    positivity
  nlinarith

/-- Collision energy of any additive product-table vector. -/
theorem rawCollisionUpper_bound
    {q t : ℕ} (g : S.Coeff) (H : S.SectorNumerics q t) :
    (q : ℝ) * S.rawCollisionUpper (S.synth g) ≤
      16 * (t : ℝ) ^ 3 * S.rawNormSq (S.synth g) := by
  classical
  let K : ℝ := 16 * (S.totalMean g) ^ 2 +
    16 * (d : ℝ) *
      ∑ k, S.rawNormSq (S.lift k (S.centered k (g k)))
  have hpair : ∀ i, ∀ j ∈ (Finset.univ.erase i),
      (q : ℝ) * S.rawAvg (fun x =>
        S.collisionIndicatorV i j x * (S.synth g x) ^ 2) ≤ K := by
    intro i j hj
    exact S.q_mul_pairCollisionEnergy_le g H i j
      (Finset.ne_of_mem_erase hj)
  unfold rawCollisionUpper
  rw [Finset.mul_sum]
  have hone : ∀ i,
      (q : ℝ) * ∑ j ∈ (Finset.univ.erase i),
          S.rawAvg (fun x =>
            S.collisionIndicatorV i j x * (S.synth g x) ^ 2) ≤
        (d : ℝ) * K := by
    intro i
    rw [Finset.mul_sum]
    calc
      ∑ j ∈ (Finset.univ.erase i),
          (q : ℝ) * S.rawAvg (fun x =>
            S.collisionIndicatorV i j x * (S.synth g x) ^ 2) ≤
          ∑ j ∈ (Finset.univ.erase i), K :=
        Finset.sum_le_sum fun j hj => hpair i j hj
      _ = ((Finset.univ.erase i).card : ℝ) * K := by
        simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (d : ℝ) * K := by
        have hc : (Finset.univ.erase i).card ≤ d := by
          simp
        have hcR : ((Finset.univ.erase i).card : ℝ) ≤ (d : ℝ) := by
          exact_mod_cast hc
        have hK : 0 ≤ K := by
          unfold K
          positivity
        exact mul_le_mul_of_nonneg_right hcR hK
  have hsum :
      (∑ i, (q : ℝ) * ∑ j ∈ (Finset.univ.erase i),
        S.rawAvg (fun x =>
          S.collisionIndicatorV i j x * (S.synth g x) ^ 2)) ≤
        (d : ℝ) ^ 2 * K := by
    calc
      _ ≤ ∑ i : Fin d, (d : ℝ) * K :=
        Finset.sum_le_sum fun i _ => hone i
      _ = (d : ℝ) ^ 2 * K := by
        simp [Finset.sum_const, nsmul_eq_mul, pow_two]
        ring
  have hd : (d : ℝ) ≤ (t : ℝ) := by
    exact_mod_cast H.coord_le
  have ht : (1 : ℝ) ≤ (t : ℝ) := by
    exact_mod_cast H.t_pos
  have hmeanvar := S.rawNormSq_synth g
  have hvar0 : 0 ≤ ∑ k,
      S.rawNormSq (S.lift k (S.centered k (g k))) := by
    apply Finset.sum_nonneg
    intro k _
    rw [S.rawNormSq_lift]
    unfold coordAvg
    positivity
  have ha0 : 0 ≤ (S.totalMean g) ^ 2 := sq_nonneg _
  have ht0 : 0 ≤ (t : ℝ) := by positivity
  calc
    _ ≤ (d : ℝ) ^ 2 * K := hsum
    _ ≤ 16 * (t : ℝ) ^ 3 *
        ((S.totalMean g) ^ 2 +
          ∑ k, S.rawNormSq
            (S.lift k (S.centered k (g k)))) := by
      unfold K
      nlinarith
    _ = 16 * (t : ℝ) ^ 3 * S.rawNormSq (S.synth g) := by
      rw [hmeanvar]

end SectorData
end IndependentMatchingBlockOccupancy
