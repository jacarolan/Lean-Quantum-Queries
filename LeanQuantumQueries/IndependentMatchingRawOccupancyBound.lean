import LeanQuantumQueries.IndependentMatchingRawOccupancy

open scoped BigOperators

namespace IndependentMatchingBlockOccupancy
namespace SectorData

variable {d B : ℕ} (S : SectorData d B)

/-- Product-table overlap of the occupancy count with one centered row. -/
noncomputable def rawCountCenteredSq {u : Fin B} (c : S.OutsideCoeff u)
    (j : Fin d) : ℝ :=
  S.rawAvg fun x => S.rawOccupancyCount u x * (S.centeredLift c j x) ^ 2

/-- The occupancy-count moment is the sum of its coordinate-cylinder moments. -/
theorem rawCountCenteredSq_eq_sum {u : Fin B} (c : S.OutsideCoeff u)
    (j : Fin d) :
    S.rawCountCenteredSq c j = ∑ i, S.rawAtCenteredSq c i j := by
  classical
  unfold rawCountCenteredSq rawOccupancyCount rawAtCenteredSq
  rw [show (fun x => (∑ i, S.rawAtU u i) x *
      (S.centeredLift c j x) ^ 2) =
      ∑ i, (fun x => S.rawAtU u i x * (S.centeredLift c j x) ^ 2) by
        funext x
        simp only [Finset.sum_apply, Finset.sum_mul]]
  exact S.rawAvg_sum _

/-- Pointwise mean-plus-centered decomposition. -/
theorem synth_apply_eq_mean_add_centered {u : Fin B}
    (c : S.OutsideCoeff u) (x : S.RawPlacement) :
    S.synth c.val x = S.totalMean c.val + ∑ i, S.centeredLift c i x := by
  have h := congrFun (S.synth_eq_const_add_centered c.val) x
  simpa [constVec, centeredLift] using h

/-- The square of an additive product-table vector is bounded by its constant
part and the sum of its centered row squares. -/
theorem synth_sq_le_mean_add_centered {u : Fin B}
    (c : S.OutsideCoeff u) (x : S.RawPlacement) :
    (S.synth c.val x) ^ 2 ≤
      2 * (S.totalMean c.val) ^ 2 +
        2 * (d : ℝ) * ∑ i, (S.centeredLift c i x) ^ 2 := by
  classical
  let z : ℝ := ∑ i, S.centeredLift c i x
  let W : ℝ := ∑ i, (S.centeredLift c i x) ^ 2
  have hcs : z ^ 2 ≤ (d : ℝ) * W := by
    have h := sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset (Fin d)))
      (f := fun i => S.centeredLift c i x)
    simpa [z, W, Fintype.card_fin] using h
  have hdec : S.synth c.val x = S.totalMean c.val + z := by
    simpa [z] using S.synth_apply_eq_mean_add_centered c x
  rw [hdec]
  nlinarith [sq_nonneg (S.totalMean c.val - z)]

/-- Raw occupied energy is controlled by a constant part and the centered-row
occupancy moments. -/
theorem rawOccupiedEnergy_synth_le_decomposition {u : Fin B}
    (c : S.OutsideCoeff u) :
    S.rawOccupiedEnergy u (S.synth c.val) ≤
      2 * (S.totalMean c.val) ^ 2 * S.rawAvg (S.rawOccupancyCount u) +
        2 * (d : ℝ) * ∑ j, S.rawCountCenteredSq c j := by
  classical
  have hfirstAvg :
      S.rawAvg (fun x =>
        2 * (S.totalMean c.val) ^ 2 * S.rawOccupancyCount u x) =
        2 * (S.totalMean c.val) ^ 2 *
          S.rawAvg (S.rawOccupancyCount u) := by
    rw [show (fun x =>
        2 * (S.totalMean c.val) ^ 2 * S.rawOccupancyCount u x) =
      (2 * (S.totalMean c.val) ^ 2) • S.rawOccupancyCount u by
        funext x
        rfl]
    rw [S.rawAvg_smul]
  have hsecondAvg :
      S.rawAvg (fun x =>
        2 * (d : ℝ) * ∑ j,
          S.rawOccupancyCount u x * (S.centeredLift c j x) ^ 2) =
        2 * (d : ℝ) * ∑ j, S.rawCountCenteredSq c j := by
    rw [show (fun x =>
        2 * (d : ℝ) * ∑ j,
          S.rawOccupancyCount u x * (S.centeredLift c j x) ^ 2) =
      (2 * (d : ℝ)) •
        ∑ j, (fun x =>
          S.rawOccupancyCount u x * (S.centeredLift c j x) ^ 2) by
        funext x
        simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply]]
    rw [S.rawAvg_smul, S.rawAvg_sum]
    rfl
  calc
    S.rawOccupiedEnergy u (S.synth c.val) ≤
        S.rawAvg (fun x => S.rawOccupancyCount u x *
          (S.synth c.val x) ^ 2) :=
      S.rawOccupiedEnergy_le_count u (S.synth c.val)
    _ ≤ S.rawAvg (fun x =>
        2 * (S.totalMean c.val) ^ 2 * S.rawOccupancyCount u x +
          2 * (d : ℝ) * ∑ j,
            S.rawOccupancyCount u x * (S.centeredLift c j x) ^ 2) := by
      apply S.rawAvg_mono
      intro x
      have hsq := S.synth_sq_le_mean_add_centered c x
      have hc := S.rawOccupancyCount_nonneg u x
      have hmul := mul_le_mul_of_nonneg_left hsq hc
      calc
        S.rawOccupancyCount u x * (S.synth c.val x) ^ 2 ≤
            S.rawOccupancyCount u x *
              (2 * (S.totalMean c.val) ^ 2 +
                2 * (d : ℝ) * ∑ j, (S.centeredLift c j x) ^ 2) := hmul
        _ = 2 * (S.totalMean c.val) ^ 2 * S.rawOccupancyCount u x +
            2 * (d : ℝ) * ∑ j,
              S.rawOccupancyCount u x * (S.centeredLift c j x) ^ 2 := by
          rw [← Finset.mul_sum]
          ring
    _ = 2 * (S.totalMean c.val) ^ 2 * S.rawAvg (S.rawOccupancyCount u) +
        2 * (d : ℝ) * ∑ j, S.rawCountCenteredSq c j := by
      rw [show (fun x =>
          2 * (S.totalMean c.val) ^ 2 * S.rawOccupancyCount u x +
            2 * (d : ℝ) * ∑ j,
              S.rawOccupancyCount u x * (S.centeredLift c j x) ^ 2) =
        (fun x => 2 * (S.totalMean c.val) ^ 2 *
          S.rawOccupancyCount u x) +
        (fun x => 2 * (d : ℝ) * ∑ j,
          S.rawOccupancyCount u x * (S.centeredLift c j x) ^ 2) by
          rfl]
      rw [S.rawAvg_add, hfirstAvg, hsecondAvg]

/-- One diagonal cylinder moment is controlled by the complete-family mean
term plus a universal multiple of the corresponding row variance. -/
theorem q_mul_rawAtCenteredSq_self_le {q t : ℕ} {u : Fin B}
    (c : S.OutsideCoeff u) (H : S.SectorBounds q t)
    (hgapU : ∀ i, ¬ S.Complete i →
      (S.orbit i).card ≤ 8 * (S.missingValues u i).card)
    (i : Fin d) :
    (q : ℝ) * S.rawAtCenteredSq c i i ≤
      (if i ∈ S.completeAtU u then
        (q : ℝ) * ((S.coefficientMean c i) ^ 2 /
          ((S.orbit i).card : ℝ))
       else 0) + 64 * S.coefficientVariance c i := by
  classical
  by_cases hiC : i ∈ S.completeAtU u
  · have hui := ((S.mem_completeAtU_iff u i).1 hiC).2
    rw [S.rawAtCenteredSq_self_eq_of_mem c i hui]
    simp only [hiC, if_true]
    have hv := S.coefficientVariance_nonneg c i
    nlinarith
  · simp only [hiC, if_false, zero_add]
    by_cases hui : u ∈ S.orbit i
    · have hinc : ¬ S.Complete i := by
        intro hcomplete
        exact hiC ((S.mem_completeAtU_iff u i).2 ⟨hcomplete, hui⟩)
      rw [S.rawAtCenteredSq_self_eq_of_mem c i hui]
      have hm : 0 < ((S.orbit i).card : ℝ) := by
        exact_mod_cast (S.orbit_nonempty i).card_pos
      have hqdiv : (q : ℝ) / ((S.orbit i).card : ℝ) ≤ 8 := by
        apply (div_le_iff₀ hm).2
        exact_mod_cast H.orbit_lower i
      have hmean := S.incomplete_mean_sq_le c i (hgapU i hinc)
      calc
        (q : ℝ) *
            ((S.coefficientMean c i) ^ 2 /
              ((S.orbit i).card : ℝ)) =
          ((q : ℝ) / ((S.orbit i).card : ℝ)) *
            (S.coefficientMean c i) ^ 2 := by ring
        _ ≤ 8 * (S.coefficientMean c i) ^ 2 :=
          mul_le_mul_of_nonneg_right hqdiv (sq_nonneg _)
        _ ≤ 64 * S.coefficientVariance c i := by nlinarith
    · rw [S.rawAtCenteredSq_self_eq_zero_of_not_mem c i hui]
      simp only [mul_zero]
      exact mul_nonneg (by norm_num) (S.coefficientVariance_nonneg c i)

/-- Sum of all diagonal centered moments. -/
theorem q_mul_sum_rawAtCenteredSq_self_le {q t : ℕ} {u : Fin B}
    (c : S.OutsideCoeff u) (H : S.SectorBounds q t)
    (horth : S.RawCommonOrthogonal u (S.synth c.val))
    (hgapU : ∀ i, ¬ S.Complete i →
      (S.orbit i).card ≤ 8 * (S.missingValues u i).card) :
    (q : ℝ) * ∑ i, S.rawAtCenteredSq c i i ≤
      20000 * (t : ℝ) * S.rawNormSq (S.synth c.val) +
        64 * S.totalVariance c := by
  classical
  let T : Fin d → ℝ := fun i =>
    (q : ℝ) * ((S.coefficientMean c i) ^ 2 /
      ((S.orbit i).card : ℝ))
  have hpoint :
      ∑ i, (q : ℝ) * S.rawAtCenteredSq c i i ≤
        ∑ i, ((if i ∈ S.completeAtU u then T i else 0) +
          64 * S.coefficientVariance c i) := by
    apply Finset.sum_le_sum
    intro i _
    exact S.q_mul_rawAtCenteredSq_self_le c H hgapU i
  have hite :
      (∑ i, if i ∈ S.completeAtU u then T i else 0) =
        ∑ i ∈ S.completeAtU u, T i := by
    simp only [Finset.sum_ite_mem, Finset.univ_inter]
  have hTsum :
      (∑ i ∈ S.completeAtU u, T i) =
        (q : ℝ) * ∑ i ∈ S.completeAtU u,
          (S.coefficientMean c i) ^ 2 /
            ((S.orbit i).card : ℝ) := by
    unfold T
    rw [Finset.mul_sum]
  have hVsum :
      (∑ i, 64 * S.coefficientVariance c i) =
        64 * S.totalVariance c := by
    unfold totalVariance
    rw [Finset.mul_sum]
  have hsum :
      (q : ℝ) * ∑ i, S.rawAtCenteredSq c i i ≤
        (q : ℝ) * ∑ i ∈ S.completeAtU u,
          (S.coefficientMean c i) ^ 2 /
            ((S.orbit i).card : ℝ) +
          64 * S.totalVariance c := by
    rw [Finset.mul_sum]
    calc
      ∑ i, (q : ℝ) * S.rawAtCenteredSq c i i ≤
          ∑ i, ((if i ∈ S.completeAtU u then T i else 0) +
            64 * S.coefficientVariance c i) := hpoint
      _ = (∑ i, if i ∈ S.completeAtU u then T i else 0) +
          ∑ i, 64 * S.coefficientVariance c i :=
        Finset.sum_add_distrib
      _ = (q : ℝ) * ∑ i ∈ S.completeAtU u,
          (S.coefficientMean c i) ^ 2 /
            ((S.orbit i).card : ℝ) +
          64 * S.totalVariance c := by
        rw [hite, hTsum, hVsum]
  have hcomplete := S.complete_weighted_mean_bound c H horth hgapU
  linarith

/-- One occupancy-count/centered-row moment is its diagonal term plus at most
`8d/q` times that row's variance. -/
theorem q_mul_rawCountCenteredSq_le {q t : ℕ} {u : Fin B}
    (c : S.OutsideCoeff u) (H : S.SectorBounds q t) (j : Fin d) :
    (q : ℝ) * S.rawCountCenteredSq c j ≤
      (q : ℝ) * S.rawAtCenteredSq c j j +
        8 * (d : ℝ) * S.coefficientVariance c j := by
  classical
  rw [S.rawCountCenteredSq_eq_sum c j]
  rw [← Finset.sum_erase_add Finset.univ
    (fun i => S.rawAtCenteredSq c i j) (Finset.mem_univ j)]
  rw [mul_add]
  have hoff :
      (q : ℝ) * ∑ i ∈ Finset.univ.erase j,
          S.rawAtCenteredSq c i j ≤
        8 * (d : ℝ) * S.coefficientVariance c j := by
    rw [Finset.mul_sum]
    calc
      ∑ i ∈ Finset.univ.erase j,
          (q : ℝ) * S.rawAtCenteredSq c i j ≤
        ∑ _i ∈ Finset.univ.erase j,
          8 * S.coefficientVariance c j := by
        apply Finset.sum_le_sum
        intro i hi
        exact S.q_mul_rawAtCenteredSq_le_eight_variance c H i j
          (Ne.symm (Finset.ne_of_mem_erase hi))
      _ = ((Finset.univ.erase j).card : ℝ) *
          (8 * S.coefficientVariance c j) := by
        simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (d : ℝ) * (8 * S.coefficientVariance c j) := by
        apply mul_le_mul_of_nonneg_right
        · simpa [Fintype.card_fin] using
            (Finset.univ.erase j).card_le_univ
        · exact mul_nonneg (by norm_num) (S.coefficientVariance_nonneg c j)
      _ = 8 * (d : ℝ) * S.coefficientVariance c j := by ring
  nlinarith

/-- Total occupancy-count/centered-row contribution. -/
theorem q_mul_sum_rawCountCenteredSq_le {q t : ℕ} {u : Fin B}
    (c : S.OutsideCoeff u) (H : S.SectorBounds q t)
    (horth : S.RawCommonOrthogonal u (S.synth c.val))
    (hgapU : ∀ i, ¬ S.Complete i →
      (S.orbit i).card ≤ 8 * (S.missingValues u i).card) :
    (q : ℝ) * ∑ j, S.rawCountCenteredSq c j ≤
      20000 * (t : ℝ) * S.rawNormSq (S.synth c.val) +
        (64 + 8 * (d : ℝ)) * S.totalVariance c := by
  classical
  have hpoint :
      ∑ j, (q : ℝ) * S.rawCountCenteredSq c j ≤
        ∑ j, ((q : ℝ) * S.rawAtCenteredSq c j j +
          8 * (d : ℝ) * S.coefficientVariance c j) := by
    apply Finset.sum_le_sum
    intro j _
    exact S.q_mul_rawCountCenteredSq_le c H j
  have hsum :
      (q : ℝ) * ∑ j, S.rawCountCenteredSq c j ≤
        (q : ℝ) * ∑ j, S.rawAtCenteredSq c j j +
          8 * (d : ℝ) * S.totalVariance c := by
    rw [Finset.mul_sum]
    simpa [totalVariance, Finset.sum_add_distrib, Finset.mul_sum] using hpoint
  have hdiag := S.q_mul_sum_rawAtCenteredSq_self_le c H horth hgapU
  nlinarith

/-- Ideal product-table occupancy estimate for a quotient-orthogonal outside
vector represented by supported coefficients. -/
theorem q_mul_rawOccupiedEnergy_synth_le {q t : ℕ} {u : Fin B}
    (c : S.OutsideCoeff u) (H : S.SectorBounds q t)
    (horth : S.RawCommonOrthogonal u (S.synth c.val))
    (hgapU : ∀ i, ¬ S.Complete i →
      (S.orbit i).card ≤ 8 * (S.missingValues u i).card) :
    (q : ℝ) * S.rawOccupiedEnergy u (S.synth c.val) ≤
      50000 * (t : ℝ) ^ 2 * S.rawNormSq (S.synth c.val) := by
  have hdecomp := S.rawOccupiedEnergy_synth_le_decomposition c
  have hq0 : 0 ≤ (q : ℝ) := by positivity
  have hscaled :
      (q : ℝ) * S.rawOccupiedEnergy u (S.synth c.val) ≤
        2 * (S.totalMean c.val) ^ 2 *
            ((q : ℝ) * S.rawAvg (S.rawOccupancyCount u)) +
          2 * (d : ℝ) *
            ((q : ℝ) * ∑ j, S.rawCountCenteredSq c j) := by
    calc
      (q : ℝ) * S.rawOccupiedEnergy u (S.synth c.val) ≤
          (q : ℝ) *
            (2 * (S.totalMean c.val) ^ 2 *
                S.rawAvg (S.rawOccupancyCount u) +
              2 * (d : ℝ) * ∑ j, S.rawCountCenteredSq c j) :=
        mul_le_mul_of_nonneg_left hdecomp hq0
      _ = 2 * (S.totalMean c.val) ^ 2 *
            ((q : ℝ) * S.rawAvg (S.rawOccupancyCount u)) +
          2 * (d : ℝ) *
            ((q : ℝ) * ∑ j, S.rawCountCenteredSq c j) := by ring
  have hcount := S.q_mul_rawAvg_occupancyCount_le H u
  have hcenter := S.q_mul_sum_rawCountCenteredSq_le c H horth hgapU
  have hfirst :
      2 * (S.totalMean c.val) ^ 2 *
          ((q : ℝ) * S.rawAvg (S.rawOccupancyCount u)) ≤
        16 * (d : ℝ) * (S.totalMean c.val) ^ 2 := by
    calc
      2 * (S.totalMean c.val) ^ 2 *
          ((q : ℝ) * S.rawAvg (S.rawOccupancyCount u)) ≤
        2 * (S.totalMean c.val) ^ 2 * (8 * (d : ℝ)) :=
          mul_le_mul_of_nonneg_left hcount
            (mul_nonneg (by norm_num) (sq_nonneg _))
      _ = 16 * (d : ℝ) * (S.totalMean c.val) ^ 2 := by ring
  have hd0 : 0 ≤ (d : ℝ) := by positivity
  have hsecond :
      2 * (d : ℝ) *
          ((q : ℝ) * ∑ j, S.rawCountCenteredSq c j) ≤
        2 * (d : ℝ) *
          (20000 * (t : ℝ) * S.rawNormSq (S.synth c.val) +
            (64 + 8 * (d : ℝ)) * S.totalVariance c) :=
    mul_le_mul_of_nonneg_left hcenter (mul_nonneg (by norm_num) hd0)
  have hdt : (d : ℝ) ≤ (t : ℝ) := by exact_mod_cast H.coord_le
  have ht : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast H.t_pos
  have ht0 : 0 ≤ (t : ℝ) := le_trans (by norm_num) ht
  have hV := S.totalVariance_nonneg c
  have hnorm := S.rawNormSq_synth_eq c
  have ha2 : 0 ≤ (S.totalMean c.val) ^ 2 := sq_nonneg _
  have hnorm0 : 0 ≤ S.rawNormSq (S.synth c.val) := by
    rw [hnorm]
    positivity
  have ha_le_norm :
      (S.totalMean c.val) ^ 2 ≤ S.rawNormSq (S.synth c.val) := by
    rw [hnorm]
    linarith
  have hV_le_norm :
      S.totalVariance c ≤ S.rawNormSq (S.synth c.val) := by
    rw [hnorm]
    linarith
  have hdA :
      (d : ℝ) * (S.totalMean c.val) ^ 2 ≤
        (t : ℝ) * S.rawNormSq (S.synth c.val) := by
    calc
      (d : ℝ) * (S.totalMean c.val) ^ 2 ≤
          (t : ℝ) * (S.totalMean c.val) ^ 2 :=
        mul_le_mul_of_nonneg_right hdt ha2
      _ ≤ (t : ℝ) * S.rawNormSq (S.synth c.val) :=
        mul_le_mul_of_nonneg_left ha_le_norm ht0
  have hdV :
      (d : ℝ) * S.totalVariance c ≤
        (t : ℝ) * S.rawNormSq (S.synth c.val) := by
    calc
      (d : ℝ) * S.totalVariance c ≤
          (t : ℝ) * S.totalVariance c :=
        mul_le_mul_of_nonneg_right hdt hV
      _ ≤ (t : ℝ) * S.rawNormSq (S.synth c.val) :=
        mul_le_mul_of_nonneg_left hV_le_norm ht0
  have hdtNorm :
      (d : ℝ) * (t : ℝ) * S.rawNormSq (S.synth c.val) ≤
        (t : ℝ) ^ 2 * S.rawNormSq (S.synth c.val) := by
    have hdt' : (d : ℝ) * (t : ℝ) ≤ (t : ℝ) ^ 2 := by
      calc
        (d : ℝ) * (t : ℝ) ≤ (t : ℝ) * (t : ℝ) :=
          mul_le_mul_of_nonneg_right hdt ht0
        _ = (t : ℝ) ^ 2 := by ring
    exact mul_le_mul_of_nonneg_right hdt' hnorm0
  have hd2V :
      (d : ℝ) ^ 2 * S.totalVariance c ≤
        (t : ℝ) ^ 2 * S.rawNormSq (S.synth c.val) := by
    have hd2 : (d : ℝ) ^ 2 ≤ (t : ℝ) ^ 2 := by nlinarith
    calc
      (d : ℝ) ^ 2 * S.totalVariance c ≤
          (t : ℝ) ^ 2 * S.totalVariance c :=
        mul_le_mul_of_nonneg_right hd2 hV
      _ ≤ (t : ℝ) ^ 2 * S.rawNormSq (S.synth c.val) :=
        mul_le_mul_of_nonneg_left hV_le_norm (sq_nonneg _)
  have htNorm_le_t2Norm :
      (t : ℝ) * S.rawNormSq (S.synth c.val) ≤
        (t : ℝ) ^ 2 * S.rawNormSq (S.synth c.val) := by
    have htt : (t : ℝ) ≤ (t : ℝ) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right htt hnorm0
  calc
    (q : ℝ) * S.rawOccupiedEnergy u (S.synth c.val) ≤
        16 * (d : ℝ) * (S.totalMean c.val) ^ 2 +
          2 * (d : ℝ) *
            (20000 * (t : ℝ) * S.rawNormSq (S.synth c.val) +
              (64 + 8 * (d : ℝ)) * S.totalVariance c) :=
      hscaled.trans (add_le_add hfirst hsecond)
    _ ≤ 50000 * (t : ℝ) ^ 2 * S.rawNormSq (S.synth c.val) := by
      nlinarith

end SectorData
end IndependentMatchingBlockOccupancy
