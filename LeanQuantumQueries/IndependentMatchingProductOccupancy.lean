import LeanQuantumQueries.IndependentMatchingConditioning
import LeanQuantumQueries.IndependentMatchingDefectArithmetic

open scoped BigOperators

namespace IndependentMatchingBlockOccupancy
namespace SectorData

variable {d B : ℕ} (S : SectorData d B)

/-- Numerical facts supplied by the block-orbit construction.  They are kept
as a predicate so the graph-specific file can prove them, rather than as
extra fields of `SectorData`. -/
structure SectorNumericsV (q t : ℕ) : Prop where
  t_pos : 1 ≤ t
  coord_le : d ≤ t
  orbit_lower : ∀ i, q ≤ 8 * (S.orbit i).card
  incomplete_gap : ∀ (u : Fin B) i, ¬ S.Complete i →
    (S.orbit i).card ≤ 8 * (S.missingValues u i).card

/-- Coordinates whose orbit contains the distinguished block. -/
def atUIndicesV (u : Fin B) : Finset (Fin d) :=
  Finset.univ.filter fun i => u ∈ S.orbit i

/-- Complete coordinates whose orbit contains the distinguished block. -/
def completeAtUV (u : Fin B) : Finset (Fin d) :=
  Finset.univ.filter fun i => S.Complete i ∧ u ∈ S.orbit i

/-- Structurally incomplete coordinates. -/
def incompleteIndicesV : Finset (Fin d) :=
  Finset.univ.filter fun i => ¬ S.Complete i

/-- Incomplete coordinates whose orbit contains the distinguished block. -/
def incompleteAtUV (u : Fin B) : Finset (Fin d) :=
  Finset.univ.filter fun i => ¬ S.Complete i ∧ u ∈ S.orbit i

@[simp] theorem mem_atUIndicesV_iff (u : Fin B) (i : Fin d) :
    i ∈ S.atUIndicesV u ↔ u ∈ S.orbit i := by
  simp [atUIndicesV]

@[simp] theorem mem_completeAtUV_iff (u : Fin B) (i : Fin d) :
    i ∈ S.completeAtUV u ↔ S.Complete i ∧ u ∈ S.orbit i := by
  simp [completeAtUV]

@[simp] theorem mem_incompleteIndicesV_iff (i : Fin d) :
    i ∈ S.incompleteIndicesV ↔ ¬ S.Complete i := by
  simp [incompleteIndicesV]

@[simp] theorem mem_incompleteAtUV_iff (u : Fin B) (i : Fin d) :
    i ∈ S.incompleteAtUV u ↔ ¬ S.Complete i ∧ u ∈ S.orbit i := by
  simp [incompleteAtUV]

/-- Mean of one coefficient row. -/
noncomputable def rowMeanV {u : Fin B} (c : S.OutsideCoeff u)
    (i : Fin d) : ℝ := S.coordAvg i (c.val i)

/-- Variance of one centered coefficient row. -/
noncomputable def rowVarianceV {u : Fin B} (c : S.OutsideCoeff u)
    (i : Fin d) : ℝ :=
  S.rawNormSq (S.lift i (S.centered i (c.val i)))

/-- Sum of all centered row variances. -/
noncomputable def totalVarianceV {u : Fin B} (c : S.OutsideCoeff u) : ℝ :=
  ∑ i, S.rowVarianceV c i

/-- Product-table occupied-energy upper sum.  On injective placements the
coordinate cylinders are disjoint, so this becomes the actual occupied
energy. -/
noncomputable def rawOccupiedUpperV {u : Fin B} (c : S.OutsideCoeff u) : ℝ :=
  ∑ i ∈ S.atUIndicesV u,
    S.rawAvg (fun x => S.rawAtU u i x * (S.synth c.val x) ^ 2)

/-- Each row variance is nonnegative. -/
theorem rowVarianceV_nonneg {u : Fin B} (c : S.OutsideCoeff u)
    (i : Fin d) : 0 ≤ S.rowVarianceV c i := by
  rw [rowVarianceV, S.rawNormSq_lift]
  unfold coordAvg
  exact div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    (by positivity)

/-- Total variance is nonnegative. -/
theorem totalVarianceV_nonneg {u : Fin B} (c : S.OutsideCoeff u) :
    0 ≤ S.totalVarianceV c := by
  unfold totalVarianceV
  exact Finset.sum_nonneg fun i _ => S.rowVarianceV_nonneg c i

/-- Exact norm decomposition in the row notation. -/
theorem rawNormSq_synth_eq_mean_varianceV {u : Fin B}
    (c : S.OutsideCoeff u) :
    S.rawNormSq (S.synth c.val) =
      (S.totalMean c.val) ^ 2 + S.totalVarianceV c := by
  exact S.rawNormSq_synth c.val

/-- Variance over any coordinate subset is at most total variance. -/
theorem sum_rowVarianceV_le_total {u : Fin B}
    (c : S.OutsideCoeff u) (I : Finset (Fin d)) :
    (∑ i ∈ I, S.rowVarianceV c i) ≤ S.totalVarianceV c := by
  unfold totalVarianceV
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
  intro i _ _
  exact S.rowVarianceV_nonneg c i

/-- There are at most `t` coordinates in any of the displayed index sets. -/
theorem card_indexSet_le_t {q t : ℕ} (H : S.SectorNumericsV q t)
    (I : Finset (Fin d)) : I.card ≤ t :=
  le_trans (Finset.card_le_univ I) H.coord_le

/-- The sum of all incomplete row means is controlled by total variance. -/
theorem incomplete_mean_sum_sq_leV
    {q t : ℕ} {u : Fin B} (c : S.OutsideCoeff u)
    (H : S.SectorNumericsV q t) :
    (∑ i ∈ S.incompleteIndicesV, S.rowMeanV c i) ^ 2 ≤
      8 * (t : ℝ) * S.totalVarianceV c := by
  classical
  let I := S.incompleteIndicesV
  have hcs := Finset.sq_sum_le_card_mul_sum_sq
    (s := I) (f := fun i => S.rowMeanV c i)
  have hmean :
      (∑ i ∈ I, (S.rowMeanV c i) ^ 2) ≤
        8 * ∑ i ∈ I, S.rowVarianceV c i := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hinc : ¬ S.Complete i :=
      (S.mem_incompleteIndicesV_iff i).1 hi
    exact OutsideCoeff.mean_sq_le_eight_variance (S := S) c i
      (H.incomplete_gap u i hinc)
  have hvar := S.sum_rowVarianceV_le_total c I
  have hcardNat : I.card ≤ t := S.card_indexSet_le_t H I
  have hcard : (I.card : ℝ) ≤ (t : ℝ) := by exact_mod_cast hcardNat
  have hIvar : 0 ≤ ∑ i ∈ I, S.rowVarianceV c i :=
    Finset.sum_nonneg fun i _ => S.rowVarianceV_nonneg c i
  have hV := S.totalVarianceV_nonneg c
  have ht : 0 ≤ (t : ℝ) := by positivity
  nlinarith

/-- Defect contribution of incomplete coordinates containing `u`. -/
theorem incomplete_defect_boundV
    {q t : ℕ} {u : Fin B} (c : S.OutsideCoeff u)
    (H : S.SectorNumericsV q t) :
    (q : ℝ) * ∑ i ∈ S.incompleteAtUV u,
        (S.totalMean c.val - S.rowMeanV c i) ^ 2 /
          ((S.orbit i).card : ℝ) ≤
      144 * (t : ℝ) *
        ((S.totalMean c.val) ^ 2 + S.totalVarianceV c) := by
  classical
  let J := S.incompleteAtUV u
  let I := S.incompleteIndicesV
  let a := S.totalMean c.val
  let V := S.totalVarianceV c
  have ht : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast H.t_pos
  have hV : 0 ≤ V := S.totalVarianceV_nonneg c
  have hterm : ∀ i ∈ J,
      (q : ℝ) * ((a - S.rowMeanV c i) ^ 2 /
        ((S.orbit i).card : ℝ)) ≤
        16 * a ^ 2 + 16 * (S.rowMeanV c i) ^ 2 := by
    intro i hi
    have hmi : 0 < ((S.orbit i).card : ℝ) := by
      exact_mod_cast (S.orbit_nonempty i).card_pos
    have hqmi : (q : ℝ) / ((S.orbit i).card : ℝ) ≤ 8 := by
      apply (div_le_iff₀ hmi).2
      exact_mod_cast H.orbit_lower i
    have hdef : (a - S.rowMeanV c i) ^ 2 ≤
        2 * a ^ 2 + 2 * (S.rowMeanV c i) ^ 2 := by
      nlinarith [sq_nonneg (a + S.rowMeanV c i)]
    calc
      (q : ℝ) * ((a - S.rowMeanV c i) ^ 2 /
          ((S.orbit i).card : ℝ)) =
          ((q : ℝ) / ((S.orbit i).card : ℝ)) *
            (a - S.rowMeanV c i) ^ 2 := by ring
      _ ≤ 8 * (a - S.rowMeanV c i) ^ 2 :=
        mul_le_mul_of_nonneg_right hqmi (sq_nonneg _)
      _ ≤ 8 * (2 * a ^ 2 + 2 * (S.rowMeanV c i) ^ 2) :=
        mul_le_mul_of_nonneg_left hdef (by norm_num)
      _ = 16 * a ^ 2 + 16 * (S.rowMeanV c i) ^ 2 := by ring
  have hsum :
      (q : ℝ) * ∑ i ∈ J,
          (a - S.rowMeanV c i) ^ 2 /
            ((S.orbit i).card : ℝ) ≤
        16 * (J.card : ℝ) * a ^ 2 +
          16 * ∑ i ∈ J, (S.rowMeanV c i) ^ 2 := by
    rw [Finset.mul_sum]
    calc
      ∑ i ∈ J, (q : ℝ) *
          ((a - S.rowMeanV c i) ^ 2 /
            ((S.orbit i).card : ℝ)) ≤
          ∑ i ∈ J,
            (16 * a ^ 2 + 16 * (S.rowMeanV c i) ^ 2) :=
        Finset.sum_le_sum fun i hi => hterm i hi
      _ = 16 * (J.card : ℝ) * a ^ 2 +
          16 * ∑ i ∈ J, (S.rowMeanV c i) ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_const,
          Finset.mul_sum, nsmul_eq_mul]
        ring
  have hJsubI : J ⊆ I := by
    intro i hi
    exact (S.mem_incompleteIndicesV_iff i).2
      ((S.mem_incompleteAtUV_iff u i).1 hi).1
  have hmeanJ :
      (∑ i ∈ J, (S.rowMeanV c i) ^ 2) ≤
        8 * S.totalVarianceV c := by
    have hlocal :
        (∑ i ∈ I, (S.rowMeanV c i) ^ 2) ≤
          8 * ∑ i ∈ I, S.rowVarianceV c i := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      have hinc := (S.mem_incompleteIndicesV_iff i).1 hi
      exact OutsideCoeff.mean_sq_le_eight_variance (S := S) c i
        (H.incomplete_gap u i hinc)
    have hsub :
        (∑ i ∈ J, (S.rowMeanV c i) ^ 2) ≤
          ∑ i ∈ I, (S.rowMeanV c i) ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hJsubI
      intro i _ _
      exact sq_nonneg _
    have hvar := S.sum_rowVarianceV_le_total c I
    nlinarith
  have hcardNat : J.card ≤ t := S.card_indexSet_le_t H J
  have hcard : (J.card : ℝ) ≤ (t : ℝ) := by exact_mod_cast hcardNat
  have ha : 0 ≤ a ^ 2 := sq_nonneg _
  have htarget :
      16 * (J.card : ℝ) * a ^ 2 +
          16 * ∑ i ∈ J, (S.rowMeanV c i) ^ 2 ≤
        144 * (t : ℝ) * (a ^ 2 + V) := by
    nlinarith
  exact le_trans hsum htarget

/-- Defect contribution of complete coordinates containing `u`. -/
theorem complete_defect_boundV
    {q t : ℕ} {u : Fin B} (c : S.OutsideCoeff u)
    (H : S.SectorNumericsV q t)
    (horth : S.RawCommonOrthogonal u (S.synth c.val)) :
    (q : ℝ) * ∑ i ∈ S.completeAtUV u,
        (S.totalMean c.val - S.rowMeanV c i) ^ 2 /
          ((S.orbit i).card : ℝ) ≤
      200 * (t : ℝ) *
        ((S.totalMean c.val) ^ 2 + S.totalVarianceV c) := by
  classical
  let C := S.completeAtUV u
  let a := S.totalMean c.val
  let V := S.totalVarianceV c
  have ht : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast H.t_pos
  have hq : 0 ≤ (q : ℝ) := by positivity
  have hV : 0 ≤ V := S.totalVarianceV_nonneg c
  by_cases hav : ∃ h : Fin d, S.Complete h ∧ u ∉ S.orbit h
  · rcases hav with ⟨h, hh, huh⟩
    have hzero : ∀ i ∈ C, a - S.rowMeanV c i = 0 := by
      intro i hi
      have hi' := (S.mem_completeAtUV_iff u i).1 hi
      have hm := OutsideCoeff.complete_mean_eq_total_of_avoidingV
        (S := S) c horth i h hi'.1 hh hi'.2 huh
      unfold a rowMeanV
      linarith
    have hz :
        (q : ℝ) * ∑ i ∈ C,
            (a - S.rowMeanV c i) ^ 2 /
              ((S.orbit i).card : ℝ) = 0 := by
      apply mul_eq_zero_of_right
      apply Finset.sum_eq_zero
      intro i hi
      rw [hzero i hi]
      simp
    rw [hz]
    positivity
  · have hcontains : ∀ i, S.Complete i → u ∈ S.orbit i := by
      intro i hi
      by_contra hui
      exact hav ⟨i, hi, hui⟩
    by_cases hCempty : C = ∅
    · subst C
      simp [ht, hV]
    have hCne : C.Nonempty := Finset.nonempty_iff_ne_empty.2 hCempty
    let i0 : Fin d := hCne.choose
    have hi0C : i0 ∈ C := hCne.choose_spec
    have hi0 := (S.mem_completeAtUV_iff u i0).1 hi0C
    let lam : ℝ :=
      (a - S.rowMeanV c i0) / ((S.orbit i0).card : ℝ)
    let I := S.incompleteIndicesV
    let b : ℝ := ∑ i ∈ I, S.rowMeanV c i
    have hdef : ∀ i ∈ C,
        a - S.rowMeanV c i =
          ((S.orbit i).card : ℝ) * lam := by
      intro i hiC
      have hi := (S.mem_completeAtUV_iff u i).1 hiC
      have hscaled := OutsideCoeff.complete_scaled_defect_eqV
        (S := S) c horth i i0 hi.1 hi0.1 hi.2 hi0.2
      have hmi : ((S.orbit i).card : ℝ) ≠ 0 := by
        exact_mod_cast (S.orbit_nonempty i).card_ne_zero
      calc
        a - S.rowMeanV c i =
            ((S.orbit i).card : ℝ) *
              ((a - S.rowMeanV c i) /
                ((S.orbit i).card : ℝ)) := by
          field_simp [hmi]
        _ = ((S.orbit i).card : ℝ) *
              ((a - S.rowMeanV c i0) /
                ((S.orbit i0).card : ℝ)) := by
          rw [hscaled]
        _ = ((S.orbit i).card : ℝ) * lam := rfl
    have hCeq : C = Finset.univ.filter S.Complete := by
      ext i
      simp [C, completeAtUV, hcontains i]
    have hpartition :
        (∑ i, S.rowMeanV c i) =
          (∑ i ∈ C, S.rowMeanV c i) + b := by
      rw [hCeq]
      unfold b I incompleteIndicesV
      exact (Finset.sum_filter_add_sum_filter_not
        (s := (Finset.univ : Finset (Fin d)))
        (p := S.Complete)
        (f := fun i => S.rowMeanV c i)).symm
    have hsumC :
        (∑ i ∈ C, S.rowMeanV c i) =
          (C.card : ℝ) * a -
            (∑ i ∈ C, ((S.orbit i).card : ℝ)) * lam := by
      calc
        (∑ i ∈ C, S.rowMeanV c i) =
            ∑ i ∈ C,
              (a - ((S.orbit i).card : ℝ) * lam) := by
          apply Finset.sum_congr rfl
          intro i hi
          linarith [hdef i hi]
        _ = (C.card : ℝ) * a -
            (∑ i ∈ C, ((S.orbit i).card : ℝ)) * lam := by
          rw [Finset.sum_sub_distrib, Finset.sum_const,
            Finset.sum_mul, nsmul_eq_mul]
          ring
    have haSum : a = ∑ i, S.rowMeanV c i := by
      rfl
    have heq :
        (∑ i ∈ C, ((S.orbit i).card : ℝ)) * lam =
          ((C.card : ℝ) - 1) * a + b := by
      rw [haSum, hpartition, hsumC]
      ring
    have hb : b ^ 2 ≤ 8 * (t : ℝ) * V := by
      exact S.incomplete_mean_sum_sq_leV c H
    have hcardNat : C.card ≤ t := S.card_indexSet_le_t H C
    have hcard : (C.card : ℝ) ≤ (t : ℝ) := by exact_mod_cast hcardNat
    have hmpos : ∀ i ∈ C, 0 < ((S.orbit i).card : ℝ) := by
      intro i _
      exact_mod_cast (S.orbit_nonempty i).card_pos
    have hlower : ∀ i ∈ C,
        (q : ℝ) ≤ 8 * ((S.orbit i).card : ℝ) := by
      intro i _
      exact_mod_cast H.orbit_lower i
    have harith := weighted_complete_defect_bound
      C (fun i => ((S.orbit i).card : ℝ))
      (q : ℝ) (t : ℝ) a b lam V ht hq hV hcard hmpos hlower heq hb
    have hrewrite :
        (q : ℝ) * ∑ i ∈ C,
            (a - S.rowMeanV c i) ^ 2 /
              ((S.orbit i).card : ℝ) =
          (q : ℝ) * ∑ i ∈ C,
            ((((S.orbit i).card : ℝ) * lam) ^ 2 /
              ((S.orbit i).card : ℝ)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [hdef i hi]
    rw [hrewrite]
    exact harith

/-- Contribution of the remaining-row variances. -/
theorem remaining_variance_boundV
    {q t : ℕ} {u : Fin B} (c : S.OutsideCoeff u)
    (H : S.SectorNumericsV q t) :
    (q : ℝ) * ∑ i ∈ S.atUIndicesV u,
        (∑ j ∈ (Finset.univ.erase i), S.rowVarianceV c j) /
          ((S.orbit i).card : ℝ) ≤
      8 * (t : ℝ) * S.totalVarianceV c := by
  classical
  let U := S.atUIndicesV u
  let V := S.totalVarianceV c
  have hterm : ∀ i ∈ U,
      (q : ℝ) *
          ((∑ j ∈ (Finset.univ.erase i), S.rowVarianceV c j) /
            ((S.orbit i).card : ℝ)) ≤ 8 * V := by
    intro i _
    have hmi : 0 < ((S.orbit i).card : ℝ) := by
      exact_mod_cast (S.orbit_nonempty i).card_pos
    have hratio : (q : ℝ) / ((S.orbit i).card : ℝ) ≤ 8 := by
      apply (div_le_iff₀ hmi).2
      exact_mod_cast H.orbit_lower i
    have hsum := S.sum_rowVarianceV_le_total c (Finset.univ.erase i)
    have hsum0 : 0 ≤
        ∑ j ∈ (Finset.univ.erase i), S.rowVarianceV c j :=
      Finset.sum_nonneg fun j _ => S.rowVarianceV_nonneg c j
    calc
      (q : ℝ) *
          ((∑ j ∈ (Finset.univ.erase i), S.rowVarianceV c j) /
            ((S.orbit i).card : ℝ)) =
          ((q : ℝ) / ((S.orbit i).card : ℝ)) *
            (∑ j ∈ (Finset.univ.erase i), S.rowVarianceV c j) := by ring
      _ ≤ 8 * (∑ j ∈ (Finset.univ.erase i), S.rowVarianceV c j) :=
        mul_le_mul_of_nonneg_right hratio hsum0
      _ ≤ 8 * V := mul_le_mul_of_nonneg_left hsum (by norm_num)
  rw [Finset.mul_sum]
  calc
    ∑ i ∈ U, (q : ℝ) *
        ((∑ j ∈ (Finset.univ.erase i), S.rowVarianceV c j) /
          ((S.orbit i).card : ℝ)) ≤
        ∑ _i ∈ U, 8 * V :=
      Finset.sum_le_sum fun i hi => hterm i hi
    _ = 8 * (U.card : ℝ) * V := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 8 * (t : ℝ) * V := by
      have hcardNat : U.card ≤ t := S.card_indexSet_le_t H U
      have hcard : (U.card : ℝ) ≤ (t : ℝ) := by exact_mod_cast hcardNat
      have hV := S.totalVarianceV_nonneg c
      nlinarith

/-- The product-table occupied upper sum is bounded by `352 t/q` times total
squared norm. -/
theorem rawOccupiedUpperV_bound
    {q t : ℕ} {u : Fin B} (c : S.OutsideCoeff u)
    (H : S.SectorNumericsV q t)
    (horth : S.RawCommonOrthogonal u (S.synth c.val)) :
    (q : ℝ) * S.rawOccupiedUpperV c ≤
      352 * (t : ℝ) * S.rawNormSq (S.synth c.val) := by
  classical
  let U := S.atUIndicesV u
  let C := S.completeAtUV u
  let J := S.incompleteAtUV u
  let a := S.totalMean c.val
  let V := S.totalVarianceV c
  have hpartition : U = C ∪ J := by
    ext i
    by_cases hi : S.Complete i <;> simp [U, C, J, atUIndicesV,
      completeAtUV, incompleteAtUV, hi]
  have hdisj : Disjoint C J := by
    refine Finset.disjoint_left.2 ?_
    intro i hiC hiJ
    exact ((S.mem_incompleteAtUV_iff u i).1 hiJ).1
      ((S.mem_completeAtUV_iff u i).1 hiC).1
  unfold rawOccupiedUpperV
  rw [show S.atUIndicesV u = U by rfl, hpartition,
    Finset.sum_union hdisj]
  have hformula : ∀ i,
      S.rawAvg (fun x => S.rawAtU u i x * (S.synth c.val x) ^ 2) =
        ((a - S.rowMeanV c i) ^ 2 +
          ∑ j ∈ (Finset.univ.erase i), S.rowVarianceV c j) /
            ((S.orbit i).card : ℝ) := by
    intro i
    have hui : u ∈ S.orbit i := by
      by_cases hi : i ∈ U
      · exact (S.mem_atUIndicesV_iff u i).1 hi
      · by_contra hnot
        exact hi ((S.mem_atUIndicesV_iff u i).2 (by simpa using hnot))
    rw [OutsideCoeff.rawAvg_atU_mul_synth_sq (S := S) c i hui,
      S.rawNormSq_synth_eraseRow]
    rfl
  have hformulaC :
      (∑ i ∈ C,
        S.rawAvg (fun x => S.rawAtU u i x * (S.synth c.val x) ^ 2)) =
      ∑ i ∈ C,
        ((a - S.rowMeanV c i) ^ 2 +
          ∑ j ∈ (Finset.univ.erase i), S.rowVarianceV c j) /
            ((S.orbit i).card : ℝ) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hformula i
  have hformulaJ :
      (∑ i ∈ J,
        S.rawAvg (fun x => S.rawAtU u i x * (S.synth c.val x) ^ 2)) =
      ∑ i ∈ J,
        ((a - S.rowMeanV c i) ^ 2 +
          ∑ j ∈ (Finset.univ.erase i), S.rowVarianceV c j) /
            ((S.orbit i).card : ℝ) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hformula i
  rw [hformulaC, hformulaJ]
  have hsplit :
      (q : ℝ) *
          ((∑ i ∈ C,
              ((a - S.rowMeanV c i) ^ 2 +
                ∑ j ∈ (Finset.univ.erase i), S.rowVarianceV c j) /
                  ((S.orbit i).card : ℝ)) +
           (∑ i ∈ J,
              ((a - S.rowMeanV c i) ^ 2 +
                ∑ j ∈ (Finset.univ.erase i), S.rowVarianceV c j) /
                  ((S.orbit i).card : ℝ))) =
        ((q : ℝ) * ∑ i ∈ C,
            (a - S.rowMeanV c i) ^ 2 /
              ((S.orbit i).card : ℝ)) +
        ((q : ℝ) * ∑ i ∈ J,
            (a - S.rowMeanV c i) ^ 2 /
              ((S.orbit i).card : ℝ)) +
        ((q : ℝ) * ∑ i ∈ U,
            (∑ j ∈ (Finset.univ.erase i), S.rowVarianceV c j) /
              ((S.orbit i).card : ℝ)) := by
    rw [hpartition, Finset.sum_union hdisj]
    simp only [add_div]
    repeat' rw [Finset.sum_add_distrib]
    ring
  rw [hsplit]
  have hC := S.complete_defect_boundV c H horth
  have hJ := S.incomplete_defect_boundV c H
  have hVrem := S.remaining_variance_boundV c H
  rw [S.rawNormSq_synth_eq_mean_varianceV] at hC hJ ⊢
  have ht : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast H.t_pos
  have hnorm : 0 ≤ a ^ 2 + V := by
    exact add_nonneg (sq_nonneg _) (S.totalVarianceV_nonneg c)
  nlinarith

end SectorData
end IndependentMatchingBlockOccupancy
