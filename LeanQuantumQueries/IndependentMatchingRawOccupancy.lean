import LeanQuantumQueries.IndependentMatchingMeanBound

open scoped BigOperators

namespace IndependentMatchingBlockOccupancy
namespace SectorData

variable {d B : ℕ} (S : SectorData d B)

/-- Occupancy of a distinguished block before collision deletion. -/
def RawOccupied (u : Fin B) (x : S.RawPlacement) : Prop :=
  ∃ i, S.block x i = u

/-- Number of product coordinates carrying the distinguished block. -/
noncomputable def rawOccupancyCount (u : Fin B) : S.RawVector :=
  ∑ i, S.rawAtU u i

/-- Uniform product-table energy on placements occupying the distinguished
block. -/
noncomputable def rawOccupiedEnergy (u : Fin B) (f : S.RawVector) : ℝ := by
  classical
  exact S.rawAvg fun x => if S.RawOccupied u x then (f x) ^ 2 else 0

private theorem rawPlacement_nonempty : Nonempty S.RawPlacement := by
  classical
  refine ⟨fun i => ?_⟩
  exact ⟨(S.orbit_nonempty i).choose, (S.orbit_nonempty i).choose_spec⟩

private theorem rawPlacement_card_pos :
    0 < (Fintype.card S.RawPlacement : ℝ) := by
  haveI := S.rawPlacement_nonempty
  exact_mod_cast Fintype.card_pos

/-- Monotonicity of uniform product averaging. -/
theorem rawAvg_mono {f g : S.RawVector} (h : ∀ x, f x ≤ g x) :
    S.rawAvg f ≤ S.rawAvg g := by
  classical
  unfold rawAvg
  apply (div_le_div_iff_of_pos_right S.rawPlacement_card_pos).2
  exact Finset.sum_le_sum fun x _ => h x

/-- A finite coordinate sum can be moved through product averaging. -/
theorem rawAvg_sum (F : Fin d → S.RawVector) :
    S.rawAvg (∑ i, F i) = ∑ i, S.rawAvg (F i) := by
  classical
  unfold rawAvg
  simp only [Finset.sum_apply, Finset.sum_div]
  rw [Finset.sum_comm]

/-- Averaging a pointwise nonnegative function is nonnegative. -/
theorem rawAvg_nonneg {f : S.RawVector} (hf : ∀ x, 0 ≤ f x) :
    0 ≤ S.rawAvg f := by
  classical
  unfold rawAvg
  exact div_nonneg (Finset.sum_nonneg fun x _ => hf x)
    (by positivity)

/-- Every raw cylinder indicator is nonnegative. -/
theorem rawAtU_nonneg (u : Fin B) (i : Fin d) (x : S.RawPlacement) :
    0 ≤ S.rawAtU u i x := by
  unfold rawAtU rawFiber
  split_ifs <;> norm_num

/-- The occupancy count is nonnegative. -/
theorem rawOccupancyCount_nonneg (u : Fin B) (x : S.RawPlacement) :
    0 ≤ S.rawOccupancyCount u x := by
  classical
  unfold rawOccupancyCount
  simp only [Finset.sum_apply]
  exact Finset.sum_nonneg fun i _ => S.rawAtU_nonneg u i x

/-- An occupied product placement has occupancy count at least one. -/
theorem one_le_rawOccupancyCount (u : Fin B) (x : S.RawPlacement)
    (hx : S.RawOccupied u x) :
    1 ≤ S.rawOccupancyCount u x := by
  classical
  rcases hx with ⟨i, hi⟩
  have hone : S.rawAtU u i x = 1 := by
    simp [rawAtU, rawFiber, hi]
  calc
    1 = S.rawAtU u i x := hone.symm
    _ ≤ ∑ j, S.rawAtU u j x :=
      Finset.single_le_sum (fun j _ => S.rawAtU_nonneg u j x)
        (Finset.mem_univ i)
    _ = S.rawOccupancyCount u x := by
      simp [rawOccupancyCount]

/-- Occupied energy is bounded by occupancy-count-weighted energy. -/
theorem rawOccupiedEnergy_le_count (u : Fin B) (f : S.RawVector) :
    S.rawOccupiedEnergy u f ≤
      S.rawAvg (fun x => S.rawOccupancyCount u x * (f x) ^ 2) := by
  classical
  unfold rawOccupiedEnergy
  apply S.rawAvg_mono
  intro x
  by_cases hx : S.RawOccupied u x
  · simp only [hx, if_true]
    have hs := sq_nonneg (f x)
    have hc := S.one_le_rawOccupancyCount u x hx
    nlinarith
  · simp only [hx, if_false]
    exact mul_nonneg (S.rawOccupancyCount_nonneg u x) (sq_nonneg _)

/-- A raw distinguished fiber is zero when the block is absent from its
coordinate orbit. -/
theorem rawAtU_eq_zero_of_not_mem (u : Fin B) (i : Fin d)
    (hui : u ∉ S.orbit i) : S.rawAtU u i = 0 := by
  funext x
  unfold rawAtU rawFiber
  have hne : S.block x i ≠ u := by
    intro h
    apply hui
    rw [← h]
    exact (x i).2
  simp [hne]

/-- Product probability of fixing one coordinate at the distinguished block. -/
theorem rawAvg_rawAtU_eq_of_mem (u : Fin B) (i : Fin d)
    (hui : u ∈ S.orbit i) :
    S.rawAvg (S.rawAtU u i) = 1 / ((S.orbit i).card : ℝ) := by
  rw [S.rawAtU_eq_lift_indicator, S.rawAvg_lift,
    S.coordAvg_orbitIndicator u i hui]

/-- A coordinate absent from the distinguished block has zero cylinder
probability. -/
theorem rawAvg_rawAtU_eq_zero_of_not_mem (u : Fin B) (i : Fin d)
    (hui : u ∉ S.orbit i) : S.rawAvg (S.rawAtU u i) = 0 := by
  rw [S.rawAtU_eq_zero_of_not_mem u i hui]
  simp [rawAvg]

/-- The orbit lower bound gives a denominator-free cylinder-probability
estimate. -/
theorem q_mul_rawAvg_rawAtU_le_eight {q t : ℕ}
    (H : S.SectorBounds q t) (u : Fin B) (i : Fin d) :
    (q : ℝ) * S.rawAvg (S.rawAtU u i) ≤ 8 := by
  by_cases hui : u ∈ S.orbit i
  · rw [S.rawAvg_rawAtU_eq_of_mem u i hui]
    have hm : 0 < ((S.orbit i).card : ℝ) := by
      exact_mod_cast (S.orbit_nonempty i).card_pos
    have hq : (q : ℝ) ≤ 8 * ((S.orbit i).card : ℝ) := by
      exact_mod_cast H.orbit_lower i
    calc
      (q : ℝ) * (1 / ((S.orbit i).card : ℝ)) =
          (q : ℝ) / ((S.orbit i).card : ℝ) := by ring
      _ ≤ 8 := (div_le_iff₀ hm).2 hq
  · rw [S.rawAvg_rawAtU_eq_zero_of_not_mem u i hui]
    norm_num

/-- Total distinguished-block occupancy probability, in cross-multiplied
form. -/
theorem q_mul_rawAvg_occupancyCount_le {q t : ℕ}
    (H : S.SectorBounds q t) (u : Fin B) :
    (q : ℝ) * S.rawAvg (S.rawOccupancyCount u) ≤ 8 * (d : ℝ) := by
  classical
  unfold rawOccupancyCount
  rw [S.rawAvg_sum, Finset.mul_sum]
  calc
    ∑ i, (q : ℝ) * S.rawAvg (S.rawAtU u i) ≤ ∑ _i : Fin d, (8 : ℝ) :=
      Finset.sum_le_sum fun i _ => S.q_mul_rawAvg_rawAtU_le_eight H u i
    _ = 8 * (d : ℝ) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      ring

/-- Centered lift associated with one coordinate row. -/
noncomputable def centeredLift {u : Fin B} (c : S.OutsideCoeff u)
    (i : Fin d) : S.RawVector :=
  S.lift i (S.centered i (c.val i))

/-- Product average of a distinguished cylinder times one centered square. -/
noncomputable def rawAtCenteredSq {u : Fin B} (c : S.OutsideCoeff u)
    (i j : Fin d) : ℝ :=
  S.rawAvg fun x => S.rawAtU u i x * (S.centeredLift c j x) ^ 2

/-- These mixed energies are nonnegative. -/
theorem rawAtCenteredSq_nonneg {u : Fin B} (c : S.OutsideCoeff u)
    (i j : Fin d) : 0 ≤ S.rawAtCenteredSq c i j := by
  unfold rawAtCenteredSq
  apply S.rawAvg_nonneg
  intro x
  exact mul_nonneg (S.rawAtU_nonneg u i x) (sq_nonneg _)

/-- Off-diagonal cylinder/centered-square moments factor by product
independence. -/
theorem rawAtCenteredSq_eq_of_ne_of_mem {u : Fin B}
    (c : S.OutsideCoeff u) (i j : Fin d) (hji : j ≠ i)
    (hui : u ∈ S.orbit i) :
    S.rawAtCenteredSq c i j =
      (1 / ((S.orbit i).card : ℝ)) * S.coefficientVariance c j := by
  unfold rawAtCenteredSq centeredLift coefficientVariance
  rw [S.rawAtU_eq_lift_indicator]
  rw [show (fun x => S.lift i (S.orbitIndicator u i) x *
      (S.lift j (S.centered j (c.val j)) x) ^ 2) =
      (fun x => S.lift i (S.orbitIndicator u i) x *
        S.lift j (fun a => (S.centered j (c.val j) a) ^ 2) x) by
        funext x
        rfl]
  rw [S.rawAvg_mul_lift i j hji,
    S.coordAvg_orbitIndicator u i hui,
    ← S.rawNormSq_lift j]

/-- If the distinguished block is absent from the first orbit, every mixed
moment with its cylinder vanishes. -/
theorem rawAtCenteredSq_eq_zero_of_not_mem {u : Fin B}
    (c : S.OutsideCoeff u) (i j : Fin d)
    (hui : u ∉ S.orbit i) : S.rawAtCenteredSq c i j = 0 := by
  unfold rawAtCenteredSq
  rw [S.rawAtU_eq_zero_of_not_mem u i hui]
  simp [rawAvg]

/-- Uniform cross-multiplied off-diagonal moment bound. -/
theorem q_mul_rawAtCenteredSq_le_eight_variance
    {q t : ℕ} {u : Fin B} (c : S.OutsideCoeff u)
    (H : S.SectorBounds q t) (i j : Fin d) (hji : j ≠ i) :
    (q : ℝ) * S.rawAtCenteredSq c i j ≤
      8 * S.coefficientVariance c j := by
  by_cases hui : u ∈ S.orbit i
  · rw [S.rawAtCenteredSq_eq_of_ne_of_mem c i j hji hui]
    have hm : 0 < ((S.orbit i).card : ℝ) := by
      exact_mod_cast (S.orbit_nonempty i).card_pos
    have hq : (q : ℝ) / ((S.orbit i).card : ℝ) ≤ 8 := by
      apply (div_le_iff₀ hm).2
      exact_mod_cast H.orbit_lower i
    have hv := S.coefficientVariance_nonneg c j
    calc
      (q : ℝ) *
          ((1 / ((S.orbit i).card : ℝ)) * S.coefficientVariance c j) =
        ((q : ℝ) / ((S.orbit i).card : ℝ)) *
          S.coefficientVariance c j := by ring
      _ ≤ 8 * S.coefficientVariance c j :=
        mul_le_mul_of_nonneg_right hq hv
  · rw [S.rawAtCenteredSq_eq_zero_of_not_mem c i j hui]
    simp only [mul_zero]
    exact mul_nonneg (by norm_num) (S.coefficientVariance_nonneg c j)

/-- The same-coordinate cylinder moment is the squared row mean divided by
the orbit size. -/
theorem rawAtCenteredSq_self_eq_of_mem {u : Fin B}
    (c : S.OutsideCoeff u) (i : Fin d) (hui : u ∈ S.orbit i) :
    S.rawAtCenteredSq c i i =
      (S.coefficientMean c i) ^ 2 / ((S.orbit i).card : ℝ) := by
  classical
  let uu : {a : Fin B // a ∈ S.orbit i} := ⟨u, hui⟩
  have hcenter : S.centered i (c.val i) uu = -S.coefficientMean c i := by
    unfold centered coefficientMean
    rw [OutsideCoeff.atU_eq_zero (S := S) c i hui]
    ring
  unfold rawAtCenteredSq centeredLift
  rw [S.rawAtU_eq_lift_indicator]
  rw [show (fun x => S.lift i (S.orbitIndicator u i) x *
      (S.lift i (S.centered i (c.val i)) x) ^ 2) =
      S.lift i (fun a => S.orbitIndicator u i a *
        (S.centered i (c.val i) a) ^ 2) by
        funext x
        rfl]
  rw [S.rawAvg_lift]
  unfold coordAvg orbitIndicator
  have hsum :
      (∑ a : {a : Fin B // a ∈ S.orbit i},
        (if a.1 = u then (1 : ℝ) else 0) *
          (S.centered i (c.val i) a) ^ 2) =
        (S.coefficientMean c i) ^ 2 := by
    rw [Fintype.sum_eq_single uu]
    · simp [uu, hcenter]
    · intro a ha
      have hne : a.1 ≠ u := by
        intro h
        apply ha
        exact Subtype.ext h
      simp [hne]
  rw [hsum]

/-- Diagonal moment vanishes when the distinguished block is absent. -/
theorem rawAtCenteredSq_self_eq_zero_of_not_mem {u : Fin B}
    (c : S.OutsideCoeff u) (i : Fin d)
    (hui : u ∉ S.orbit i) : S.rawAtCenteredSq c i i = 0 :=
  S.rawAtCenteredSq_eq_zero_of_not_mem c i i hui

end SectorData
end IndependentMatchingBlockOccupancy
