import LeanQuantumQueries.IndependentMatchingProduct

open scoped BigOperators

namespace IndependentMatchingBlockOccupancy
namespace SectorData

variable {d B : ℕ} (S : SectorData d B)

/-- Uniform average over the product placement table. -/
noncomputable def rawAvg (f : S.RawVector) : ℝ :=
  (∑ x, f x) / (Fintype.card S.RawPlacement : ℝ)

/-- Uniform average over one coordinate orbit. -/
noncomputable def coordAvg (i : Fin d)
    (g : {a : Fin B // a ∈ S.orbit i} → ℝ) : ℝ :=
  (∑ a, g a) / (S.orbit i).card

/-- Lift a one-coordinate function to the product table. -/
def lift (i : Fin d) (g : {a : Fin B // a ∈ S.orbit i} → ℝ) : S.RawVector :=
  fun x => g (x i)

/-- Constant vector on the product table. -/
def constVec (a : ℝ) : S.RawVector := fun _ => a

/-- Uniform inner product on the product table. -/
noncomputable def rawInner (f g : S.RawVector) : ℝ :=
  S.rawAvg (fun x => f x * g x)

/-- Squared uniform `L²` norm. -/
noncomputable def rawNormSq (f : S.RawVector) : ℝ := S.rawInner f f

private theorem remaining_nonempty (i : Fin d) : Nonempty (S.Remaining i) := by
  classical
  refine ⟨fun j => ?_⟩
  exact ⟨(S.orbit_nonempty j.1).choose, (S.orbit_nonempty j.1).choose_spec⟩

private theorem remaining₂_nonempty (i j : Fin d) : Nonempty (S.Remaining₂ i j) := by
  classical
  refine ⟨fun k => ?_⟩
  exact ⟨(S.orbit_nonempty k.1).choose, (S.orbit_nonempty k.1).choose_spec⟩

private theorem remaining_card_ne_zero (i : Fin d) :
    (Fintype.card (S.Remaining i) : ℝ) ≠ 0 := by
  haveI := S.remaining_nonempty i
  exact_mod_cast Fintype.card_ne_zero

private theorem remaining₂_card_ne_zero (i j : Fin d) :
    (Fintype.card (S.Remaining₂ i j) : ℝ) ≠ 0 := by
  haveI := S.remaining₂_nonempty i j
  exact_mod_cast Fintype.card_ne_zero

private theorem orbit_card_ne_zero (i : Fin d) :
    ((S.orbit i).card : ℝ) ≠ 0 := by
  exact_mod_cast (S.orbit_nonempty i).card_ne_zero

private theorem raw_card_ne_zero :
    (Fintype.card S.RawPlacement : ℝ) ≠ 0 := by
  classical
  let x : S.RawPlacement := fun i =>
    ⟨(S.orbit_nonempty i).choose, (S.orbit_nonempty i).choose_spec⟩
  haveI : Nonempty S.RawPlacement := ⟨x⟩
  exact_mod_cast Fintype.card_ne_zero

/-- Average of a lifted coordinate function. -/
theorem rawAvg_lift (i : Fin d)
    (g : {a : Fin B // a ∈ S.orbit i} → ℝ) :
    S.rawAvg (S.lift i g) = S.coordAvg i g := by
  unfold rawAvg lift coordAvg
  rw [S.sum_coordinate i g, S.card_rawPlacement i]
  field_simp [S.remaining_card_ne_zero i, S.orbit_card_ne_zero i] <;> ring

/-- Average of a constant. -/
theorem rawAvg_const (a : ℝ) : S.rawAvg (S.constVec a) = a := by
  unfold rawAvg constVec
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp [S.raw_card_ne_zero] <;> ring

/-- Two distinct lifted coordinate functions factor under product averaging. -/
theorem rawAvg_mul_lift (i j : Fin d) (hji : j ≠ i)
    (g : {a : Fin B // a ∈ S.orbit i} → ℝ)
    (h : {b : Fin B // b ∈ S.orbit j} → ℝ) :
    S.rawAvg (fun x => S.lift i g x * S.lift j h x) =
      S.coordAvg i g * S.coordAvg j h := by
  unfold rawAvg lift coordAvg
  rw [S.sum_two_coordinates i j hji (fun a b => g a * h b),
    S.card_rawPlacement₂ i j hji]
  rw [← Fintype.sum_mul_sum]
  field_simp [S.remaining₂_card_ne_zero i j,
    S.orbit_card_ne_zero i, S.orbit_card_ne_zero j] <;> ring

/-- Linearity of product averaging. -/
theorem rawAvg_add (f g : S.RawVector) :
    S.rawAvg (f + g) = S.rawAvg f + S.rawAvg g := by
  classical
  unfold rawAvg
  simp only [Pi.add_apply, Finset.sum_add_distrib, add_div]

/-- Averaging commutes with scalar multiplication. -/
theorem rawAvg_smul (c : ℝ) (f : S.RawVector) :
    S.rawAvg (c • f) = c * S.rawAvg f := by
  classical
  unfold rawAvg
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum]
  ring

/-- Bilinearity in the first argument. -/
theorem rawInner_add_left (f g h : S.RawVector) :
    S.rawInner (f + g) h = S.rawInner f h + S.rawInner g h := by
  unfold rawInner
  simpa [Pi.add_apply, add_mul] using S.rawAvg_add
    (fun x => f x * h x) (fun x => g x * h x)

/-- Bilinearity in the second argument. -/
theorem rawInner_add_right (f g h : S.RawVector) :
    S.rawInner f (g + h) = S.rawInner f g + S.rawInner f h := by
  unfold rawInner
  simpa [Pi.add_apply, mul_add] using S.rawAvg_add
    (fun x => f x * g x) (fun x => f x * h x)

/-- A finite sum can be moved out of the first inner-product argument. -/
theorem rawInner_sum_left (F : Fin d → S.RawVector) (g : S.RawVector) :
    S.rawInner (∑ i, F i) g = ∑ i, S.rawInner (F i) g := by
  classical
  unfold rawInner rawAvg
  simp only [Finset.sum_apply, Finset.sum_mul, Finset.sum_div]
  rw [Finset.sum_comm]

/-- A finite sum can be moved out of the second inner-product argument. -/
theorem rawInner_sum_right (f : S.RawVector) (G : Fin d → S.RawVector) :
    S.rawInner f (∑ i, G i) = ∑ i, S.rawInner f (G i) := by
  classical
  unfold rawInner rawAvg
  simp only [Finset.sum_apply, Finset.mul_sum, Finset.sum_div]
  rw [Finset.sum_comm]

/-- Inner product of constant vectors. -/
theorem rawInner_const_const (a b : ℝ) :
    S.rawInner (S.constVec a) (S.constVec b) = a * b := by
  unfold rawInner
  simpa [constVec] using S.rawAvg_const (a * b)

/-- Inner product of a constant and one coordinate lift. -/
theorem rawInner_const_lift (a : ℝ) (i : Fin d)
    (g : {x : Fin B // x ∈ S.orbit i} → ℝ) :
    S.rawInner (S.constVec a) (S.lift i g) = a * S.coordAvg i g := by
  unfold rawInner
  rw [show (fun x => S.constVec a x * S.lift i g x) =
      a • S.lift i g by
        funext x
        simp [constVec, lift]]
  rw [S.rawAvg_smul, S.rawAvg_lift]

/-- Symmetric version of `rawInner_const_lift`. -/
theorem rawInner_lift_const (a : ℝ) (i : Fin d)
    (g : {x : Fin B // x ∈ S.orbit i} → ℝ) :
    S.rawInner (S.lift i g) (S.constVec a) = a * S.coordAvg i g := by
  unfold rawInner
  rw [show (fun x => S.lift i g x * S.constVec a x) =
      a • S.lift i g by
        funext x
        simp [constVec, lift, mul_comm]]
  rw [S.rawAvg_smul, S.rawAvg_lift]

/-- Inner product of two distinct coordinate lifts. -/
theorem rawInner_lift_lift (i j : Fin d) (hji : j ≠ i)
    (g : {a : Fin B // a ∈ S.orbit i} → ℝ)
    (h : {b : Fin B // b ∈ S.orbit j} → ℝ) :
    S.rawInner (S.lift i g) (S.lift j h) =
      S.coordAvg i g * S.coordAvg j h := by
  exact S.rawAvg_mul_lift i j hji g h

/-- Center a function on one coordinate orbit. -/
noncomputable def centered (i : Fin d)
    (g : {a : Fin B // a ∈ S.orbit i} → ℝ) :
    {a : Fin B // a ∈ S.orbit i} → ℝ :=
  fun a => g a - S.coordAvg i g

/-- A centered coordinate function has mean zero. -/
theorem coordAvg_centered (i : Fin d)
    (g : {a : Fin B // a ∈ S.orbit i} → ℝ) :
    S.coordAvg i (S.centered i g) = 0 := by
  change ((∑ a, (g a - (∑ b, g b) / ((S.orbit i).card : ℝ))) /
    ((S.orbit i).card : ℝ)) = 0
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp [S.orbit_card_ne_zero i] <;> ring

/-- Synthesis of additive coordinate functions. -/
noncomputable def synth
    (g : ∀ i : Fin d, {a : Fin B // a ∈ S.orbit i} → ℝ) : S.RawVector :=
  fun x => ∑ i, g i (x i)

/-- Sum of the coordinate means. -/
noncomputable def totalMean
    (g : ∀ i : Fin d, {a : Fin B // a ∈ S.orbit i} → ℝ) : ℝ :=
  ∑ i, S.coordAvg i (g i)

/-- Pointwise decomposition into one constant and centered coordinate terms. -/
theorem synth_eq_const_add_centered
    (g : ∀ i : Fin d, {a : Fin B // a ∈ S.orbit i} → ℝ) :
    S.synth g = S.constVec (S.totalMean g) +
      ∑ i, S.lift i (S.centered i (g i)) := by
  classical
  funext x
  unfold synth constVec totalMean lift centered
  simp only [Pi.add_apply, Finset.sum_apply]
  rw [← Finset.sum_add_distrib]
  ring_nf

/-- Exact squared-norm decomposition for additive coordinate functions on the
uniform product table. -/
theorem rawNormSq_synth
    (g : ∀ i : Fin d, {a : Fin B // a ∈ S.orbit i} → ℝ) :
    S.rawNormSq (S.synth g) =
      (S.totalMean g) ^ 2 +
        ∑ i, S.rawNormSq (S.lift i (S.centered i (g i))) := by
  classical
  rw [S.synth_eq_const_add_centered g]
  unfold rawNormSq
  rw [S.rawInner_add_left, S.rawInner_add_right, S.rawInner_add_right]
  have hcrossL :
      (∑ i, S.rawInner (S.lift i (S.centered i (g i)))
        (S.constVec (S.totalMean g))) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [S.rawInner_lift_const, S.coordAvg_centered]
    simp
  have hcrossR :
      (∑ i, S.rawInner (S.constVec (S.totalMean g))
        (S.lift i (S.centered i (g i)))) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [S.rawInner_const_lift, S.coordAvg_centered]
    simp
  have hdouble :
      (∑ i, ∑ j, S.rawInner (S.lift i (S.centered i (g i)))
        (S.lift j (S.centered j (g j)))) =
      ∑ i, S.rawNormSq (S.lift i (S.centered i (g i))) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single i]
    · rfl
    · intro j _ hji
      rw [S.rawInner_lift_lift j i (Ne.symm hji)]
      simp [S.coordAvg_centered]
    · simp
  have hConstSum :
      S.rawInner (S.constVec (S.totalMean g))
        (∑ i, S.lift i (S.centered i (g i))) = 0 := by
    rw [S.rawInner_sum_right]
    exact hcrossR
  have hSumConst :
      S.rawInner (∑ i, S.lift i (S.centered i (g i)))
        (S.constVec (S.totalMean g)) = 0 := by
    rw [S.rawInner_sum_left]
    exact hcrossL
  have hSumSum :
      S.rawInner (∑ i, S.lift i (S.centered i (g i)))
        (∑ j, S.lift j (S.centered j (g j))) =
      ∑ i, ∑ j, S.rawInner (S.lift i (S.centered i (g i)))
        (S.lift j (S.centered j (g j))) := by
    rw [S.rawInner_sum_left]
    apply Finset.sum_congr rfl
    intro i _
    rw [S.rawInner_sum_right]
  rw [hConstSum, hSumConst, hSumSum, hdouble, S.rawInner_const_const]
  ring

end SectorData
end IndependentMatchingBlockOccupancy
