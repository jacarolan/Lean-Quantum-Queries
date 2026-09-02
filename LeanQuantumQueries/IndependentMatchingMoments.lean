import LeanQuantumQueries.IndependentMatchingProductThree
import LeanQuantumQueries.IndependentMatchingIdeal

open scoped BigOperators

namespace IndependentMatchingBlockOccupancy
namespace SectorData

variable {d B : ℕ} (S : SectorData d B)

private theorem remaining₂_nonemptyV (i j : Fin d) :
    Nonempty (S.Remaining₂ i j) := by
  classical
  refine ⟨fun k => ?_⟩
  exact ⟨(S.orbit_nonempty k.1).choose,
    (S.orbit_nonempty k.1).choose_spec⟩

private theorem remaining₃_nonemptyV (i j k : Fin d) :
    Nonempty (S.Remaining₃ i j k) := by
  classical
  refine ⟨fun l => ?_⟩
  exact ⟨(S.orbit_nonempty l.1).choose,
    (S.orbit_nonempty l.1).choose_spec⟩

private theorem remaining₂_card_ne_zeroV (i j : Fin d) :
    (Fintype.card (S.Remaining₂ i j) : ℝ) ≠ 0 := by
  haveI := S.remaining₂_nonemptyV i j
  exact_mod_cast Fintype.card_ne_zero

private theorem remaining₃_card_ne_zeroV (i j k : Fin d) :
    (Fintype.card (S.Remaining₃ i j k) : ℝ) ≠ 0 := by
  haveI := S.remaining₃_nonemptyV i j k
  exact_mod_cast Fintype.card_ne_zero

/-- Normalized expectation of a function of two distinct coordinates. -/
theorem rawAvg_two_coordinatesV (i j : Fin d) (hji : j ≠ i)
    (F : {a : Fin B // a ∈ S.orbit i} →
      {b : Fin B // b ∈ S.orbit j} → ℝ) :
    S.rawAvg (fun x => F (x i) (x j)) =
      (∑ a, ∑ b, F a b) /
        (((S.orbit i).card : ℝ) * (S.orbit j).card) := by
  unfold rawAvg
  rw [S.sum_two_coordinates i j hji F,
    S.card_rawPlacement₂ i j hji]
  rw [show
      (Fintype.card (S.Remaining₂ i j) : ℝ) *
          (S.orbit i).card * (S.orbit j).card =
        (Fintype.card (S.Remaining₂ i j) : ℝ) *
          (((S.orbit i).card : ℝ) * (S.orbit j).card) by ring]
  simpa using mul_div_mul_left
    (∑ a, ∑ b, F a b)
    (((S.orbit i).card : ℝ) * (S.orbit j).card)
    (S.remaining₂_card_ne_zeroV i j)

/-- Normalized expectation of a function of three distinct coordinates. -/
theorem rawAvg_three_coordinatesV (i j k : Fin d)
    (hji : j ≠ i) (hki : k ≠ i) (hkj : k ≠ j)
    (F : {a : Fin B // a ∈ S.orbit i} →
      {b : Fin B // b ∈ S.orbit j} →
      {c : Fin B // c ∈ S.orbit k} → ℝ) :
    S.rawAvg (fun x => F (x i) (x j) (x k)) =
      (∑ a, ∑ b, ∑ c, F a b c) /
        (((S.orbit i).card : ℝ) * (S.orbit j).card *
          (S.orbit k).card) := by
  unfold rawAvg
  rw [S.sum_three_coordinates i j k hji hki hkj F,
    S.card_rawPlacement₃ i j k hji hki hkj]
  rw [show
      (Fintype.card (S.Remaining₃ i j k) : ℝ) *
          (S.orbit i).card * (S.orbit j).card * (S.orbit k).card =
        (Fintype.card (S.Remaining₃ i j k) : ℝ) *
          (((S.orbit i).card : ℝ) * (S.orbit j).card *
            (S.orbit k).card) by ring]
  simpa using mul_div_mul_left
    (∑ a, ∑ b, ∑ c, F a b c)
    (((S.orbit i).card : ℝ) * (S.orbit j).card *
      (S.orbit k).card)
    (S.remaining₃_card_ne_zeroV i j k)

end SectorData
end IndependentMatchingBlockOccupancy
