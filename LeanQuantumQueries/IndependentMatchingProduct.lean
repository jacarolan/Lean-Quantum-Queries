import LeanQuantumQueries.IndependentMatchingBlockOccupancy

namespace IndependentMatchingBlockOccupancy
namespace SectorData

variable {d B : ℕ} (S : SectorData d B)

/-- The coordinates other than `i`. -/
abbrev Except (i : Fin d) := {j : Fin d // j ≠ i}

/-- Product of all coordinate orbits except coordinate `i`. -/
abbrev Remaining (i : Fin d) :=
  ∀ j : Except i, {a : Fin B // a ∈ S.orbit j.1}

/-- Splitting a product placement into one fixed coordinate and all remaining
coordinates. -/
noncomputable def fixedFiberEquiv (i : Fin d)
    (a : {a : Fin B // a ∈ S.orbit i}) :
    {x : S.RawPlacement // x i = a} ≃ S.Remaining i := by
  classical
  let forward : {x : S.RawPlacement // x i = a} → S.Remaining i :=
    fun x j => x.1 j.1
  let backward : S.Remaining i → {x : S.RawPlacement // x i = a} := fun y => by
    let x : S.RawPlacement := fun j => by
      by_cases h : j = i
      · subst j
        exact a
      · exact y ⟨j, h⟩
    exact ⟨x, by simp [x]⟩
  exact
    { toFun := forward
      invFun := backward
      left_inv := by
        intro x
        apply Subtype.ext
        funext j
        by_cases h : j = i
        · subst j
          simp [backward, x.2]
        · simp [backward, h]
      right_inv := by
        intro y
        funext j
        simp [backward, j.2] }

/-- Cardinality of a fixed product-coordinate fiber. -/
theorem card_fixedFiber (i : Fin d)
    (a : {a : Fin B // a ∈ S.orbit i}) :
    Fintype.card {x : S.RawPlacement // x i = a} =
      Fintype.card (S.Remaining i) := by
  exact Fintype.card_congr (S.fixedFiberEquiv i a)

/-- Summing a function of one coordinate over a finite product. -/
theorem sum_coordinate (i : Fin d)
    (F : {a : Fin B // a ∈ S.orbit i} → ℝ) :
    (∑ x : S.RawPlacement, F (x i)) =
      (Fintype.card (S.Remaining i) : ℝ) * ∑ a, F a := by
  classical
  rw [← Fintype.sum_fiberwise (fun x : S.RawPlacement => x i)
    (fun x => F (x i))]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  have hconst : ∀ x : {x : S.RawPlacement // x i = a}, F (x.1 i) = F a :=
    fun x => congrArg F x.2
  simp_rw [hconst]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, S.card_fixedFiber i a]

/-- Cardinality factorization obtained from `sum_coordinate`. -/
theorem card_rawPlacement (i : Fin d) :
    (Fintype.card S.RawPlacement : ℝ) =
      (Fintype.card (S.Remaining i) : ℝ) * (S.orbit i).card := by
  have h := S.sum_coordinate i (fun _ => (1 : ℝ))
  simpa using h

/-- Coordinates other than `i` and `j`. -/
abbrev Except₂ (i j : Fin d) := {k : Fin d // k ≠ i ∧ k ≠ j}

/-- Product of all coordinate orbits except coordinates `i` and `j`. -/
abbrev Remaining₂ (i j : Fin d) :=
  ∀ k : Except₂ i j, {a : Fin B // a ∈ S.orbit k.1}

/-- Splitting a product placement after two distinct coordinates are fixed. -/
noncomputable def pairFiberEquiv (i j : Fin d) (hji : j ≠ i)
    (a : {a : Fin B // a ∈ S.orbit i})
    (b : {b : Fin B // b ∈ S.orbit j}) :
    {x : S.RawPlacement // x i = a ∧ x j = b} ≃ S.Remaining₂ i j := by
  classical
  let forward : {x : S.RawPlacement // x i = a ∧ x j = b} → S.Remaining₂ i j :=
    fun x k => x.1 k.1
  let backward : S.Remaining₂ i j →
      {x : S.RawPlacement // x i = a ∧ x j = b} := fun y => by
    let x : S.RawPlacement := fun k => by
      by_cases hki : k = i
      · subst k
        exact a
      · by_cases hkj : k = j
        · subst k
          exact b
        · exact y ⟨k, hki, hkj⟩
    exact ⟨x, by constructor <;> simp [x, hji]⟩
  exact
    { toFun := forward
      invFun := backward
      left_inv := by
        intro x
        apply Subtype.ext
        funext k
        by_cases hki : k = i
        · subst k
          simp [backward, x.2.1]
        · by_cases hkj : k = j
          · subst k
            simp [backward, hki, x.2.2]
          · simp [backward, hki, hkj]
      right_inv := by
        intro y
        funext k
        simp [backward, k.2.1, k.2.2] }

/-- Cardinality of a two-coordinate fiber. -/
theorem card_pairFiber (i j : Fin d) (hji : j ≠ i)
    (a : {a : Fin B // a ∈ S.orbit i})
    (b : {b : Fin B // b ∈ S.orbit j}) :
    Fintype.card {x : S.RawPlacement // x i = a ∧ x j = b} =
      Fintype.card (S.Remaining₂ i j) := by
  exact Fintype.card_congr (S.pairFiberEquiv i j hji a b)

/-- Summing a function of two distinct coordinates over the product table. -/
theorem sum_two_coordinates (i j : Fin d) (hji : j ≠ i)
    (F : {a : Fin B // a ∈ S.orbit i} →
      {b : Fin B // b ∈ S.orbit j} → ℝ) :
    (∑ x : S.RawPlacement, F (x i) (x j)) =
      (Fintype.card (S.Remaining₂ i j) : ℝ) *
        ∑ a, ∑ b, F a b := by
  classical
  rw [← Fintype.sum_fiberwise
    (fun x : S.RawPlacement => (x i, x j))
    (fun x => F (x i) (x j))]
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  have hconst : ∀ x : {x : S.RawPlacement // (x i, x j) = (a, b)},
      F (x.1 i) (x.1 j) = F a b := by
    intro x
    exact congrArg₂ F (congrArg Prod.fst x.2) (congrArg Prod.snd x.2)
  simp_rw [hconst]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 1
  let e : {x : S.RawPlacement // (x i, x j) = (a, b)} ≃
      {x : S.RawPlacement // x i = a ∧ x j = b} :=
    Equiv.subtypeEquivRight fun x => Prod.ext_iff
  rw [Fintype.card_congr e, S.card_pairFiber i j hji a b]

/-- Two-coordinate cardinal factorization. -/
theorem card_rawPlacement₂ (i j : Fin d) (hji : j ≠ i) :
    (Fintype.card S.RawPlacement : ℝ) =
      (Fintype.card (S.Remaining₂ i j) : ℝ) *
        (S.orbit i).card * (S.orbit j).card := by
  have h := S.sum_two_coordinates i j hji (fun _ _ => (1 : ℝ))
  simpa [mul_assoc] using h

end SectorData
end IndependentMatchingBlockOccupancy
