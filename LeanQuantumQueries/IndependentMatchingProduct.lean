import LeanQuantumQueries.IndependentMatchingBlockOccupancy

namespace IndependentMatchingBlockOccupancy
namespace SectorData

variable {d B : ℕ} (S : SectorData d B)

/-- The coordinates other than `i`. -/
abbrev Except (i : Fin d) := {j : Fin d // j ≠ i}

/-- Product of all coordinate orbits except coordinate `i`. -/
abbrev Remaining (i : Fin d) :=
  ∀ j : Except i, {a : Fin B // a ∈ S.orbit j.1}

/-- Insert a fixed value at coordinate `i`. -/
noncomputable def insertAt (i : Fin d)
    (a : {a : Fin B // a ∈ S.orbit i}) (y : S.Remaining i) :
    S.RawPlacement := fun j => by
  classical
  by_cases h : j = i
  · subst j
    exact a
  · exact y ⟨j, h⟩

@[simp] theorem insertAt_same (i : Fin d)
    (a : {a : Fin B // a ∈ S.orbit i}) (y : S.Remaining i) :
    S.insertAt i a y i = a := by
  simp [insertAt]

@[simp] theorem insertAt_ne (i j : Fin d) (h : j ≠ i)
    (a : {a : Fin B // a ∈ S.orbit i}) (y : S.Remaining i) :
    S.insertAt i a y j = y ⟨j, h⟩ := by
  simp [insertAt, h]

/-- Splitting a product placement into one fixed coordinate and all remaining
coordinates. -/
noncomputable def fixedFiberEquiv (i : Fin d)
    (a : {a : Fin B // a ∈ S.orbit i}) :
    {x : S.RawPlacement // x i = a} ≃ S.Remaining i where
  toFun x j := x.1 j.1
  invFun y := ⟨S.insertAt i a y, S.insertAt_same i a y⟩
  left_inv := by
    intro x
    apply Subtype.ext
    funext j
    by_cases h : j = i
    · subst j
      simpa using x.2.symm
    · exact S.insertAt_ne i j h a (fun k => x.1 k.1)
  right_inv := by
    intro y
    funext j
    simpa using S.insertAt_ne i j.1 j.2 a y

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

/-- Insert two fixed coordinate values. -/
noncomputable def insertAt₂ (i j : Fin d)
    (a : {a : Fin B // a ∈ S.orbit i})
    (b : {b : Fin B // b ∈ S.orbit j})
    (y : S.Remaining₂ i j) : S.RawPlacement := fun k => by
  classical
  by_cases hki : k = i
  · subst k
    exact a
  · by_cases hkj : k = j
    · subst k
      exact b
    · exact y ⟨k, hki, hkj⟩

@[simp] theorem insertAt₂_left (i j : Fin d) (hji : j ≠ i)
    (a : {a : Fin B // a ∈ S.orbit i})
    (b : {b : Fin B // b ∈ S.orbit j})
    (y : S.Remaining₂ i j) : S.insertAt₂ i j a b y i = a := by
  simp [insertAt₂]

@[simp] theorem insertAt₂_right (i j : Fin d) (hji : j ≠ i)
    (a : {a : Fin B // a ∈ S.orbit i})
    (b : {b : Fin B // b ∈ S.orbit j})
    (y : S.Remaining₂ i j) : S.insertAt₂ i j a b y j = b := by
  simp [insertAt₂, hji]

@[simp] theorem insertAt₂_ne (i j k : Fin d) (hki : k ≠ i) (hkj : k ≠ j)
    (a : {a : Fin B // a ∈ S.orbit i})
    (b : {b : Fin B // b ∈ S.orbit j})
    (y : S.Remaining₂ i j) :
    S.insertAt₂ i j a b y k = y ⟨k, hki, hkj⟩ := by
  simp [insertAt₂, hki, hkj]

/-- Splitting a product placement after two distinct coordinates are fixed. -/
noncomputable def pairFiberEquiv (i j : Fin d) (hji : j ≠ i)
    (a : {a : Fin B // a ∈ S.orbit i})
    (b : {b : Fin B // b ∈ S.orbit j}) :
    {x : S.RawPlacement // x i = a ∧ x j = b} ≃ S.Remaining₂ i j where
  toFun x k := x.1 k.1
  invFun y := ⟨S.insertAt₂ i j a b y,
    ⟨S.insertAt₂_left i j hji a b y, S.insertAt₂_right i j hji a b y⟩⟩
  left_inv := by
    intro x
    apply Subtype.ext
    funext k
    by_cases hki : k = i
    · subst k
      simpa using x.2.1.symm
    · by_cases hkj : k = j
      · subst k
        simpa using x.2.2.symm
      · exact S.insertAt₂_ne i j k hki hkj a b (fun l => x.1 l.1)
  right_inv := by
    intro y
    funext k
    simpa using S.insertAt₂_ne i j k.1 k.2.1 k.2.2 a b y

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
