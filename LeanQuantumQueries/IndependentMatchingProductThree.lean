import LeanQuantumQueries.IndependentMatchingProduct

namespace IndependentMatchingBlockOccupancy
namespace SectorData

variable {d B : ℕ} (S : SectorData d B)

/-- Coordinates other than three selected indices. -/
abbrev Except₃ (i j k : Fin d) :=
  {l : Fin d // l ≠ i ∧ l ≠ j ∧ l ≠ k}

/-- Product of all coordinate orbits except three selected indices. -/
abbrev Remaining₃ (i j k : Fin d) :=
  ∀ l : S.Except₃ i j k, {a : Fin B // a ∈ S.orbit l.1}

/-- Insert three fixed coordinate values. -/
noncomputable def insertAt₃ (i j k : Fin d)
    (a : {a : Fin B // a ∈ S.orbit i})
    (b : {b : Fin B // b ∈ S.orbit j})
    (c : {c : Fin B // c ∈ S.orbit k})
    (y : S.Remaining₃ i j k) : S.RawPlacement := fun l => by
  classical
  by_cases hli : l = i
  · subst l
    exact a
  · by_cases hlj : l = j
    · subst l
      exact b
    · by_cases hlk : l = k
      · subst l
        exact c
      · exact y ⟨l, hli, hlj, hlk⟩

@[simp] theorem insertAt₃_first (i j k : Fin d)
    (a : {a : Fin B // a ∈ S.orbit i})
    (b : {b : Fin B // b ∈ S.orbit j})
    (c : {c : Fin B // c ∈ S.orbit k})
    (y : S.Remaining₃ i j k) :
    S.insertAt₃ i j k a b c y i = a := by
  simp [insertAt₃]

@[simp] theorem insertAt₃_second (i j k : Fin d) (hji : j ≠ i)
    (a : {a : Fin B // a ∈ S.orbit i})
    (b : {b : Fin B // b ∈ S.orbit j})
    (c : {c : Fin B // c ∈ S.orbit k})
    (y : S.Remaining₃ i j k) :
    S.insertAt₃ i j k a b c y j = b := by
  simp [insertAt₃, hji]

@[simp] theorem insertAt₃_third (i j k : Fin d)
    (hki : k ≠ i) (hkj : k ≠ j)
    (a : {a : Fin B // a ∈ S.orbit i})
    (b : {b : Fin B // b ∈ S.orbit j})
    (c : {c : Fin B // c ∈ S.orbit k})
    (y : S.Remaining₃ i j k) :
    S.insertAt₃ i j k a b c y k = c := by
  simp [insertAt₃, hki, hkj]

@[simp] theorem insertAt₃_other (i j k l : Fin d)
    (hli : l ≠ i) (hlj : l ≠ j) (hlk : l ≠ k)
    (a : {a : Fin B // a ∈ S.orbit i})
    (b : {b : Fin B // b ∈ S.orbit j})
    (c : {c : Fin B // c ∈ S.orbit k})
    (y : S.Remaining₃ i j k) :
    S.insertAt₃ i j k a b c y l = y ⟨l, hli, hlj, hlk⟩ := by
  simp [insertAt₃, hli, hlj, hlk]

/-- A three-coordinate fiber is equivalent to the remaining product. -/
noncomputable def tripleFiberEquiv (i j k : Fin d)
    (hji : j ≠ i) (hki : k ≠ i) (hkj : k ≠ j)
    (a : {a : Fin B // a ∈ S.orbit i})
    (b : {b : Fin B // b ∈ S.orbit j})
    (c : {c : Fin B // c ∈ S.orbit k}) :
    {x : S.RawPlacement // x i = a ∧ x j = b ∧ x k = c} ≃
      S.Remaining₃ i j k where
  toFun x l := x.1 l.1
  invFun y := ⟨S.insertAt₃ i j k a b c y,
    ⟨S.insertAt₃_first i j k a b c y,
      S.insertAt₃_second i j k hji a b c y,
      S.insertAt₃_third i j k hki hkj a b c y⟩⟩
  left_inv := by
    intro x
    apply Subtype.ext
    funext l
    change S.insertAt₃ i j k a b c (fun r => x.1 r.1) l = x.1 l
    by_cases hli : l = i
    · subst l
      rw [S.insertAt₃_first]
      exact x.2.1.symm
    · by_cases hlj : l = j
      · subst l
        rw [S.insertAt₃_second i j k hji]
        exact x.2.2.1.symm
      · by_cases hlk : l = k
        · subst l
          rw [S.insertAt₃_third i j k hki hkj]
          exact x.2.2.2.symm
        · exact S.insertAt₃_other i j k l hli hlj hlk a b c
            (fun r => x.1 r.1)
  right_inv := by
    intro y
    funext l
    change S.insertAt₃ i j k a b c y l.1 = y l
    simpa using S.insertAt₃_other i j k l.1
      l.2.1 l.2.2.1 l.2.2.2 a b c y

/-- Cardinality of a fixed three-coordinate fiber. -/
theorem card_tripleFiber (i j k : Fin d)
    (hji : j ≠ i) (hki : k ≠ i) (hkj : k ≠ j)
    (a : {a : Fin B // a ∈ S.orbit i})
    (b : {b : Fin B // b ∈ S.orbit j})
    (c : {c : Fin B // c ∈ S.orbit k}) :
    Fintype.card
      {x : S.RawPlacement // x i = a ∧ x j = b ∧ x k = c} =
      Fintype.card (S.Remaining₃ i j k) := by
  exact Fintype.card_congr
    (S.tripleFiberEquiv i j k hji hki hkj a b c)

/-- Sum a function of three distinct coordinates over the product table. -/
theorem sum_three_coordinates (i j k : Fin d)
    (hji : j ≠ i) (hki : k ≠ i) (hkj : k ≠ j)
    (F : {a : Fin B // a ∈ S.orbit i} →
      {b : Fin B // b ∈ S.orbit j} →
      {c : Fin B // c ∈ S.orbit k} → ℝ) :
    (∑ x : S.RawPlacement, F (x i) (x j) (x k)) =
      (Fintype.card (S.Remaining₃ i j k) : ℝ) *
        ∑ a, ∑ b, ∑ c, F a b c := by
  classical
  rw [← Fintype.sum_fiberwise
    (fun x : S.RawPlacement => ((x i, x j), x k))
    (fun x => F (x i) (x j) (x k))]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  have hconst : ∀ x :
      {x : S.RawPlacement // ((x i, x j), x k) = ((a, b), c)},
      F (x.1 i) (x.1 j) (x.1 k) = F a b c := by
    intro x
    exact congrArg₃ F
      (congrArg (fun p => p.1.1) x.2)
      (congrArg (fun p => p.1.2) x.2)
      (congrArg Prod.snd x.2)
  simp_rw [hconst]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 1
  let e :
      {x : S.RawPlacement // ((x i, x j), x k) = ((a, b), c)} ≃
      {x : S.RawPlacement // x i = a ∧ x j = b ∧ x k = c} :=
    Equiv.subtypeEquivRight fun x => by
      constructor
      · intro h
        exact ⟨congrArg (fun p => p.1.1) h,
          congrArg (fun p => p.1.2) h,
          congrArg Prod.snd h⟩
      · rintro ⟨hi, hj, hk⟩
        exact Prod.ext (Prod.ext hi hj) hk
  rw [Fintype.card_congr e,
    S.card_tripleFiber i j k hji hki hkj a b c]

/-- Three-coordinate cardinal factorization. -/
theorem card_rawPlacement₃ (i j k : Fin d)
    (hji : j ≠ i) (hki : k ≠ i) (hkj : k ≠ j) :
    (Fintype.card S.RawPlacement : ℝ) =
      (Fintype.card (S.Remaining₃ i j k) : ℝ) *
        (S.orbit i).card * (S.orbit j).card * (S.orbit k).card := by
  have h := S.sum_three_coordinates i j k hji hki hkj
    (fun _ _ _ => (1 : ℝ))
  simpa [mul_assoc] using h

end SectorData
end IndependentMatchingBlockOccupancy
