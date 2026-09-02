import Mathlib

/-!
# Counterexample to the proposed placement-table reduction

This file is self-contained.  It works in the smallest nontrivial symmetric
injective placement table: two abstract block vertices placed injectively into
four actual blocks.  Block `0` is distinguished.

The proposed reduction used one distinguished rooted row in `H_u`, while its
`H_{¬u}` sector contained all non-distinguished rows and all non-distinguished
alternative-root columns.  It then asserted that a complete alternative-root
family puts the distinguished row into `H_{¬u}`.  The assertion is false.

The same example also disproves the corresponding quotient-occupancy bound:
a nonzero vector in the outside space, after quotienting by the actual
one-row intersection, is supported entirely on occupied placements.
-/

open scoped BigOperators

namespace BlockOccupancyReductionCounterexample

/-- Two block names, required to be different.  This is exactly
`Inj (Fin 2) (Fin 4)`, written as an off-diagonal pair for convenience. -/
abbrev Placement := {p : Fin 4 × Fin 4 // p.1 ≠ p.2}

/-- Real amplitudes on the injective placement table. -/
abbrev TableVector := Placement → ℝ

/-- Distinguished block. -/
def u : Fin 4 := 0

/-- The first coordinate cylinder. -/
def row (a : Fin 4) : TableVector :=
  fun p => if p.1.1 = a then 1 else 0

/-- The second coordinate cylinder. -/
def col (a : Fin 4) : TableVector :=
  fun p => if p.1.2 = a then 1 else 0

/-- The actual outside-cylinder space: all non-`u` rows and columns. -/
noncomputable def outsideSpace : Submodule ℝ TableVector :=
  Submodule.span ℝ
    ({f | ∃ a : Fin 4, a ≠ u ∧ f = row a} ∪
     {f | ∃ a : Fin 4, a ≠ u ∧ f = col a})

/-- A larger coefficient space containing the outside-cylinder span. -/
noncomputable def coefficientSpace : Submodule ℝ TableVector where
  carrier := {f | ∃ φ ψ : Fin 4 → ℝ,
    φ u = 0 ∧ ψ u = 0 ∧ f = fun p => φ p.1.1 + ψ p.1.2}
  zero_mem' := by
    refine ⟨0, 0, ?_, ?_, ?_⟩
    · rfl
    · rfl
    · funext p
      simp
  add_mem' := by
    rintro f g ⟨φ, ψ, hφ, hψ, rfl⟩ ⟨φ', ψ', hφ', hψ', rfl⟩
    refine ⟨φ + φ', ψ + ψ', ?_, ?_, ?_⟩
    · simp [hφ, hφ']
    · simp [hψ, hψ']
    · funext p
      simp only [Pi.add_apply]
      ring
  smul_mem' := by
    rintro c f ⟨φ, ψ, hφ, hψ, rfl⟩
    refine ⟨c • φ, c • ψ, ?_, ?_, ?_⟩
    · simp [hφ]
    · simp [hψ]
    · funext p
      simp only [Pi.smul_apply, smul_eq_mul]
      ring

lemma row_mem_coefficientSpace {a : Fin 4} (ha : a ≠ u) :
    row a ∈ coefficientSpace := by
  let φ : Fin 4 → ℝ := fun b => if b = a then 1 else 0
  refine ⟨φ, 0, ?_, ?_, ?_⟩
  · simp [φ, ha]
  · rfl
  · funext p
    simp [row, φ, eq_comm]

lemma col_mem_coefficientSpace {a : Fin 4} (ha : a ≠ u) :
    col a ∈ coefficientSpace := by
  let ψ : Fin 4 → ℝ := fun b => if b = a then 1 else 0
  refine ⟨0, ψ, ?_, ?_, ?_⟩
  · rfl
  · simp [ψ, ha]
  · funext p
    simp [col, ψ, eq_comm]

lemma outsideSpace_le_coefficientSpace : outsideSpace ≤ coefficientSpace := by
  apply Submodule.span_le.2
  rintro f (hf | hf)
  · rcases hf with ⟨a, ha, rfl⟩
    exact row_mem_coefficientSpace ha
  · rcases hf with ⟨a, ha, rfl⟩
    exact col_mem_coefficientSpace ha

lemma row_mem_outside {a : Fin 4} (ha : a ≠ u) : row a ∈ outsideSpace := by
  apply Submodule.subset_span
  exact Or.inl ⟨a, ha, rfl⟩

lemma col_mem_outside {a : Fin 4} (ha : a ≠ u) : col a ∈ outsideSpace := by
  apply Submodule.subset_span
  exact Or.inr ⟨a, ha, rfl⟩

/-- Three concrete legal placements used by the separation argument. -/
def p02 : Placement := ⟨(0, 2), by decide⟩
def p10 : Placement := ⟨(1, 0), by decide⟩
def p12 : Placement := ⟨(1, 2), by decide⟩

/-- The family of all columns rooted away from `u` is complete on the
`X₀ = u` row, simply by injectivity. -/
def CompleteAlternativeFamily : Prop :=
  ∀ p : Placement, p.1.1 = u → p.1.2 ≠ u

lemma alternative_family_complete : CompleteAlternativeFamily := by
  intro p hp hq
  exact p.2 (hp.trans hq.symm)

/-- The distinguished row is not even in the larger additive coefficient
space, hence not in the outside-cylinder span. -/
lemma distinguished_row_not_mem_coefficientSpace : row u ∉ coefficientSpace := by
  intro h
  rcases h with ⟨φ, ψ, hφ, hψ, hf⟩
  have h02 := congrFun hf p02
  have h10 := congrFun hf p10
  have h12 := congrFun hf p12
  simp [row, u, p02, p10, p12, hφ, hψ] at h02 h10 h12
  linarith

/-- This is the direct counterexample to the proposed exact-rerooting lemma:
the alternative-root family is complete on the distinguished row, but the
row state does not belong to the outside space. -/
theorem complete_but_no_exact_rerooting :
    CompleteAlternativeFamily ∧ row u ∉ outsideSpace := by
  refine ⟨alternative_family_complete, ?_⟩
  intro h
  exact distinguished_row_not_mem_coefficientSpace
    (outsideSpace_le_coefficientSpace h)

/-- The one-dimensional rooted sector used in the proposed reduction. -/
noncomputable def rootLine : Submodule ℝ TableVector where
  carrier := {f | ∃ c : ℝ, f = c • row u}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro f g ⟨c, rfl⟩ ⟨d, rfl⟩
    refine ⟨c + d, ?_⟩
    simp [add_smul]
  smul_mem' := by
    rintro c f ⟨d, rfl⟩
    refine ⟨c * d, ?_⟩
    simp [mul_smul]

/-- In this table the actual intersection of the one rooted line with the
outside space is zero. -/
lemma rootLine_inter_outside_eq_zero {g : TableVector}
    (hgroot : g ∈ rootLine) (hgout : g ∈ outsideSpace) : g = 0 := by
  rcases hgroot with ⟨c, hgc⟩
  have hcoeff : g ∈ coefficientSpace := outsideSpace_le_coefficientSpace hgout
  rcases hcoeff with ⟨φ, ψ, hφ, hψ, hf⟩
  have h02 := congrFun hgc p02
  have h10 := congrFun hgc p10
  have h12 := congrFun hgc p12
  have k02 := congrFun hf p02
  have k10 := congrFun hf p10
  have k12 := congrFun hf p12
  simp [row, u, p02, p10, p12] at h02 h10 h12
  simp [u, p02, p10, p12, hφ, hψ] at k02 k10 k12
  have hc : c = 0 := by linarith
  rw [hgc, hc]
  simp

/-- The zero-sum difference of the two distinguished cylinders. -/
def badVector : TableVector := row u - col u

lemma badVector_expansion :
    badVector =
      (col 1 + col 2 + col 3) - (row 1 + row 2 + row 3) := by
  funext p
  rcases p with ⟨⟨x, y⟩, hxy⟩
  fin_cases x <;> fin_cases y <;>
    simp [badVector, row, col, u] at hxy ⊢

lemma badVector_mem_outside : badVector ∈ outsideSpace := by
  rw [badVector_expansion]
  apply Submodule.sub_mem
  · exact Submodule.add_mem _
      (Submodule.add_mem _ (col_mem_outside (by decide))
        (col_mem_outside (by decide)))
      (col_mem_outside (by decide))
  · exact Submodule.add_mem _
      (Submodule.add_mem _ (row_mem_outside (by decide))
        (row_mem_outside (by decide)))
      (row_mem_outside (by decide))

/-- Unnormalized real inner product. -/
noncomputable def tableInner (f g : TableVector) : ℝ :=
  ∑ p, f p * g p

/-- Membership in `outsideSpace ⊖ (rootLine ∩ outsideSpace)`. -/
def InOneRootOutsideQuotient (f : TableVector) : Prop :=
  f ∈ outsideSpace ∧
    ∀ g, g ∈ rootLine → g ∈ outsideSpace → tableInner f g = 0

lemma badVector_in_one_root_quotient : InOneRootOutsideQuotient badVector := by
  refine ⟨badVector_mem_outside, ?_⟩
  intro g hgroot hgout
  have hg : g = 0 := rootLine_inter_outside_eq_zero hgroot hgout
  subst g
  simp [tableInner]

/-- A placement occupies the distinguished block if either coordinate is `u`. -/
def Occupied (p : Placement) : Prop := p.1.1 = u ∨ p.1.2 = u

noncomputable def occupiedEnergy (f : TableVector) : ℝ :=
  ∑ p, if Occupied p then (f p) ^ 2 else 0

noncomputable def totalEnergy (f : TableVector) : ℝ :=
  ∑ p, (f p) ^ 2

lemma badVector_zero_of_not_occupied (p : Placement) (hp : ¬ Occupied p) :
    badVector p = 0 := by
  have hx : p.1.1 ≠ u := by
    intro h
    exact hp (Or.inl h)
  have hy : p.1.2 ≠ u := by
    intro h
    exact hp (Or.inr h)
  simp [badVector, row, col, hx, hy]

lemma badVector_occupiedEnergy_eq_totalEnergy :
    occupiedEnergy badVector = totalEnergy badVector := by
  classical
  unfold occupiedEnergy totalEnergy
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : Occupied p
  · simp [hp]
  · have hz := badVector_zero_of_not_occupied p hp
    simp [hp, hz]

lemma badVector_totalEnergy_pos : 0 < totalEnergy badVector := by
  classical
  have hsingle : (badVector p02) ^ 2 ≤ totalEnergy badVector := by
    unfold totalEnergy
    exact Finset.single_le_sum (fun p _ => sq_nonneg (badVector p))
      (Finset.mem_univ p02)
  have hp02 : badVector p02 = 1 := by
    simp [badVector, row, col, u, p02]
  rw [hp02] at hsingle
  norm_num at hsingle ⊢
  linarith

/-- The claimed one-root quotient bound already fails for `d = 2`, `M = 4`.
Its advertised coefficient is `(d-1)/(M-2)=1/2`, whereas this vector has
occupied-energy ratio exactly one. -/
theorem one_root_quotient_occupancy_bound_is_false :
    ¬ ∀ f : TableVector,
        InOneRootOutsideQuotient f →
        occupiedEnergy f ≤ (1 / 2 : ℝ) * totalEnergy f := by
  intro hbound
  have h := hbound badVector badVector_in_one_root_quotient
  rw [badVector_occupiedEnergy_eq_totalEnergy] at h
  have hpos := badVector_totalEnergy_pos
  linarith

end BlockOccupancyReductionCounterexample
