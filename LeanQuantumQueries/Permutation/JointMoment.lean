import LeanQuantumQueries.Permutation.CompletionCount

/-!
# Exact joint moments of random-permutation extension indicators

For partial permutations `f` and `g`, this file formalizes the elementary
identity

  E_π [1[f ⊆ π] 1[g ⊆ π]]
    = 1 / N.descFactorial |f.graph ∪ g.graph|

when the two partial permutations are compatible, and zero otherwise.  This is
the exact matrix-entry calculation behind the partial-bijection moment method;
no representation theory is used.
-/

namespace LeanQuantumQueries.Permutation
namespace PartialPerm

open Equiv Equiv.Perm
open scoped BigOperators

variable {N r s : ℕ}

/-- Compatibility is symmetric. -/
theorem compatible_symm (f : PartialPerm N r) (g : PartialPerm N s)
    (h : f.Compatible g) : g.Compatible f := by
  constructor
  · intro x y₁ y₂ hg hf
    exact (h.1 hf hg).symm
  · intro x₁ x₂ y hg hf
    exact (h.2 hf hg).symm

/-- Every partial permutation is compatible with itself. -/
theorem compatible_refl (f : PartialPerm N r) : f.Compatible f := by
  exact ⟨f.left_unique, f.right_unique⟩

/-- Two partial permutations admitting a common total extension are
compatible. -/
theorem compatible_of_common_extension
    (f : PartialPerm N r) (g : PartialPerm N s)
    {π : Equiv.Perm (Fin N)}
    (hf : f.Extends π) (hg : g.Extends π) : f.Compatible g := by
  constructor
  · intro x y₁ y₂ h₁ h₂
    exact (hf (x, y₁) h₁).symm.trans (hg (x, y₂) h₂)
  · intro x₁ x₂ y h₁ h₂
    apply π.injective
    exact (hf (x₁, y) h₁).trans (hg (x₂, y) h₂).symm

/-- The union of two compatible partial permutations. -/
def compatibleUnion
    (f : PartialPerm N r) (g : PartialPerm N s)
    (h : f.Compatible g) :
    PartialPerm N ((f.graph ∪ g.graph).card) := by
  refine ⟨f.graph ∪ g.graph, ?_⟩
  refine ⟨rfl, ?_, ?_⟩
  · intro x y₁ y₂ h₁ h₂
    rw [Finset.mem_union] at h₁ h₂
    rcases h₁ with hf₁ | hg₁ <;> rcases h₂ with hf₂ | hg₂
    · exact f.left_unique hf₁ hf₂
    · exact h.1 hf₁ hg₂
    · exact (h.1 hf₂ hg₁).symm
    · exact g.left_unique hg₁ hg₂
  · intro x₁ x₂ y h₁ h₂
    rw [Finset.mem_union] at h₁ h₂
    rcases h₁ with hf₁ | hg₁ <;> rcases h₂ with hf₂ | hg₂
    · exact f.right_unique hf₁ hf₂
    · exact h.2 hf₁ hg₂
    · exact (h.2 hf₂ hg₁).symm
    · exact g.right_unique hg₁ hg₂

@[simp] theorem graph_compatibleUnion
    (f : PartialPerm N r) (g : PartialPerm N s)
    (h : f.Compatible g) :
    (f.compatibleUnion g h).graph = f.graph ∪ g.graph := rfl

/-- Extending the compatible union is equivalent to extending both pieces. -/
theorem extends_compatibleUnion_iff
    (f : PartialPerm N r) (g : PartialPerm N s)
    (h : f.Compatible g) (π : Equiv.Perm (Fin N)) :
    (f.compatibleUnion g h).Extends π ↔ f.Extends π ∧ g.Extends π := by
  constructor
  · intro hu
    constructor
    · intro e he
      apply hu e
      exact Finset.mem_union_left g.graph he
    · intro e he
      apply hu e
      exact Finset.mem_union_right f.graph he
  · rintro ⟨hf, hg⟩ e he
    rw [graph_compatibleUnion, Finset.mem_union] at he
    rcases he with he | he
    · exact hf e he
    · exact hg e he

/-- Common completions are exactly completions of the compatible union. -/
noncomputable def commonCompletionEquivUnion
    (f : PartialPerm N r) (g : PartialPerm N s)
    (h : f.Compatible g) :
    {π : Equiv.Perm (Fin N) // f.Extends π ∧ g.Extends π} ≃
      {π : Equiv.Perm (Fin N) // (f.compatibleUnion g h).Extends π} where
  toFun π := ⟨π.1, (f.extends_compatibleUnion_iff g h π.1).2 π.2⟩
  invFun π := ⟨π.1, (f.extends_compatibleUnion_iff g h π.1).1 π.2⟩
  left_inv π := by
    apply Subtype.ext
    rfl
  right_inv π := by
    apply Subtype.ext
    rfl

/-- Exact number of common completions in the compatible case. -/
theorem card_common_completions_of_compatible
    (f : PartialPerm N r) (g : PartialPerm N s)
    (h : f.Compatible g) :
    Fintype.card {π : Equiv.Perm (Fin N) // f.Extends π ∧ g.Extends π} =
      Nat.factorial (N - (f.graph ∪ g.graph).card) := by
  classical
  calc
    Fintype.card {π : Equiv.Perm (Fin N) // f.Extends π ∧ g.Extends π} =
        Fintype.card
          {π : Equiv.Perm (Fin N) // (f.compatibleUnion g h).Extends π} :=
      Fintype.card_congr (f.commonCompletionEquivUnion g h)
    _ = Nat.factorial (N - (f.graph ∪ g.graph).card) := by
      simpa using (card_completions (f.compatibleUnion g h))

/-- Incompatible partial permutations have no common completion. -/
theorem card_common_completions_of_incompatible
    (f : PartialPerm N r) (g : PartialPerm N s)
    (h : ¬f.Compatible g) :
    Fintype.card {π : Equiv.Perm (Fin N) // f.Extends π ∧ g.Extends π} = 0 := by
  classical
  letI : IsEmpty {π : Equiv.Perm (Fin N) // f.Extends π ∧ g.Extends π} :=
    ⟨fun π => h (f.compatible_of_common_extension g π.2.1 π.2.2)⟩
  exact Fintype.card_eq_zero

/-- Complete common-completion count, including the incompatible case. -/
theorem card_common_completions
    (f : PartialPerm N r) (g : PartialPerm N s) :
    Fintype.card {π : Equiv.Perm (Fin N) // f.Extends π ∧ g.Extends π} =
      if f.Compatible g then
        Nat.factorial (N - (f.graph ∪ g.graph).card)
      else 0 := by
  classical
  by_cases h : f.Compatible g
  · simp [h, f.card_common_completions_of_compatible g h]
  · simp [h, f.card_common_completions_of_incompatible g h]

/-- A compatible union contains at most `N` graph edges. -/
theorem card_union_graph_le
    (f : PartialPerm N r) (g : PartialPerm N s)
    (h : f.Compatible g) :
    (f.graph ∪ g.graph).card ≤ N := by
  have hcard := Finset.card_le_univ (f.compatibleUnion g h).dom
  simpa using hcard

/-- The extension indicator of a partial permutation. -/
noncomputable def extensionIndicator
    (f : PartialPerm N r) (π : Equiv.Perm (Fin N)) : ℚ :=
  if f.Extends π then 1 else 0

/-- The normalized joint moment of two extension indicators under a uniformly
random total permutation. -/
noncomputable def jointMoment
    (f : PartialPerm N r) (g : PartialPerm N s) : ℚ :=
  (∑ π : Equiv.Perm (Fin N), f.extensionIndicator π * g.extensionIndicator π) /
    Fintype.card (Equiv.Perm (Fin N))

/-- The numerator of the joint moment is the number of common completions. -/
theorem sum_extensionIndicator_mul
    (f : PartialPerm N r) (g : PartialPerm N s) :
    ∑ π : Equiv.Perm (Fin N),
        f.extensionIndicator π * g.extensionIndicator π =
      (Fintype.card
        {π : Equiv.Perm (Fin N) // f.Extends π ∧ g.Extends π} : ℚ) := by
  classical
  rw [Fintype.card_subtype]
  rw [← Finset.sum_boole (R := ℚ)
    (fun π : Equiv.Perm (Fin N) => f.Extends π ∧ g.Extends π) Finset.univ]
  apply Finset.sum_congr rfl
  intro π _
  by_cases hf : f.Extends π <;> by_cases hg : g.Extends π <;>
    simp [extensionIndicator, hf, hg]

/-- Exact factorial-ratio form of the joint moment in the compatible case. -/
theorem jointMoment_of_compatible
    (f : PartialPerm N r) (g : PartialPerm N s)
    (h : f.Compatible g) :
    f.jointMoment g =
      (Nat.factorial (N - (f.graph ∪ g.graph).card) : ℚ) /
        Nat.factorial N := by
  classical
  rw [jointMoment, f.sum_extensionIndicator_mul g,
    f.card_common_completions_of_compatible g h, Fintype.card_perm]
  simp

/-- The joint moment vanishes in the incompatible case. -/
theorem jointMoment_of_incompatible
    (f : PartialPerm N r) (g : PartialPerm N s)
    (h : ¬f.Compatible g) :
    f.jointMoment g = 0 := by
  classical
  rw [jointMoment, f.sum_extensionIndicator_mul g,
    f.card_common_completions_of_incompatible g h]
  simp

/-- Convert the factorial ratio to the reciprocal descending factorial. -/
theorem factorial_ratio_eq_inv_descFactorial
    {u : ℕ} (h : u ≤ N) :
    (Nat.factorial (N - u) : ℚ) / Nat.factorial N =
      1 / (N.descFactorial u : ℚ) := by
  have hmulNat :
      Nat.factorial (N - u) * N.descFactorial u = Nat.factorial N :=
    Nat.factorial_mul_descFactorial h
  have hmulRat :
      (Nat.factorial (N - u) : ℚ) * (N.descFactorial u : ℚ) =
        (Nat.factorial N : ℚ) := by
    exact_mod_cast hmulNat
  have hfac : (Nat.factorial N : ℚ) ≠ 0 := by positivity
  have hdesc : (N.descFactorial u : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt ((Nat.descFactorial_pos).2 h))
  field_simp [hfac, hdesc]
  exact hmulRat

/-- The key matrix-entry identity: compatible partial permutations have joint
moment `1 / (N)_{|f ∪ g|}`. -/
theorem jointMoment_of_compatible_eq_inv_descFactorial
    (f : PartialPerm N r) (g : PartialPerm N s)
    (h : f.Compatible g) :
    f.jointMoment g =
      1 / (N.descFactorial ((f.graph ∪ g.graph).card) : ℚ) := by
  rw [f.jointMoment_of_compatible g h,
    factorial_ratio_eq_inv_descFactorial (f.card_union_graph_le g h)]

/-- Complete exact joint-moment identity, including incompatibility. -/
theorem jointMoment_eq
    (f : PartialPerm N r) (g : PartialPerm N s) :
    f.jointMoment g =
      if f.Compatible g then
        1 / (N.descFactorial ((f.graph ∪ g.graph).card) : ℚ)
      else 0 := by
  classical
  by_cases h : f.Compatible g
  · simp [h, f.jointMoment_of_compatible_eq_inv_descFactorial g h]
  · simp [h, f.jointMoment_of_incompatible g h]

/-- Diagonal specialization: a size-`r` partial permutation is extended with
probability `1 / (N)_r`. -/
theorem jointMoment_self (f : PartialPerm N r) :
    f.jointMoment f = 1 / (N.descFactorial r : ℚ) := by
  have h := f.jointMoment_of_compatible_eq_inv_descFactorial f f.compatible_refl
  simpa using h

end PartialPerm
end LeanQuantumQueries.Permutation
