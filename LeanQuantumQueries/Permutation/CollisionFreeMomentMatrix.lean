import LeanQuantumQueries.Permutation.OneCallFlatness
import Mathlib.Analysis.Matrix.PosDef

/-!
# The collision-free random-permutation moment matrix

This file defines the actual density matrix obtained by averaging the
collision-free `q`-query permutation states.  Its rows and columns are indexed
by size-`q` partial permutations.  The matrix is a normalized Gram matrix of
extension indicators, hence positive semidefinite.  We also prove that its
trace is one.
-/

namespace LeanQuantumQueries.Permutation
namespace PartialPerm

open scoped BigOperators
open Matrix

variable {N q : ℕ}

/-- The graph embedding `x ↦ (x, π x)` associated with a total permutation. -/
def graphEmbeddingOfPerm (π : Equiv.Perm (Fin N)) : Fin N ↪ Fin N × Fin N where
  toFun x := (x, π x)
  inj' := by
    intro x y h
    exact congrArg Prod.fst h

/-- Restrict a total permutation to a `q`-element subset of its domain. -/
def partialOfSubset
    (π : Equiv.Perm (Fin N)) (S : QSubset N q) : PartialPerm N q := by
  refine ⟨S.1.map (graphEmbeddingOfPerm π), ?_⟩
  refine ⟨by simp [S.2], ?_, ?_⟩
  · intro x y₁ y₂ h₁ h₂
    rw [Finset.mem_map] at h₁ h₂
    rcases h₁ with ⟨a, ha, h₁eq⟩
    rcases h₂ with ⟨b, hb, h₂eq⟩
    have hax : a = x := congrArg Prod.fst h₁eq
    have hbx : b = x := congrArg Prod.fst h₂eq
    have hay₁ : π a = y₁ := congrArg Prod.snd h₁eq
    have hby₂ : π b = y₂ := congrArg Prod.snd h₂eq
    exact hay₁.symm.trans (congrArg π (hax.trans hbx.symm) |>.trans hby₂)
  · intro x₁ x₂ y h₁ h₂
    rw [Finset.mem_map] at h₁ h₂
    rcases h₁ with ⟨a, ha, h₁eq⟩
    rcases h₂ with ⟨b, hb, h₂eq⟩
    have hax₁ : a = x₁ := congrArg Prod.fst h₁eq
    have hbx₂ : b = x₂ := congrArg Prod.fst h₂eq
    have hay : π a = y := congrArg Prod.snd h₁eq
    have hby : π b = y := congrArg Prod.snd h₂eq
    have hab : a = b := π.injective (hay.trans hby.symm)
    exact hax₁.symm.trans (hab.trans hbx₂)

@[simp] theorem mem_partialOfSubset_graph
    (π : Equiv.Perm (Fin N)) (S : QSubset N q) (x y : Fin N) :
    (x, y) ∈ (partialOfSubset π S).graph ↔ x ∈ S.1 ∧ y = π x := by
  constructor
  · intro h
    change (x, y) ∈ S.1.map (graphEmbeddingOfPerm π) at h
    rw [Finset.mem_map] at h
    rcases h with ⟨a, ha, heq⟩
    have hax : a = x := congrArg Prod.fst heq
    have hay : π a = y := congrArg Prod.snd heq
    exact ⟨hax ▸ ha, hay.symm.trans (congrArg π hax)⟩
  · rintro ⟨hx, hy⟩
    change (x, y) ∈ S.1.map (graphEmbeddingOfPerm π)
    rw [Finset.mem_map]
    exact ⟨x, hx, by ext <;> simp [hy, graphEmbeddingOfPerm]⟩

@[simp] theorem partialOfSubset_extends
    (π : Equiv.Perm (Fin N)) (S : QSubset N q) :
    (partialOfSubset π S).Extends π := by
  intro e he
  rcases e with ⟨x, y⟩
  exact ((mem_partialOfSubset_graph π S x y).1 he).2.symm

@[simp] theorem dom_partialOfSubset
    (π : Equiv.Perm (Fin N)) (S : QSubset N q) :
    (partialOfSubset π S).dom = S.1 := by
  ext x
  simp [mem_dom_iff, mem_partialOfSubset_graph]

/-- A partial permutation extended by `π` is determined by its domain. -/
theorem partialOfSubset_dom
    (π : Equiv.Perm (Fin N)) (f : PartialPerm N q)
    (hf : f.Extends π) :
    partialOfSubset π ⟨f.dom, f.card_dom⟩ = f := by
  apply Subtype.ext
  apply Finset.ext
  rintro ⟨x, y⟩
  constructor
  · intro h
    have hmem := (mem_partialOfSubset_graph π ⟨f.dom, f.card_dom⟩ x y).1 h
    rcases (mem_dom_iff f x).1 hmem.1 with ⟨z, hxz⟩
    have hpix : π x = z := hf (x, z) hxz
    have hy : y = z := hmem.2.trans hpix
    exact hy ▸ hxz
  · intro h
    apply (mem_partialOfSubset_graph π ⟨f.dom, f.card_dom⟩ x y).2
    exact ⟨(mem_dom_iff f x).2 ⟨y, h⟩, (hf (x, y) h).symm⟩

/-- The partial permutations extended by a fixed total permutation are in
bijection with its `q`-element domain subsets. -/
noncomputable def extendedPartialEquivQSubset
    (π : Equiv.Perm (Fin N)) :
    {f : PartialPerm N q // f.Extends π} ≃ QSubset N q where
  toFun f := ⟨f.1.dom, f.1.card_dom⟩
  invFun S := ⟨partialOfSubset π S, partialOfSubset_extends π S⟩
  left_inv f := by
    apply Subtype.ext
    exact partialOfSubset_dom π f.1 f.2
  right_inv S := by
    apply Subtype.ext
    exact dom_partialOfSubset π S

/-- Exactly `N.choose q` size-`q` partial permutations are extended by a fixed
permutation. -/
theorem card_extendedPartial
    (π : Equiv.Perm (Fin N)) :
    Fintype.card {f : PartialPerm N q // f.Extends π} = Nat.choose N q := by
  classical
  calc
    Fintype.card {f : PartialPerm N q // f.Extends π} =
        Fintype.card (QSubset N q) :=
      Fintype.card_congr (extendedPartialEquivQSubset π)
    _ = Nat.choose N q := card_qSubset N q

/-- Real-valued extension incidence matrix. -/
noncomputable def extensionIncidence (N q : ℕ) :
    Matrix (Equiv.Perm (Fin N)) (PartialPerm N q) ℝ :=
  fun π f => if f.Extends π then 1 else 0

/-- Normalizing scalar for the collision-free ensemble. -/
noncomputable def momentNormalizer (N q : ℕ) : ℝ :=
  1 / ((Nat.factorial N : ℝ) * Nat.choose N q)

/-- The actual collision-free random-permutation moment matrix. -/
noncomputable def collisionFreeMomentMatrix (N q : ℕ) :
    Matrix (PartialPerm N q) (PartialPerm N q) ℝ :=
  momentNormalizer N q •
    ((extensionIncidence N q)ᴴ * extensionIncidence N q)

/-- The collision-free moment matrix is positive semidefinite. -/
theorem collisionFreeMomentMatrix_posSemidef (N q : ℕ) :
    (collisionFreeMomentMatrix N q).PosSemidef := by
  unfold collisionFreeMomentMatrix
  apply Matrix.PosSemidef.smul
    (Matrix.posSemidef_conjTranspose_mul_self (extensionIncidence N q))
  unfold momentNormalizer
  positivity

/-- The trace of the raw incidence Gram matrix. -/
theorem trace_incidence_gram
    (N q : ℕ) :
    Matrix.trace ((extensionIncidence N q)ᴴ * extensionIncidence N q) =
      (Nat.factorial N : ℝ) * Nat.choose N q := by
  classical
  unfold Matrix.trace
  simp only [Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, starRingEnd_apply, star_trivial,
    extensionIncidence]
  rw [Finset.sum_comm]
  calc
    (∑ π : Equiv.Perm (Fin N),
        ∑ f : PartialPerm N q,
          (if f.Extends π then 1 else 0) *
            (if f.Extends π then 1 else 0)) =
      ∑ π : Equiv.Perm (Fin N),
        (Fintype.card {f : PartialPerm N q // f.Extends π} : ℝ) := by
          apply Fintype.sum_congr
          intro π
          rw [Fintype.card_subtype]
          rw [← Finset.sum_boole (R := ℝ)
            (fun f : PartialPerm N q => f.Extends π) Finset.univ]
          apply Finset.sum_congr rfl
          intro f _
          by_cases h : f.Extends π <;> simp [h]
    _ = ∑ _π : Equiv.Perm (Fin N), (Nat.choose N q : ℝ) := by
          apply Fintype.sum_congr
          intro π
          rw [card_extendedPartial π]
    _ = (Nat.factorial N : ℝ) * Nat.choose N q := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm,
            Fintype.card_fin]
          simp [nsmul_eq_mul, mul_comm]

/-- For `q ≤ N`, the collision-free moment matrix has trace one. -/
theorem collisionFreeMomentMatrix_trace
    (hqN : q ≤ N) :
    Matrix.trace (collisionFreeMomentMatrix N q) = 1 := by
  have hfac : (Nat.factorial N : ℝ) ≠ 0 := by positivity
  have hchoose : (Nat.choose N q : ℝ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero hqN
  rw [collisionFreeMomentMatrix, Matrix.trace_smul,
    trace_incidence_gram]
  unfold momentNormalizer
  simp [smul_eq_mul, hfac, hchoose]

end PartialPerm
end LeanQuantumQueries.Permutation
