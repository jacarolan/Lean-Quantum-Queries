import LeanQuantumQueries.Permutation.PartialPerm

/-!
# Counting completions of a partial permutation

This file proves the elementary counting lemma used in the partial-bijection
proof of the one-call quantum attack.  An `r`-edge partial permutation on
`Fin N` has exactly `Nat.factorial (N - r)` extensions to a total permutation.

The proof chooses one completion `baseCompletion f`.  Left multiplication by
its inverse identifies every other completion with a permutation supported on
the complement of `f.dom`.  Mathlib's enumeration of permutations supported
on a finset then gives the factorial count.
-/

namespace LeanQuantumQueries.Permutation
namespace PartialPerm

open Equiv Equiv.Perm

variable {N r : ℕ}

/-- The image attached by `f` to a point in its domain. -/
noncomputable def imageOf (f : PartialPerm N r) (x : ↥f.dom) : Fin N :=
  Classical.choose ((mem_dom_iff f x.1).1 x.2)

/-- The chosen image really is an edge of the graph. -/
theorem imageOf_mem_graph (f : PartialPerm N r) (x : ↥f.dom) :
    (x.1, f.imageOf x) ∈ f.graph :=
  Classical.choose_spec ((mem_dom_iff f x.1).1 x.2)

/-- Injectivity of a partial permutation on its domain. -/
theorem imageOf_injective (f : PartialPerm N r) : Function.Injective f.imageOf := by
  intro x₁ x₂ h
  apply Subtype.ext
  apply f.right_unique (f.imageOf_mem_graph x₁)
  rw [h]
  exact f.imageOf_mem_graph x₂

/-- The domain has one point for each graph edge. -/
@[simp] theorem card_dom (f : PartialPerm N r) : f.dom.card = r := by
  have hinj :
      Set.InjOn (Prod.fst : Fin N × Fin N → Fin N) f.graph := by
    rintro ⟨x₁, y₁⟩ h₁ ⟨x₂, y₂⟩ h₂ hx
    dsimp at hx
    subst x₂
    have hy : y₁ = y₂ := f.left_unique h₁ h₂
    simp [hy]
  calc
    f.dom.card = f.graph.card := by
      simpa [dom] using Finset.card_image_of_injOn hinj
    _ = r := f.card_graph

/-- Every finite partial permutation has at least one total completion. -/
theorem exists_completion (f : PartialPerm N r) :
    ∃ π : Equiv.Perm (Fin N), f.Extends π := by
  obtain ⟨π, hπ⟩ := Equiv.Perm.exists_extending_pair
    (fun x : ↥f.dom => (x : Fin N))
    (fun x : ↥f.dom => f.imageOf x)
    Subtype.val_injective
    f.imageOf_injective
  refine ⟨π, ?_⟩
  intro e he
  let x : ↥f.dom :=
    ⟨e.1, (mem_dom_iff f e.1).2 ⟨e.2, he⟩⟩
  have hmap : π e.1 = f.imageOf x := hπ x
  have himage : f.imageOf x = e.2 :=
    f.left_unique (f.imageOf_mem_graph x) he
  exact hmap.trans himage

/-- A fixed total completion, used only to identify all completions with a
copy of the symmetric group on the unused points. -/
noncomputable def baseCompletion (f : PartialPerm N r) : Equiv.Perm (Fin N) :=
  Classical.choose f.exists_completion

/-- The fixed completion extends `f`. -/
theorem baseCompletion_extends (f : PartialPerm N r) :
    f.Extends f.baseCompletion :=
  Classical.choose_spec f.exists_completion

/-- Completions of `f` are in bijection with permutations supported on the
complement of its domain. -/
noncomputable def completionEquivComplement (f : PartialPerm N r) :
    {π : Equiv.Perm (Fin N) // f.Extends π} ≃
      {q : Equiv.Perm (Fin N) // q ∈ permsOfFinset f.domᶜ} where
  toFun π :=
    ⟨f.baseCompletion⁻¹ * π.1, by
      rw [mem_perms_of_finset_iff]
      intro x hx
      rw [Finset.mem_compl]
      intro hxdom
      rcases (mem_dom_iff f x).1 hxdom with ⟨y, hxy⟩
      have hπx : π.1 x = y := π.2 (x, y) hxy
      have hbasex : f.baseCompletion x = y :=
        f.baseCompletion_extends (x, y) hxy
      apply hx
      change f.baseCompletion.symm (π.1 x) = x
      rw [hπx, ← hbasex]
      exact f.baseCompletion.symm_apply_apply x⟩
  invFun q :=
    ⟨f.baseCompletion * q.1, by
      intro e he
      have hxdom : e.1 ∈ f.dom :=
        (mem_dom_iff f e.1).2 ⟨e.2, he⟩
      have hqfix : q.1 e.1 = e.1 := by
        by_contra hne
        have hcomp : e.1 ∈ f.domᶜ :=
          (mem_perms_of_finset_iff.mp q.2) hne
        exact (Finset.mem_compl.mp hcomp) hxdom
      rw [mul_apply, hqfix]
      exact f.baseCompletion_extends e he⟩
  left_inv π := by
    apply Subtype.ext
    simp
  right_inv q := by
    apply Subtype.ext
    simp

/-- Exact completion count: an `r`-edge partial permutation on `N` points has
exactly `Nat.factorial (N - r)` total extensions. -/
theorem card_completions (f : PartialPerm N r) :
    Fintype.card {π : Equiv.Perm (Fin N) // f.Extends π} =
      Nat.factorial (N - r) := by
  classical
  calc
    Fintype.card {π : Equiv.Perm (Fin N) // f.Extends π} =
        Fintype.card
          {q : Equiv.Perm (Fin N) // q ∈ permsOfFinset f.domᶜ} :=
      Fintype.card_congr f.completionEquivComplement
    _ = (permsOfFinset f.domᶜ).card := by
      simpa using Fintype.card_coe (permsOfFinset f.domᶜ)
    _ = Nat.factorial (f.domᶜ.card) := card_perms_of_finset f.domᶜ
    _ = Nat.factorial (N - r) := by
      rw [Finset.card_compl, f.card_dom]
      simp

/-- The corresponding exact fraction of all `N!` permutations. -/
theorem completion_fraction (f : PartialPerm N r) :
    (Fintype.card {π : Equiv.Perm (Fin N) // f.Extends π} : ℚ) /
        Fintype.card (Equiv.Perm (Fin N)) =
      (Nat.factorial (N - r) : ℚ) / (Nat.factorial N : ℚ) := by
  rw [f.card_completions, Fintype.card_perm]
  simp

end PartialPerm
end LeanQuantumQueries.Permutation
