import Mathlib

open scoped BigOperators

namespace IndependentMatchingBlockOccupancy
namespace MatchingFlatness

/-- A total independent matching between two equally sized eligible endpoint
sets is simply an equivalence. -/
abbrev Matching (α β : Type*) := α ≃ β

/-- A list of `k` distinct prescribed left endpoints and right endpoints. -/
structure PartialMatching (k : ℕ) (α β : Type*) where
  left : Fin k ↪ α
  right : Fin k ↪ β

/-- A total matching contains all pairs prescribed by a partial matching. -/
def Extends {k : ℕ} {α β : Type*} (e : Matching α β)
    (D : PartialMatching k α β) : Prop :=
  ∀ i, e (D.left i) = D.right i

/-- Relabeling eligible endpoints on the left and right is an equivalence on
all total matchings. -/
def transport {α β : Type*} (σ : Equiv.Perm α) (τ : Equiv.Perm β) :
    Matching α β ≃ Matching α β where
  toFun e := (σ.symm.trans e).trans τ
  invFun e := (σ.trans e).trans τ.symm
  left_inv e := by
    ext x
    simp
  right_inv e := by
    ext x
    simp

/-- Any two injective partial endpoint assignments of the same size are
contained in exactly the same number of total matchings. -/
noncomputable def extensionEquiv {k : ℕ} {α β : Type*}
    (D₁ D₂ : PartialMatching k α β) :
    {e : Matching α β // Extends e D₁} ≃
      {e : Matching α β // Extends e D₂} := by
  classical
  let exσ := Equiv.Perm.exists_extending_pair
    D₁.left D₂.left D₁.left.injective D₂.left.injective
  let σ := Classical.choose exσ
  have hσ := Classical.choose_spec exσ
  let exτ := Equiv.Perm.exists_extending_pair
    D₁.right D₂.right D₁.right.injective D₂.right.injective
  let τ := Classical.choose exτ
  have hτ := Classical.choose_spec exτ
  let E := transport σ τ
  exact
    { toFun := fun e => ⟨E e.1, by
        intro i
        change τ (e.1 (σ.symm (D₂.left i))) = D₂.right i
        rw [← hσ i, σ.symm_apply_apply, e.2 i, hτ i]⟩
      invFun := fun e => ⟨E.symm e.1, by
        intro i
        change τ.symm (e.1 (σ (D₁.left i))) = D₁.right i
        rw [hσ i, e.2 i, ← hτ i, τ.symm_apply_apply]⟩
      left_inv := by
        intro e
        apply Subtype.ext
        exact E.symm_apply_apply e.1
      right_inv := by
        intro e
        apply Subtype.ext
        exact E.apply_symm_apply e.1 }

/-- Exact endpoint-flatness statement for one color. -/
theorem extension_card_eq {k : ℕ} {α β : Type*}
    (D₁ D₂ : PartialMatching k α β) :
    Nat.card {e : Matching α β // Extends e D₁} =
      Nat.card {e : Matching α β // Extends e D₂} := by
  exact Nat.card_congr (extensionEquiv D₁ D₂)

/-- Partial databases for three independently sampled colors. -/
structure ThreeColorPartial (k : Fin 3 → ℕ)
    (L R : Fin 3 → Type*) where
  edge : ∀ c, PartialMatching (k c) (L c) (R c)

/-- Triples of independently chosen total matchings extending a prescribed
three-color partial database. -/
abbrev ThreeColorExtensions {k : Fin 3 → ℕ}
    {L R : Fin 3 → Type*} (D : ThreeColorPartial k L R) :=
  ∀ c, {e : Matching (L c) (R c) // Extends e (D.edge c)}

/-- Relabeling each color independently gives an equivalence between the sets
of three-color matching completions. -/
noncomputable def threeColorExtensionEquiv {k : Fin 3 → ℕ}
    {L R : Fin 3 → Type*}
    (D₁ D₂ : ThreeColorPartial k L R) :
    ThreeColorExtensions D₁ ≃ ThreeColorExtensions D₂ :=
  Equiv.piCongrRight fun c => extensionEquiv (D₁.edge c) (D₂.edge c)

/-- Exact flatness for all three independent colors: only the number of
prescribed edges of each color matters, not their endpoint identities. -/
theorem threeColor_extension_card_eq {k : Fin 3 → ℕ}
    {L R : Fin 3 → Type*}
    (D₁ D₂ : ThreeColorPartial k L R) :
    Nat.card (ThreeColorExtensions D₁) =
      Nat.card (ThreeColorExtensions D₂) := by
  exact Nat.card_congr (threeColorExtensionEquiv D₁ D₂)

end MatchingFlatness
end IndependentMatchingBlockOccupancy
