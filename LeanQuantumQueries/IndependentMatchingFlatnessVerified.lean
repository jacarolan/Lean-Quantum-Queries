import Mathlib

namespace IndependentMatchingBlockOccupancy
namespace MatchingFlatnessVerified

/-- A total matching between the eligible endpoints of one color. -/
abbrev Matching (α β : Type*) := α ≃ β

/-- A partial matching with `k` distinct prescribed endpoint pairs. -/
structure PartialMatching (k : ℕ) (α β : Type*) where
  left : Fin k ↪ α
  right : Fin k ↪ β

/-- A total matching extends a partial matching when it contains every
prescribed pair. -/
def Extends {k : ℕ} {α β : Type*} (e : Matching α β)
    (D : PartialMatching k α β) : Prop :=
  ∀ r, e (D.left r) = D.right r

/-- Simultaneously relabel the left and right eligible endpoint sets. -/
def relabel {α β : Type*} (σ : Equiv.Perm α) (τ : Equiv.Perm β) :
    Matching α β ≃ Matching α β where
  toFun e := (σ.symm.trans e).trans τ
  invFun e := (σ.trans e).trans τ.symm
  left_inv e := by
    ext x
    simp
  right_inv e := by
    ext x
    simp

/-- Two injective partial matchings with the same number of pairs have
canonically equinumerous completion sets. -/
noncomputable def extensionEquiv {k : ℕ} {α β : Type*}
    (D₁ D₂ : PartialMatching k α β) :
    {e : Matching α β // Extends e D₁} ≃
      {e : Matching α β // Extends e D₂} := by
  classical
  let hσex : ∃ σ : Equiv.Perm α, ∀ r, σ (D₁.left r) = D₂.left r :=
    Equiv.Perm.exists_extending_pair
      D₁.left D₂.left D₁.left.injective D₂.left.injective
  let σ : Equiv.Perm α := Classical.choose hσex
  have hσ : ∀ r, σ (D₁.left r) = D₂.left r :=
    Classical.choose_spec hσex
  let hτex : ∃ τ : Equiv.Perm β, ∀ r, τ (D₁.right r) = D₂.right r :=
    Equiv.Perm.exists_extending_pair
      D₁.right D₂.right D₁.right.injective D₂.right.injective
  let τ : Equiv.Perm β := Classical.choose hτex
  have hτ : ∀ r, τ (D₁.right r) = D₂.right r :=
    Classical.choose_spec hτex
  let E := relabel σ τ
  refine
    { toFun := fun e => ⟨E e.1, ?_⟩
      invFun := fun e => ⟨E.symm e.1, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro r
    change τ (e.1 (σ.symm (D₂.left r))) = D₂.right r
    rw [← hσ r, σ.symm_apply_apply, e.2 r, hτ r]
  · intro r
    change τ.symm (e.1 (σ (D₁.left r))) = D₁.right r
    rw [hσ r, e.2 r, ← hτ r, τ.symm_apply_apply]
  · intro e
    apply Subtype.ext
    exact E.symm_apply_apply e.1
  · intro e
    apply Subtype.ext
    exact E.apply_symm_apply e.1

/-- Endpoint identities do not affect the number of completions. -/
theorem extension_natCard_eq {k : ℕ} {α β : Type*}
    (D₁ D₂ : PartialMatching k α β) :
    Nat.card {e : Matching α β // Extends e D₁} =
      Nat.card {e : Matching α β // Extends e D₂} :=
  Nat.card_congr (extensionEquiv D₁ D₂)

/-- Partial databases for the three independently sampled edge colors. -/
structure ThreeColorPartial (k : Fin 3 → ℕ)
    (L R : Fin 3 → Type*) where
  edge : ∀ c, PartialMatching (k c) (L c) (R c)

/-- Independent total matchings extending all three partial databases. -/
abbrev ThreeColorExtensions {k : Fin 3 → ℕ}
    {L R : Fin 3 → Type*} (D : ThreeColorPartial k L R) :=
  ∀ c, {e : Matching (L c) (R c) // Extends e (D.edge c)}

/-- Relabel every color independently. -/
noncomputable def threeColorExtensionEquiv {k : Fin 3 → ℕ}
    {L R : Fin 3 → Type*}
    (D₁ D₂ : ThreeColorPartial k L R) :
    ThreeColorExtensions D₁ ≃ ThreeColorExtensions D₂ :=
  Equiv.piCongrRight fun c => extensionEquiv (D₁.edge c) (D₂.edge c)

/-- Exact three-color completion flatness. -/
theorem threeColor_extension_natCard_eq {k : Fin 3 → ℕ}
    {L R : Fin 3 → Type*}
    (D₁ D₂ : ThreeColorPartial k L R) :
    Nat.card (ThreeColorExtensions D₁) =
      Nat.card (ThreeColorExtensions D₂) :=
  Nat.card_congr (threeColorExtensionEquiv D₁ D₂)

end MatchingFlatnessVerified
end IndependentMatchingBlockOccupancy
