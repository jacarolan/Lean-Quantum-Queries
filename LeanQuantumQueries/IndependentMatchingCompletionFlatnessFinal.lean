import LeanQuantumQueries.IndependentMatchingFlatnessVerified

namespace IndependentMatchingBlockOccupancy
namespace CompletionFlatness

open MatchingFlatnessVerified

/-- A total injective labeling of items of type `α` by labels of type `β`. -/
abbrev TotalInjection (α β : Type*) := α ↪ β

/-- A finite prescribed injective partial labeling. -/
structure PartialInjection (k : ℕ) (α β : Type*) where
  item : Fin k ↪ α
  label : Fin k ↪ β

/-- A total injection extends a prescribed partial labeling. -/
def ExtendsInjection {k : ℕ} {α β : Type*}
    (f : TotalInjection α β) (D : PartialInjection k α β) : Prop :=
  ∀ i, f (D.item i) = D.label i

/-- Transport a total injection by permutations of its item and label sets. -/
def transportInjection {α β : Type*}
    (σ : Equiv.Perm α) (τ : Equiv.Perm β) :
    TotalInjection α β ≃ TotalInjection α β where
  toFun f :=
    { toFun := fun x => τ (f (σ.symm x))
      inj' := fun x y h => by
        have hf : f (σ.symm x) = f (σ.symm y) := τ.injective h
        exact σ.symm.injective (f.injective hf) }
  invFun f :=
    { toFun := fun x => τ.symm (f (σ x))
      inj' := fun x y h => by
        have hf : f (σ x) = f (σ y) := τ.symm.injective h
        exact σ.injective (f.injective hf) }
  left_inv f := by
    apply Function.Embedding.ext
    intro x
    simp
  right_inv f := by
    apply Function.Embedding.ext
    intro x
    simp

/-- Partial injective label assignments of equal size have equinumerous total
injective completions. -/
noncomputable def injectionExtensionEquiv
    {k : ℕ} {α β : Type*}
    (D₁ D₂ : PartialInjection k α β) :
    {f : TotalInjection α β // ExtendsInjection f D₁} ≃
      {f : TotalInjection α β // ExtendsInjection f D₂} := by
  classical
  let exσ := Equiv.Perm.exists_extending_pair
    D₁.item D₂.item D₁.item.injective D₂.item.injective
  let σ := Classical.choose exσ
  have hσ := Classical.choose_spec exσ
  let exτ := Equiv.Perm.exists_extending_pair
    D₁.label D₂.label D₁.label.injective D₂.label.injective
  let τ := Classical.choose exτ
  have hτ := Classical.choose_spec exτ
  let E := transportInjection σ τ
  exact
    { toFun := fun f => ⟨E f.1, by
        intro i
        change τ (f.1 (σ.symm (D₂.item i))) = D₂.label i
        rw [← hσ i, σ.symm_apply_apply, f.2 i, hτ i]⟩
      invFun := fun f => ⟨E.symm f.1, by
        intro i
        change τ.symm (f.1 (σ (D₁.item i))) = D₁.label i
        rw [hσ i, f.2 i, ← hτ i, τ.symm_apply_apply]⟩
      left_inv := by
        intro f
        apply Subtype.ext
        exact E.symm_apply_apply f.1
      right_inv := by
        intro f
        apply Subtype.ext
        exact E.apply_symm_apply f.1 }

/-- Instance-free cardinal form for injective label completions. -/
theorem injection_extension_natCard_eq
    {k : ℕ} {α β : Type*}
    (D₁ D₂ : PartialInjection k α β) :
    Nat.card {f : TotalInjection α β // ExtendsInjection f D₁} =
      Nat.card {f : TotalInjection α β // ExtendsInjection f D₂} := by
  exact Nat.card_congr (injectionExtensionEquiv D₁ D₂)

/-- Independent matching and injective-label completions belonging to one
sector description. -/
structure CompletionProblem
    (k : Fin 3 → ℕ) (L R : Fin 3 → Type*)
    (ell : ℕ) (α β : Type*) where
  matching : ThreeColorPartial k L R
  labeling : PartialInjection ell α β

/-- All independent random choices extending one observed sector description. -/
abbrev Completions
    {k : Fin 3 → ℕ} {L R : Fin 3 → Type*}
    {ell : ℕ} {α β : Type*}
    (D : CompletionProblem k L R ell α β) :=
  ThreeColorExtensions D.matching ×
    {f : TotalInjection α β // ExtendsInjection f D.labeling}

/-- Simultaneously relabeling all three matching colors and the injective
labels gives an exact equivalence of completion sets. -/
noncomputable def completionEquiv
    {k : Fin 3 → ℕ} {L R : Fin 3 → Type*}
    {ell : ℕ} {α β : Type*}
    (D₁ D₂ : CompletionProblem k L R ell α β) :
    Completions D₁ ≃ Completions D₂ :=
  (threeColorExtensionEquiv D₁.matching D₂.matching).prodCongr
    (injectionExtensionEquiv D₁.labeling D₂.labeling)

/-- Exact joint completion flatness. -/
theorem completion_natCard_eq
    {k : Fin 3 → ℕ} {L R : Fin 3 → Type*}
    {ell : ℕ} {α β : Type*}
    (D₁ D₂ : CompletionProblem k L R ell α β) :
    Nat.card (Completions D₁) = Nat.card (Completions D₂) := by
  exact Nat.card_congr (completionEquiv D₁ D₂)

end CompletionFlatness
end IndependentMatchingBlockOccupancy
