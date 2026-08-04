import LeanQuantumQueries.Permutation.PartialPerm
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace LeanQuantumQueries.Permutation

open scoped ComplexConjugate
open WithLp

/-- The finite-dimensional Hilbert space with orthonormal basis indexed by `α`. -/
abbrev Hilbert (α : Type*) [Fintype α] := EuclideanSpace ℂ α

/-- The true hidden-memory space, with basis indexed by permutations. -/
abbrev PermSpace (N : ℕ) := Hilbert (Equiv.Perm (Fin N))

/-- The label space at matching degree `r`. -/
abbrev LabelSpace (N r : ℕ) := Hilbert (PartialPerm N r)

/-- Turn a coordinate function into a vector in finite-dimensional `ℓ²`. -/
noncomputable def ofFun {α : Type*} [Fintype α] (f : α → ℂ) : Hilbert α :=
  toLp 2 f

@[simp] theorem ofFun_apply {α : Type*} [Fintype α] (f : α → ℂ) (i : α) :
    ofFun f i = f i := rfl

/-- The standard basis vector at `i`. -/
noncomputable def ket {α : Type*} [Fintype α] [DecidableEq α] (i : α) : Hilbert α :=
  ofFun fun j => if j = i then 1 else 0

@[simp] theorem ket_apply {α : Type*} [Fintype α] [DecidableEq α] (i j : α) :
    ket i j = if j = i then 1 else 0 := rfl

@[simp] theorem ket_apply_self {α : Type*} [Fintype α] [DecidableEq α] (i : α) :
    ket i i = 1 := by simp [ket]

@[simp] theorem ket_apply_ne {α : Type*} [Fintype α] [DecidableEq α]
    {i j : α} (h : j ≠ i) : ket i j = 0 := by simp [ket, h]

/-- The unnormalized indicator of the permutations extending `f`. -/
noncomputable def completionIndicator {N r : ℕ} (f : PartialPerm N r) : PermSpace N :=
  ofFun fun π => if f.Extends π then 1 else 0

@[simp] theorem completionIndicator_apply {N r : ℕ} (f : PartialPerm N r)
    (π : Equiv.Perm (Fin N)) :
    completionIndicator f π = if f.Extends π then 1 else 0 := rfl

/-- The number of total permutations extending a partial permutation. -/
noncomputable def completionCard {N r : ℕ} (f : PartialPerm N r) : ℕ :=
  Fintype.card {π : Equiv.Perm (Fin N) // f.Extends π}

/-- The normalized uniform superposition over all completions of `f`. -/
noncomputable def completionState {N r : ℕ} (f : PartialPerm N r) : PermSpace N :=
  ((Real.sqrt (completionCard f : ℝ))⁻¹ : ℂ) • completionIndicator f

@[simp] theorem completionState_apply {N r : ℕ} (f : PartialPerm N r)
    (π : Equiv.Perm (Fin N)) :
    completionState f π =
      ((Real.sqrt (completionCard f : ℝ))⁻¹ : ℂ) *
        (if f.Extends π then 1 else 0) := by
  rfl

/-- Synthesis of a label vector as a linear combination of completion states. -/
noncomputable def synthesis (N r : ℕ) : LabelSpace N r →ₗ[ℂ] PermSpace N where
  toFun a := ∑ f, a f • completionState f
  map_add' a b := by
    simp only [add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c a := by
    simp only [smul_apply, RingHom.id_apply, mul_smul, Finset.smul_sum]

@[simp] theorem synthesis_apply (N r : ℕ) (a : LabelSpace N r)
    (π : Equiv.Perm (Fin N)) :
    synthesis N r a π = ∑ f, a f * completionState f π := by
  simp [synthesis]

@[simp] theorem synthesis_ket (N r : ℕ) [DecidableEq (PartialPerm N r)]
    (f : PartialPerm N r) :
    synthesis N r (ket f) = completionState f := by
  ext π
  simp [synthesis, ket]

end LeanQuantumQueries.Permutation
