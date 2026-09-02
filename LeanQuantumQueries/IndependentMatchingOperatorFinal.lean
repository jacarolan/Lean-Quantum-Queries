import LeanQuantumQueries.IndependentMatchingTypedGlobalFinal

namespace IndependentMatchingBlockOccupancy

variable {ι : Type*} [Fintype ι]

/-- Pointwise formulation of an operator norm bound on a specified domain
predicate.  For a linear subspace predicate this is exactly the restricted
operator norm inequality. -/
def RestrictedOperatorNormLEF
    {V : Type*} (normV : V → ℝ) (T : V → V)
    (domain : V → Prop) (C : ℝ) : Prop :=
  ∀ f, domain f → normV (T f) ≤ C * normV f

/-- Divided global norm estimate for the concrete typed-sector direct sum. -/
theorem typedGlobal_occupiedPart_norm_bound_divF
    {q t : ℕ} (ht : 1 ≤ t)
    (S : ι → PackedTypedSectorF q t)
    (u : TypedGlobalBlockF S)
    (hlarge : 4 * t ^ 3 ≤ q)
    {f : TypedGlobalVectorF S}
    (hf : InTypedGlobalOutsideQuotientF S u f) :
    globalL2NormF (fun s => (S s).toPackedSector)
        (globalOccupiedPartF
          (fun s => (S s).toPackedSector) u f) ≤
      (39 * (t : ℝ) * Real.sqrt (t : ℝ) /
        fourthRootNatGlobalF ((8 * q) ^ 2)) *
        globalL2NormF (fun s => (S s).toPackedSector) f := by
  have hmul := typedGlobal_occupiedPart_norm_fourthRootF
    ht S u hlarge hf
  have hq : 0 < q := by omega
  have hQ : 0 < 8 * q := by omega
  have hroot : 0 < fourthRootNatGlobalF ((8 * q) ^ 2) := by
    rw [fourthRootNatGlobalF_sq (8 * q)]
    exact Real.sqrt_pos.2 (by exact_mod_cast hQ)
  rw [show
      (39 * (t : ℝ) * Real.sqrt (t : ℝ) /
        fourthRootNatGlobalF ((8 * q) ^ 2)) *
        globalL2NormF (fun s => (S s).toPackedSector) f =
      (39 * (t : ℝ) * Real.sqrt (t : ℝ) *
        globalL2NormF (fun s => (S s).toPackedSector) f) /
          fourthRootNatGlobalF ((8 * q) ^ 2) by ring]
  apply (le_div_iff₀ hroot).2
  simpa [mul_comm, mul_left_comm, mul_assoc] using hmul

/-- Final operator-style clipping theorem for the independent eligible-color
matching model.  The operator is the occupied-block projection `E_u`; its
domain is the outside space after quotienting the exact common intersection.
The ambient size is `N=(8q)^2`, hence the denominator is exactly `N^(1/4)`. -/
theorem occupiedProjection_restrictedOperatorNormLEF
    {q t : ℕ} (ht : 1 ≤ t)
    (S : ι → PackedTypedSectorF q t)
    (u : TypedGlobalBlockF S)
    (hlarge : 4 * t ^ 3 ≤ q) :
    RestrictedOperatorNormLEF
      (globalL2NormF (fun s => (S s).toPackedSector))
      (globalOccupiedPartF (fun s => (S s).toPackedSector) u)
      (InTypedGlobalOutsideQuotientF S u)
      (39 * (t : ℝ) * Real.sqrt (t : ℝ) /
        fourthRootNatGlobalF ((8 * q) ^ 2)) := by
  intro f hf
  exact typedGlobal_occupiedPart_norm_bound_divF ht S u hlarge hf

/-- The same theorem with a variable `N` and the exact model identity
`N=(8q)^2`. -/
theorem occupiedProjection_restrictedOperatorNormLE_of_sizeF
    {q t N : ℕ} (ht : 1 ≤ t)
    (S : ι → PackedTypedSectorF q t)
    (u : TypedGlobalBlockF S)
    (hlarge : 4 * t ^ 3 ≤ q)
    (hN : N = (8 * q) ^ 2) :
    RestrictedOperatorNormLEF
      (globalL2NormF (fun s => (S s).toPackedSector))
      (globalOccupiedPartF (fun s => (S s).toPackedSector) u)
      (InTypedGlobalOutsideQuotientF S u)
      (39 * (t : ℝ) * Real.sqrt (t : ℝ) /
        fourthRootNatGlobalF N) := by
  subst N
  exact occupiedProjection_restrictedOperatorNormLEF ht S u hlarge

end IndependentMatchingBlockOccupancy
