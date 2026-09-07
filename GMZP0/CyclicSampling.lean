import GMZP0.PositiveCyclicAverage

/-! The cyclic expression is a genuine uniform average on its explicitly counted finite space. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

abbrev CyclicSamplingSpace (N q : ℕ) := Fin N × (horizontalShiftLabels N) × ZMod q × Fin N

theorem card_cyclicSamplingSpace (N q : ℕ) [NeZero q] :
    Fintype.card (CyclicSamplingSpace N q) = 2 * q * N ^ 3 := by
  simp only [CyclicSamplingSpace, Fintype.card_prod, Fintype.card_fin, Fintype.card_coe,
    horizontalShiftLabels_card, ZMod.card]
  ring

def cyclicWeight (N q : ℕ) (σ : Base N → ℝ) (X : Finset (Fin N))
    (z : CyclicSamplingSpace N q) : ℝ :=
  if z.1 ∈ X ∧ horizontalShiftIn X z.1 z.2.1.val then
    if 1 ≤ (label z.2.2.2 : ℤ) + z.2.1.val ∧ (label z.2.2.2 : ℤ) + z.2.1.val ≤ N then
      cyclicField N q σ 0 z.1 z.2.2.1 else 0
  else 0

theorem cyclicWeight_bounds (N q : ℕ) (σ : Base N → ℝ) (X : Finset (Fin N))
    (hσ : ∀ z, 0 ≤ σ z ∧ σ z ≤ 1) (z : CyclicSamplingSpace N q) :
    0 ≤ cyclicWeight N q σ X z ∧ cyclicWeight N q σ X z ≤ 1 := by
  unfold cyclicWeight
  split_ifs
  · exact cyclicField_property N q σ 0 (fun a : ℝ => 0 ≤ a ∧ a ≤ 1) hσ ⟨le_rfl, zero_le_one⟩ _ _
  · exact ⟨le_rfl, zero_le_one⟩
  · exact ⟨le_rfl, zero_le_one⟩

theorem cyclicModulusAverage_as_uniform_mean (N q : ℕ) [NeZero q]
    (p : Base N → Frequency) (X : Finset (Fin N)) (σ : Base N → ℝ) (lam : Base N → ℂ) :
    cyclicModulusAverage N q p X σ lam =
      (∑ z : CyclicSamplingSpace N q, cyclicWeight N q σ X z *
        ‖cyclicShiftLagB N q p σ lam z.1 z.2.2.1 z.2.1.val (label z.2.2.2)‖) /
          (Fintype.card (CyclicSamplingSpace N q) : ℝ) := by
  rw [card_cyclicSamplingSpace]
  simp only [cyclicModulusAverage, CyclicSamplingSpace, cyclicWeight, Fintype.sum_prod_type,
    ite_mul, zero_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.sum_coe_sort (horizontalShiftLabels N) (fun h =>
    if x ∈ X ∧ horizontalShiftIn X x h then
      ∑ v : ZMod q, ∑ t : Fin N, if 1 ≤ (label t : ℤ) + h ∧ (label t : ℤ) + h ≤ N then
        cyclicField N q σ 0 x v * ‖cyclicShiftLagB N q p σ lam x v h (label t)‖ else 0
    else 0)]
  apply Finset.sum_congr rfl
  intro h _
  by_cases hx : x ∈ X ∧ horizontalShiftIn X x h.val
  · simp only [hx, and_self, if_true]
  · simp only [hx, if_false, Finset.sum_const_zero]

end GMZP0
