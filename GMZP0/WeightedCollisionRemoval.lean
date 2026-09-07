import GMZP0.CubeCollision
import GMZP0.PositiveCubeAverage

/-! Removing colliding cubes costs only their probability and preserves every original weight. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

theorem realUniformMean_add {I : Type*} [Fintype I] (F G : I → ℝ) :
    realUniformMean (fun i => F i + G i) = realUniformMean F + realUniformMean G := by
  simp only [realUniformMean, Finset.sum_add_distrib, add_div]

theorem weighted_event_removal {I : Type*} [Fintype I] (W : I → ℝ)
    (hW : ∀ i, 0 ≤ W i ∧ W i ≤ 1) (P : I → Prop) [DecidablePred P] :
    realUniformMean W - realUniformMean (fun i => if ¬ P i then 1 else 0) ≤
      realUniformMean (fun i => if P i then W i else 0) := by
  have hp (i : I) : W i ≤ (if P i then W i else 0) + (if ¬ P i then 1 else 0) := by
    by_cases hi : P i
    · simp [hi]
    · simpa only [if_neg hi, if_pos hi, zero_add] using (hW i).2
  have hm := realUniformMean_mono W
    (fun i => (if P i then W i else 0) + (if ¬ P i then 1 else 0)) hp
  rw [realUniformMean_add] at hm
  linarith

def cyclicDistinctCubeNearWeight (N q ℓ : ℕ) (p : Base N → Frequency) (σ : Base N → ℝ)
    (d : ℕ) (E : ℝ) (x : Fin N) (Y : ZMod q) (h : ℤ) (u : CubeShiftPairs ℓ) : ℝ := by
  classical
  exact if Function.Injective (cyclicCubeVertex q ℓ h Y u)
    then cyclicCubeNearWeight N q ℓ p σ d E x Y h u else 0

def cyclicDistinctPositiveCubeNearMass (N q ℓ : ℕ) [NeZero q] (p : Base N → Frequency)
    (σ : Base N → ℝ) (d : ℕ) (E : ℝ) : ℝ :=
  realUniformMean (fun z : PositiveCubeParameters N q ℓ =>
    cyclicDistinctCubeNearWeight N q ℓ p σ d E z.1 z.2.2.1 (label z.2.1) z.2.2.2)

theorem positive_cube_total_collision_probability {N q ℓ : ℕ} [Fact q.Prime]
    (hN : 0 < N) (hℓ : 2 * ℓ < q) (hq : 2 * N < q) :
    realUniformMean (fun z : PositiveCubeParameters N q ℓ =>
      if ¬ Function.Injective (cyclicCubeVertex q ℓ (label z.2.1) z.2.2.1 z.2.2.2)
      then 1 else 0) ≤ 120 / (2 * (ℓ : ℝ) + 1) := by
  let : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  rw [realUniformMean_prod_four (fun (_ : Fin N) (h : Fin N) Y u =>
    if ¬ Function.Injective (cyclicCubeVertex q ℓ (label h) Y u) then 1 else 0)]
  calc
    _ ≤ realUniformMean (fun _ : Fin N => realUniformMean (fun _ : Fin N =>
        realUniformMean (fun _ : ZMod q => 120 / (2 * (ℓ : ℝ) + 1)))) := by
      apply realUniformMean_mono
      intro x
      apply realUniformMean_mono
      intro h
      apply realUniformMean_mono
      intro Y
      exact positive_cube_collision_probability hℓ hq h Y
    _ = _ := by simp only [realUniformMean_const]

theorem cyclicDistinctPositiveCubeNearMass_lower {N q ℓ : ℕ} [Fact q.Prime]
    (hN : 0 < N) (hℓ : 2 * ℓ < q) (hq : 2 * N < q)
    (p : Base N → Frequency) (σ : Base N → ℝ) (hσ : ∀ z, 0 ≤ σ z ∧ σ z ≤ 1)
    (d : ℕ) (E : ℝ) :
    cyclicPositiveCubeNearMass N q ℓ p σ d E - 120 / (2 * (ℓ : ℝ) + 1) ≤
      cyclicDistinctPositiveCubeNearMass N q ℓ p σ d E := by
  classical
  have hw (z : PositiveCubeParameters N q ℓ) :
      0 ≤ cyclicCubeNearWeight N q ℓ p σ d E z.1 z.2.2.1 (label z.2.1) z.2.2.2 ∧
        cyclicCubeNearWeight N q ℓ p σ d E z.1 z.2.2.1 (label z.2.1) z.2.2.2 ≤ 1 := by
    have hb := cyclicCubeNearWeight_bounds N q ℓ p σ d E z.1 z.2.2.1 (label z.2.1) z.2.2.2 hσ
    exact ⟨hb.1, hb.2.trans (cyclicCubeWeight_bounds N q ℓ σ z.1 z.2.2.1 (label z.2.1) z.2.2.2 hσ).2⟩
  have hr := weighted_event_removal
    (fun z : PositiveCubeParameters N q ℓ =>
      cyclicCubeNearWeight N q ℓ p σ d E z.1 z.2.2.1 (label z.2.1) z.2.2.2) hw
    (fun z => Function.Injective (cyclicCubeVertex q ℓ (label z.2.1) z.2.2.1 z.2.2.2))
  have hc := positive_cube_total_collision_probability hN hℓ hq
  change cyclicPositiveCubeNearMass N q ℓ p σ d E - _ ≤
    cyclicDistinctPositiveCubeNearMass N q ℓ p σ d E at hr
  linarith

end GMZP0
