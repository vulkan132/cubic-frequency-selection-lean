import GMZP0.FourShiftSmoothing
import GMZP0.CyclicSampling

/-! Smoothing the actual cyclic lag sequence while retaining the original sampling weight. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

def cyclicLagSequence (N q : ℕ) (p : Base N → Frequency) (σ : Base N → ℝ)
    (lam : Base N → ℂ) (x : Fin N) (v : ZMod q) (h t k : ℤ) : ℂ :=
  cyclicLagG N q p σ lam x v h t k * circleCharacter (cyclicShiftLagP N q p x v h t k)

theorem cyclicLagSequence_norm_le (N q : ℕ) (p : Base N → Frequency) (σ : Base N → ℝ)
    (lam : Base N → ℂ) (x : Fin N) (v : ZMod q) (h t k : ℤ)
    (hσ : ∀ z, 0 ≤ σ z ∧ σ z ≤ 1) (hlam : ∀ z, ‖lam z‖ = 1) :
    ‖cyclicLagSequence N q p σ lam x v h t k‖ ≤ 1 := by
  rw [cyclicLagSequence, norm_mul, norm_circleCharacter, mul_one]
  exact cyclicLagG_norm_le N q p σ lam x v h t k hσ hlam

def cyclicSmoothedLagB (N q ℓ : ℕ) (p : Base N → Frequency) (σ : Base N → ℝ)
    (lam : Base N → ℂ) (x : Fin N) (v : ZMod q) (h t : ℤ) : ℂ :=
  fourShiftSmoothedAverage N ℓ h t (cyclicLagSequence N q p σ lam x v h t)

theorem cyclicSmoothedLagB_error {N : ℕ} (hN : 0 < N) (q ℓ : ℕ)
    (p : Base N → Frequency) (σ : Base N → ℝ) (lam : Base N → ℂ)
    (x : Fin N) (v : ZMod q) (h t : ℤ)
    (hσ : ∀ z, 0 ≤ σ z ∧ σ z ≤ 1) (hlam : ∀ z, ‖lam z‖ = 1) :
    ‖cyclicSmoothedLagB N q ℓ p σ lam x v h t - cyclicShiftLagB N q p σ lam x v h t‖ ≤
      8 * (ℓ : ℝ) / N := by
  exact norm_fourShiftSmoothedAverage_sub_le hN ℓ h t _
    (fun k => cyclicLagSequence_norm_le N q p σ lam x v h t k hσ hlam)

def cyclicSmoothedModulusAverage (N q ℓ : ℕ) [NeZero q] (p : Base N → Frequency)
    (X : Finset (Fin N)) (σ : Base N → ℝ) (lam : Base N → ℂ) : ℝ :=
  realUniformMean (fun z : CyclicSamplingSpace N q => cyclicWeight N q σ X z *
    ‖cyclicSmoothedLagB N q ℓ p σ lam z.1 z.2.2.1 z.2.1.val (label z.2.2.2)‖)

theorem cyclic_smoothed_average_positive {N : ℕ} (hN : 0 < N) (q : ℕ) [NeZero q]
    (p : Base N → Frequency) (X : Finset (Fin N)) (σ : Base N → ℝ) (lam : Base N → ℂ)
    (a : ℝ) (ha : 0 ≤ a) (hσ : ∀ z, 0 ≤ σ z ∧ σ z ≤ 1) (hlam : ∀ z, ‖lam z‖ = 1)
    (haverage : a ≤ cyclicModulusAverage N q p X σ lam) :
    7 * a / 8 ≤ cyclicSmoothedModulusAverage N q (smoothingRadius N a) p X σ lam := by
  have hcard : 0 < Fintype.card (CyclicSamplingSpace N q) := by
    rw [card_cyclicSamplingSpace]
    have hq : 0 < q := NeZero.pos q
    positivity
  let : Nonempty (CyclicSamplingSpace N q) := Fintype.card_pos_iff.mp hcard
  have herror (z : CyclicSamplingSpace N q) :
      ‖cyclicSmoothedLagB N q (smoothingRadius N a) p σ lam
          z.1 z.2.2.1 z.2.1.val (label z.2.2.2) -
        cyclicShiftLagB N q p σ lam z.1 z.2.2.1 z.2.1.val (label z.2.2.2)‖ ≤ a / 8 :=
    (cyclicSmoothedLagB_error hN q _ p σ lam _ _ _ _ hσ hlam).trans
      (smoothingRadius_error hN a ha)
  have hstable := weighted_norm_mean_stability (cyclicWeight N q σ X)
    (fun z => cyclicShiftLagB N q p σ lam z.1 z.2.2.1 z.2.1.val (label z.2.2.2))
    (fun z => cyclicSmoothedLagB N q (smoothingRadius N a) p σ lam
      z.1 z.2.2.1 z.2.1.val (label z.2.2.2))
    (a / 8) (by positivity) (cyclicWeight_bounds N q σ X hσ) herror
  rw [cyclicModulusAverage_as_uniform_mean] at haverage
  change a ≤ realUniformMean _ at haverage
  change realUniformMean _ - a / 8 ≤
    cyclicSmoothedModulusAverage N q (smoothingRadius N a) p X σ lam at hstable
  linarith only [haverage, hstable]

end GMZP0
