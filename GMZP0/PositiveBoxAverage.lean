import GMZP0.FullLagAverage
import GMZP0.PositiveSmoothedAverage

/-! Positive box moments of the original cyclic sequence, after justified removal of weights. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

abbrev CyclicBoxSamplingSpace (N q : ℕ) := CyclicSamplingSpace N q × fullLagLabels N

theorem card_cyclicBoxSamplingSpace (N q : ℕ) [NeZero q] :
    Fintype.card (CyclicBoxSamplingSpace N q) = 2 * q * N ^ 3 * (2 * N + 1) := by
  change Fintype.card (CyclicSamplingSpace N q × fullLagLabels N) = _
  rw [Fintype.card_prod, card_cyclicSamplingSpace, Fintype.card_coe, fullLagLabels_card]

def cyclicBoxNormAverage (N q ℓ : ℕ) [NeZero q] (p : Base N → Frequency)
    (σ : Base N → ℝ) (lam : Base N → ℂ) : ℝ :=
  realUniformMean (fun z : CyclicBoxSamplingSpace N q => cyclicLagBoxNorm N q ℓ p σ lam
    z.1.1 z.1.2.2.1 z.1.2.1.val (label z.1.2.2.2) z.2.val)

def cyclicBoxMomentAverage (N q ℓ : ℕ) [NeZero q] (p : Base N → Frequency)
    (σ : Base N → ℝ) (lam : Base N → ℂ) : ℝ :=
  realUniformMean (fun z : CyclicBoxSamplingSpace N q => boxMoment 3
    (cyclicLagBoxFunction N q ℓ p σ lam z.1.1 z.1.2.2.1 z.1.2.1.val (label z.1.2.2.2) z.2.val))

theorem cyclicSmoothedModulusAverage_le_three_boxMean {N : ℕ} (hN : 0 < N) (q ℓ : ℕ) [NeZero q]
    (p : Base N → Frequency) (X : Finset (Fin N)) (σ : Base N → ℝ) (lam : Base N → ℂ)
    (hσ : ∀ z, 0 ≤ σ z ∧ σ z ≤ 1) :
    cyclicSmoothedModulusAverage N q ℓ p X σ lam ≤ 3 * cyclicBoxNormAverage N q ℓ p σ lam := by
  have hz (z : CyclicSamplingSpace N q) :
      cyclicWeight N q σ X z * ‖cyclicSmoothedLagB N q ℓ p σ lam
        z.1 z.2.2.1 z.2.1.val (label z.2.2.2)‖ ≤
      3 * realUniformMean (fun k : fullLagLabels N => cyclicLagBoxNorm N q ℓ p σ lam
        z.1 z.2.2.1 z.2.1.val (label z.2.2.2) k.val) := by
    have hw := cyclicWeight_bounds N q σ X hσ z
    exact (mul_le_mul_of_nonneg_left
      (cyclicSmoothedLagB_le_boxSum hN q ℓ p σ lam _ _ _ _) hw.1).trans
      (weighted_lag_sum_le_three_mean hN _ _ (integer_label_bounds z.2.2.2) _
        (cyclicLagBoxNorm_nonneg N q ℓ p σ lam _ _ _ _) _ hw.2)
  have hs := realUniformMean_mono _ _ hz
  rw [realUniformMean_const_mul] at hs
  change cyclicSmoothedModulusAverage N q ℓ p X σ lam ≤ _ at hs
  unfold cyclicBoxNormAverage
  rw [realUniformMean_prod (fun (z : CyclicSamplingSpace N q) (k : fullLagLabels N) =>
    cyclicLagBoxNorm N q ℓ p σ lam z.1 z.2.2.1 z.2.1.val (label z.2.2.2) k.val)]
  exact hs

theorem cyclicBoxNormAverage_pow_le {N : ℕ} (hN : 0 < N) (q ℓ : ℕ) [NeZero q]
    (p : Base N → Frequency) (σ : Base N → ℝ) (lam : Base N → ℂ) :
    cyclicBoxNormAverage N q ℓ p σ lam ^ 16 ≤ cyclicBoxMomentAverage N q ℓ p σ lam := by
  have hcard : 0 < Fintype.card (CyclicSamplingSpace N q) := by
    rw [card_cyclicSamplingSpace]
    have hq : 0 < q := NeZero.pos q
    positivity
  let : Nonempty (CyclicSamplingSpace N q) := Fintype.card_pos_iff.mp hcard
  have hj := realUniformMean_pow_two_le
    (fun z : CyclicBoxSamplingSpace N q => cyclicLagBoxNorm N q ℓ p σ lam
      z.1.1 z.1.2.2.1 z.1.2.1.val (label z.1.2.2.2) z.2.val)
    (fun _ => cyclicLagBoxNorm_nonneg N q ℓ p σ lam _ _ _ _ _) 4
  norm_num only at hj
  simpa only [cyclicLagBoxNorm_pow, cyclicBoxNormAverage, cyclicBoxMomentAverage] using hj

theorem positive_cyclic_box_average {N : ℕ} (hN : 0 < N) (q : ℕ) [NeZero q]
    (p : Base N → Frequency) (X : Finset (Fin N)) (σ : Base N → ℝ) (lam : Base N → ℂ)
    (a : ℝ) (ha : 0 ≤ a) (hσ : ∀ z, 0 ≤ σ z ∧ σ z ≤ 1)
    (hsmoothed : 7 * a / 8 ≤ cyclicSmoothedModulusAverage N q (smoothingRadius N a) p X σ lam) :
    (a / 4) ^ 16 ≤ cyclicBoxMomentAverage N q (smoothingRadius N a) p σ lam := by
  have hm := cyclicSmoothedModulusAverage_le_three_boxMean hN q (smoothingRadius N a) p X σ lam hσ
  have hlow : a / 4 ≤ cyclicBoxNormAverage N q (smoothingRadius N a) p σ lam := by
    linarith only [hsmoothed, hm, ha]
  exact (pow_le_pow_left₀ (by positivity : 0 ≤ a / 4) hlow 16).trans
    (cyclicBoxNormAverage_pow_le hN q (smoothingRadius N a) p σ lam)

end GMZP0
