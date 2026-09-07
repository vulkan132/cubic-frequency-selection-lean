import GMZP0.UniformCubeAverage

/-! Separate the complete t average; all sixteen original weights stay outside it. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

abbrev CubeWeylParameters (N q ℓ : ℕ) :=
  Fin N × horizontalShiftLabels N × ZMod q × fullLagLabels N × CubeShiftPairs ℓ

def cubeWeylReindex (N q ℓ : ℕ) :
    (CubeWeylParameters N q ℓ × Fin N) ≃ (CyclicBoxSamplingSpace N q × CubeShiftPairs ℓ) where
  toFun z := (((z.1.1, z.1.2.1, z.1.2.2.1, z.2), z.1.2.2.2.1), z.1.2.2.2.2)
  invFun z := ((z.1.1.1, z.1.1.2.1, z.1.1.2.2.1, z.1.2, z.2), z.1.1.2.2.2)
  left_inv z := by rcases z with ⟨⟨x, h, Y, k, u⟩, t⟩; rfl
  right_inv z := by rcases z with ⟨⟨⟨x, h, Y, t⟩, k⟩, u⟩; rfl

theorem card_cubeWeylParameters (N q ℓ : ℕ) [NeZero q] :
    Fintype.card (CubeWeylParameters N q ℓ) =
      2 * q * N ^ 2 * (2 * N + 1) * (2 * ℓ + 1) ^ 8 := by
  simp only [CubeWeylParameters, CubeShiftPairs, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_coe, horizontalShiftLabels_card, ZMod.card, fullLagLabels_card,
    Fintype.card_fun, card_smoothingShiftLabels]
  ring

def cyclicCubeTimeAverage (N q ℓ : ℕ) (p : Base N → Frequency) (x : Fin N) (Y : ZMod q)
    (h k : ℤ) (u : CubeShiftPairs ℓ) : ℂ :=
  complexUniformMean (fun t : Fin N => circleCharacter (cyclicCubePhase N q ℓ p x Y h k u (label t)))

theorem cyclicRerootedCubeAverage_split_time (N q ℓ : ℕ) [NeZero q] (p : Base N → Frequency)
    (σ : Base N → ℝ) (lam : Base N → ℂ) :
    cyclicRerootedCubeAverage N q ℓ p σ lam =
      complexUniformMean (fun z : CubeWeylParameters N q ℓ =>
        (cyclicCubeWeight N q ℓ σ z.1 z.2.2.1 z.2.1.val z.2.2.2.2 : ℂ) *
        cyclicCubeAlignment N q ℓ lam z.1 z.2.2.1 z.2.1.val z.2.2.2.2 *
        cyclicCubeTimeAverage N q ℓ p z.1 z.2.2.1 z.2.1.val z.2.2.2.1.val z.2.2.2.2) := by
  have he : complexUniformMean (fun z : CubeWeylParameters N q ℓ × Fin N =>
      cyclicRerootedCubeProduct N q ℓ p σ lam z.1.1 z.1.2.2.1 z.1.2.1.val
        (label z.2) z.1.2.2.2.1.val z.1.2.2.2.2) = cyclicRerootedCubeAverage N q ℓ p σ lam := by
    calc
      _ = complexUniformMean (fun z : CyclicBoxSamplingSpace N q × CubeShiftPairs ℓ =>
          cyclicRerootedCubeProduct N q ℓ p σ lam z.1.1.1 z.1.1.2.2.1 z.1.1.2.1.val
            (label z.1.1.2.2.2) z.1.2.val z.2) :=
        complexUniformMean_equiv (cubeWeylReindex N q ℓ) _
      _ = cyclicRerootedCubeAverage N q ℓ p σ lam :=
        complexUniformMean_prod (fun (z : CyclicBoxSamplingSpace N q) (u : CubeShiftPairs ℓ) =>
          cyclicRerootedCubeProduct N q ℓ p σ lam z.1.1 z.1.2.2.1 z.1.2.1.val
            (label z.1.2.2.2) z.2.val u)
  rw [← he, complexUniformMean_prod (fun (z : CubeWeylParameters N q ℓ) (t : Fin N) =>
    cyclicRerootedCubeProduct N q ℓ p σ lam z.1 z.2.2.1 z.2.1.val
      (label t) z.2.2.2.1.val z.2.2.2.2)]
  simp only [cyclicRerootedCubeProduct_factorized, complexUniformMean_const_mul,
    cyclicCubeTimeAverage]

def cyclicWeightedTimeNorm (N q ℓ : ℕ) [NeZero q] (p : Base N → Frequency)
    (σ : Base N → ℝ) : ℝ :=
  realUniformMean (fun z : CubeWeylParameters N q ℓ =>
    cyclicCubeWeight N q ℓ σ z.1 z.2.2.1 z.2.1.val z.2.2.2.2 *
      ‖cyclicCubeTimeAverage N q ℓ p z.1 z.2.2.1 z.2.1.val z.2.2.2.1.val z.2.2.2.2‖)

theorem cyclicCubeTimeAverage_norm_le {N : ℕ} (hN : 0 < N) (q ℓ : ℕ)
    (p : Base N → Frequency) (x : Fin N) (Y : ZMod q) (h k : ℤ) (u : CubeShiftPairs ℓ) :
    ‖cyclicCubeTimeAverage N q ℓ p x Y h k u‖ ≤ 1 := by
  let : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  exact norm_complexUniformMean_le _ 1 (fun _ => (norm_circleCharacter _).le)

theorem cyclicCubeAverage_le_weightedTimeNorm (N q ℓ : ℕ) [NeZero q]
    (p : Base N → Frequency) (σ : Base N → ℝ) (lam : Base N → ℂ)
    (hσ : ∀ z, 0 ≤ σ z ∧ σ z ≤ 1) (hlam : ∀ z, ‖lam z‖ = 1) :
    (cyclicRerootedCubeAverage N q ℓ p σ lam).re ≤ cyclicWeightedTimeNorm N q ℓ p σ := by
  rw [cyclicRerootedCubeAverage_split_time, complexUniformMean_re]
  apply realUniformMean_mono
  intro z
  calc
    _ ≤ ‖(cyclicCubeWeight N q ℓ σ z.1 z.2.2.1 z.2.1.val z.2.2.2.2 : ℂ) *
        cyclicCubeAlignment N q ℓ lam z.1 z.2.2.1 z.2.1.val z.2.2.2.2 *
        cyclicCubeTimeAverage N q ℓ p z.1 z.2.2.1 z.2.1.val z.2.2.2.1.val z.2.2.2.2‖ :=
      Complex.re_le_norm _
    _ = _ := by
      rw [norm_mul, norm_mul, cyclicCubeAlignment_norm N q ℓ lam _ _ _ _ hlam,
        Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (cyclicCubeWeight_bounds N q ℓ σ _ _ _ _ hσ).1, mul_one]

end GMZP0
