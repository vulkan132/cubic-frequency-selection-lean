import GMZP0.LagStatistic
import GMZP0.PositiveSafeStatistic

/-! The uniform positive statistic is transferred through the proved complete lag reindexing. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

theorem original_window_statistic_eq_lag {N : ℕ} (H : ℕ) (p : Base N → Frequency)
    (X : Finset (Fin N)) (μ : Base N → ℝ) (D : Finset (Base N)) (lam : Base N → ℂ)
    (hHN : H ≤ N) (hX : ∀ x ∈ X, ∀ x' ∈ X, |horizontalGap x x'| ≤ H)
    (hsafe : ∀ z ∈ D, SafeVertical (N : ℤ) H (basePoint z).2) :
    finiteSignedDoubleStatistic N p X (alignedWeightVector (originalScaledWeight N μ D) lam) =
      lagSignedDoubleStatistic N p X (originalScaledWeight N μ D) lam := by
  apply finiteSignedDoubleStatistic_eq_lag H p X (originalScaledWeight N μ D) lam hHN hX
  intro x y hσ
  exact hsafe (x, y) (originalScaledWeight_support μ D (x, y) hσ).1

/-- All constants precede the original data; positivity now concerns the exact lag-indexed sum. -/
theorem uniform_positive_safe_lag_statistic (κ η : ℝ) (hκ : 0 < κ) (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ M : ℕ, ∃ c ζ : ℝ, ∃ N₀ : ℕ,
      0 < M ∧ 0 < c ∧ 0 < ζ ∧ 0 < N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ (f : ℤ × ℤ → ℂ) (θ : Base N → Frequency)
        (lam : Base N → ℂ) (μ : Base N → ℝ), Admissible N κ η f θ lam μ →
        ∃ X : Finset (Fin N), ∃ D : Finset (Base N), ∃ a : ℕ,
          D = X ×ˢ safeRows N (N / M) ∧
          (∀ x : Fin N, x ∈ X ↔ a ≤ x.val ∧ x.val ≤ a + N / M) ∧
          c ≤ ∑ z ∈ D, μ z ∧
          (∀ x ∈ X, ∀ x' ∈ X, |(x'.val : ℤ) - (x.val : ℤ)| ≤ (N / M : ℕ)) ∧
          (∀ z ∈ D, SafeVertical (N : ℤ) (N / M : ℕ) (basePoint z).2) ∧
          η * (∑ z ∈ D, μ z) ≤ ‖weightedOriginalResponse N f θ (originalScaledWeight N μ D) lam‖ ∧
          2 * ζ ≤ lagSignedDoubleStatistic N θ X (originalScaledWeight N μ D) lam ∧
          (∀ z ∈ D, μ z ≠ 0 → η ≤ (lam z * response N f z (θ z)).re) := by
  obtain ⟨M, c, ζ, N₀, hM, hc, hζ, hN₀, hwindow⟩ := uniform_positive_safe_statistic κ η hκ hη hη1
  refine ⟨M, c, ζ, N₀, hM, hc, hζ, hN₀, ?_⟩
  intro N hNth f θ lam μ hdata
  obtain ⟨X, D, a, hDX, hinterval, hmass, hgap, hsafe, hR, hS, hresponse⟩ :=
    hwindow N hNth f θ lam μ hdata
  refine ⟨X, D, a, hDX, hinterval, hmass, hgap, hsafe, hR, ?_, hresponse⟩
  rwa [original_window_statistic_eq_lag (N / M) θ X μ D lam (Nat.div_le_self N M) hgap hsafe] at hS

end GMZP0
