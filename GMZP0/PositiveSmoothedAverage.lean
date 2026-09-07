import GMZP0.CyclicSmoothing

/-! Uniform smoothing lower bound with the original mass and pointwise response retained. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

theorem uniform_positive_smoothed_average (κ η : ℝ) (hκ : 0 < κ) (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ M : ℕ, ∃ c a : ℝ, ∃ N₀ : ℕ,
      0 < M ∧ 0 < c ∧ 0 < a ∧ 0 < N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ (q : ℕ) [NeZero q], N ^ 2 < q → q ≤ 128 * N ^ 2 →
        ∀ (f : ℤ × ℤ → ℂ) (θ : Base N → Frequency) (lam : Base N → ℂ) (μ : Base N → ℝ),
          Admissible N κ η f θ lam μ →
        ∃ X : Finset (Fin N), ∃ D : Finset (Base N), ∃ b : ℕ,
          D = X ×ˢ safeRows N (N / M) ∧
          (∀ x : Fin N, x ∈ X ↔ b ≤ x.val ∧ x.val ≤ b + N / M) ∧
          c ≤ ∑ z ∈ D, μ z ∧
          (∀ x ∈ X, ∀ x' ∈ X, |(x'.val : ℤ) - (x.val : ℤ)| ≤ (N / M : ℕ)) ∧
          (∀ z ∈ D, SafeVertical (N : ℤ) (N / M : ℕ) (basePoint z).2) ∧
          η * (∑ z ∈ D, μ z) ≤ ‖weightedOriginalResponse N f θ (originalScaledWeight N μ D) lam‖ ∧
          a ≤ cyclicModulusAverage N q θ X (originalScaledWeight N μ D) lam ∧
          7 * a / 8 ≤ cyclicSmoothedModulusAverage N q (smoothingRadius N a)
            θ X (originalScaledWeight N μ D) lam ∧
          (∀ z ∈ D, μ z ≠ 0 → η ≤ (lam z * response N f z (θ z)).re) := by
  obtain ⟨M, c, ζ, N₀, hM, hc, hζ, hN₀, hwindow⟩ := uniform_positive_cyclic_average κ η hκ hη hη1
  have ha : 0 < ζ / 128 := div_pos hζ (by norm_num)
  refine ⟨M, c, ζ / 128, N₀, hM, hc, ha, hN₀, ?_⟩
  intro N hNth q _ hq hqUpper f θ lam μ hdata
  have hN : 0 < N := hN₀.trans_le hNth
  obtain ⟨X, D, b, hDX, hinterval, hmass, hgap, hsafe, hR, hA, hresponse⟩ :=
    hwindow N hNth q hq hqUpper f θ lam μ hdata
  refine ⟨X, D, b, hDX, hinterval, hmass, hgap, hsafe, hR, hA, ?_, hresponse⟩
  exact cyclic_smoothed_average_positive hN q θ X (originalScaledWeight N μ D) lam
    (ζ / 128) ha.le (originalScaledWeight_bounds hN μ D hdata.2.2.1) hdata.2.1 hA

end GMZP0
