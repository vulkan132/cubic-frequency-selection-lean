import GMZP0.UniformOriginalRealLift
import GMZP0.CyclicFrequencyAverage

/-! Uniform positive local fourth norm average for the same real lift and original responses. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

theorem uniform_original_local_four (κ η : ℝ) (hκ : 0 < κ) (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ M : ℕ, ∃ c a : ℝ, ∃ d : ℕ, ∃ E : ℝ, ∃ N₀ : ℕ,
      0 < M ∧ 0 < c ∧ 0 < a ∧ 0 < d ∧ 0 < E ∧ 0 < N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ (q : ℕ) [Fact q.Prime], N ^ 2 < q → q ≤ 128 * N ^ 2 →
        ∀ (f : ℤ × ℤ → ℂ) (θ : Base N → Frequency) (lam : Base N → ℂ) (μ : Base N → ℝ),
          Admissible N κ η f θ lam μ →
        ∃ X : Finset (Fin N), ∃ D : Finset (Base N), ∃ b : ℕ, ∃ F : Fin N → ZMod q → ℝ,
          D = X ×ˢ safeRows N (N / M) ∧
          (∀ x : Fin N, x ∈ X ↔ b ≤ x.val ∧ x.val ≤ b + N / M) ∧
          c ≤ ∑ z ∈ D, μ z ∧
          (∀ x ∈ X, ∀ x' ∈ X, |(x'.val : ℤ) - (x.val : ℤ)| ≤ (N / M : ℕ)) ∧
          (∀ z ∈ D, SafeVertical (N : ℤ) (N / M : ℕ) (basePoint z).2) ∧
          η * (∑ z ∈ D, μ z) ≤ ‖weightedOriginalResponse N f θ (originalScaledWeight N μ D) lam‖ ∧
          9 ≤ liftGridSize N E ∧
          (∀ x Y, ∃ k : ℤ, F x Y = (k : ℝ) / liftGridSize N E) ∧
          (∀ x Y, |F x Y| ≤ 3) ∧
          (∀ x Y, cyclicField N q (originalScaledWeight N μ D) 0 x Y = 0 → F x Y = 0) ∧
          (∀ x Y, 0 < cyclicField N q (originalScaledWeight N μ D) 0 x Y →
            ‖((F x Y : ℝ) : Frequency) - d • cyclicField N q θ 0 x Y‖ ≤ 19 * E / (N : ℝ) ^ 3) ∧
          (a / 4) ^ 16 / (4 * (57 : ℝ) ^ 16) ≤
            cyclicLocalFourthNormAverage N q (smoothingRadius N a) (liftGridSize N E)
              (originalScaledWeight N μ D) F ∧
          (∀ z ∈ D, μ z ≠ 0 → η ≤ (lam z * response N f z (θ z)).re) := by

  obtain ⟨M, c, a, d, E, N₀, hM, hc, ha, hd, hE, hN₀, hlift⟩ :=
    uniform_original_real_lift κ η hκ hη hη1
  refine ⟨M, c, a, d, E, N₀, hM, hc, ha, hd, hE, hN₀, ?_⟩
  intro N hNN q _ hq hqUpper f θ lam μ hdata
  obtain ⟨X, D, b, F, hDX, hinterval, hmass, hgap, hsafe, hR, hsize,
      hFgrid, hFbound, hFzero, hFerror, hFmass, hresponse⟩ :=
    hlift N hNN q hq hqUpper f θ lam μ hdata
  refine ⟨X, D, b, F, hDX, hinterval, hmass, hgap, hsafe, hR, hsize,
    hFgrid, hFbound, hFzero, hFerror, ?_, hresponse⟩
  rw [cyclicLocalFourthNormAverage_eq_mass (by omega : 0 < liftGridSize N E)
    (originalScaledWeight N μ D) F hFgrid hFbound]
  exact hFmass

end GMZP0
