import GMZP0.UniformOriginalLocalFour
import GMZP0.LocalGoodFibers

/-! Uniform positive proportions of local-norm fibres, keeping all original data and one real lift. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

theorem uniform_original_local_fibres (κ η : ℝ) (hκ : 0 < κ) (hη : 0 < η) (hη1 : η ≤ 1) :
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
          ((a / 4) ^ 16 / (4 * (57 : ℝ) ^ 16)) / 2 ≤
            cyclicLocalGoodFiberMass N q (smoothingRadius N a) (liftGridSize N E)
              (originalScaledWeight N μ D) F ((a / 4) ^ 16 / (4 * (57 : ℝ) ^ 16)) ∧
          (∀ z ∈ D, μ z ≠ 0 → η ≤ (lam z * response N f z (θ z)).re) := by

  obtain ⟨M, c, a, d, E, N₀, hM, hc, ha, hd, hE, hN₀, hfour⟩ :=
    uniform_original_local_four κ η hκ hη hη1
  refine ⟨M, c, a, d, E, N₀, hM, hc, ha, hd, hE, hN₀, ?_⟩
  intro N hNN q _ hq hqUpper f θ lam μ hdata
  have hN : 0 < N := hN₀.trans_le hNN
  obtain ⟨X, D, b, F, hDX, hinterval, hmass, hgap, hsafe, hR, hsize,
      hFgrid, hFbound, hFzero, hFerror, hFmass, hresponse⟩ :=
    hfour N hNN q hq hqUpper f θ lam μ hdata
  refine ⟨X, D, b, F, hDX, hinterval, hmass, hgap, hsafe, hR, hsize,
    hFgrid, hFbound, hFzero, hFerror, hFmass, ?_, hresponse⟩
  exact cyclic_local_good_fibres hN (by omega : 0 < liftGridSize N E)
    (originalScaledWeight N μ D) F (originalScaledWeight_bounds hN μ D hdata.2.2.1)
    _ (by positivity) hFmass

end GMZP0
