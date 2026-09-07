import GMZP0.CyclicGlobalLift

/-! A simultaneous real lift on positive original cube mass, with all original responses retained. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

theorem uniform_original_real_lift (κ η : ℝ) (hκ : 0 < κ) (hη : 0 < η) (hη1 : η ≤ 1) :
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
            cyclicRealCubeMass N q (smoothingRadius N a) (originalScaledWeight N μ D) F ∧
          (∀ z ∈ D, μ z ≠ 0 → η ≤ (lam z * response N f z (θ z)).re) := by
  obtain ⟨M, c, a, d, E, N₁, hM, hc, ha, hd, hE, hN₁, hcubes⟩ :=
    uniform_distinct_original_cube_capture κ η hκ hη hη1
  obtain ⟨N₂, hN₂, hgrid⟩ := uniform_lift_grid_scale E hE
  refine ⟨M, c, a, d, E, max N₁ N₂, hM, hc, ha, hd, hE,
    hN₁.trans_le (le_max_left _ _), ?_⟩
  intro N hNN q _ hq hqUpper f θ lam μ hdata
  have hNN₁ : N₁ ≤ N := (le_max_left _ _).trans hNN
  have hNN₂ : N₂ ≤ N := (le_max_right _ _).trans hNN
  have hN : 0 < N := hN₁.trans_le hNN₁
  obtain ⟨X, D, b, hDX, hinterval, hmass, hgap, hsafe, hR, hnear, hresponse⟩ :=
    hcubes N hNN₁ q hq hqUpper f θ lam μ hdata
  obtain ⟨hsize, hscale, herror⟩ := hgrid N hNN₂
  obtain ⟨F, hFgrid, hFbound, hFzero, hFerror, hFmass⟩ :=
    exists_cyclic_real_lift (q := q) (ℓ := smoothingRadius N a) hsize θ (originalScaledWeight N μ D)
      (originalScaledWeight_bounds hN μ D hdata.2.2.1) d E hscale herror
  refine ⟨X, D, b, F, hDX, hinterval, hmass, hgap, hsafe, hR, hsize,
    hFgrid, hFbound, hFzero, hFerror, ?_, hresponse⟩
  calc
    (a / 4) ^ 16 / (4 * (57 : ℝ) ^ 16) = (1 / (57 : ℝ) ^ 16) * ((a / 4) ^ 16 / 4) := by ring
    _ ≤ (1 / (57 : ℝ) ^ 16) * cyclicDistinctPositiveCubeNearMass N q (smoothingRadius N a)
        θ (originalScaledWeight N μ D) d E := mul_le_mul_of_nonneg_left hnear (by positivity)
    _ ≤ _ := hFmass

end GMZP0
