import GMZP0.UniformOriginalLocalFibers
import GMZP0.PairScale
import GMZP0.ConcatenationInterface

/-! Original weighted real seven-cubes, conditional only on the explicit external
concatenation input at this stage. Constants precede all original data; a single
real lift, original weights and full original responses remain in the conclusion. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

theorem uniform_original_real_seven_of_concatenation (hconcat : CyclicConcatenationInput)
    (κ η : ℝ) (hκ : 0 < κ) (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ M : ℕ, ∃ c : ℝ, ∃ d : ℕ, ∃ E χ : ℝ, ∃ N₀ : ℕ,
      0 < M ∧ 0 < c ∧ 0 < d ∧ 0 < E ∧ 0 < χ ∧ 0 < N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ (q : ℕ) [Fact q.Prime], 4 * N ^ 2 < q → q ≤ 128 * N ^ 2 →
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
          χ ≤ cyclicGlobalRealSevenMass N q (originalScaledWeight N μ D) F ∧
          (∀ z ∈ D, μ z ≠ 0 → η ≤ (lam z * response N f z (θ z)).re) := by
  obtain ⟨M, c, a, d, E, B, hM, hc, ha, hd, hE, hB, hfour⟩ :=
    uniform_original_local_fibres κ η hκ hη hη1
  let β : ℝ := (a / 4) ^ 16 / (4 * 57 ^ 16)
  have hβ : 0 < β := by dsimp [β]; positivity
  obtain ⟨u, hu, hu8, hfamily⟩ := hconcat β hβ
  obtain ⟨L, hL, hscale⟩ := uniform_shrunk_radius_threshold a u ha hu
  let χ := β / 2 * pairSeventhLower a u
  have hχ : 0 < χ := mul_pos (by positivity) (pairSeventhLower_pos a u ha hu)
  refine ⟨M, c, d, E, χ, max B L, hM, hc, hd, hE, hχ, hB.trans_le (le_max_left _ _), ?_⟩
  intro N hNN q _ hq hqUpper f θ lam μ hdata
  have hBN : B ≤ N := (le_max_left _ _).trans hNN
  have hLN : L ≤ N := (le_max_right _ _).trans hNN
  have hN : 0 < N := hB.trans_le hBN
  obtain ⟨X, D, b, F, hDX, hinterval, hmass, hgap, hsafe, hR, hsize,
      hFgrid, hFbound, hFzero, hFerror, hFmass, hgood, hresponse⟩ :=
    hfour N hBN q (by omega : N ^ 2 < q) hqUpper f θ lam μ hdata
  have ha256 := original_scale_bound_of_local_four hN (by omega : 0 < liftGridSize N E)
    μ D hdata.2.2.1 F a hFmass
  have hs := shrunk_radius_short hN a u ha.le ha256 hu hu8
  obtain ⟨hscale₁, hscale₂⟩ := hscale N hLN
  obtain ⟨hℓLower, hsLower⟩ := shrunk_radius_lower a u hu hscale₁ hscale₂
  have hℓ : 0 < smoothingRadius N a := by
    have he : (0 : ℝ) < smoothingRadius N a := by linarith
    exact_mod_cast he
  refine ⟨X, D, b, F, hDX, hinterval, hmass, hgap, hsafe, hR, hsize,
    hFgrid, hFbound, hFzero, hFerror, ?_, hresponse⟩
  apply cyclic_real_seven_of_pair_family hN (by omega : 0 < liftGridSize N E)
    hq hqUpper a u β ha hu hs hsLower (originalScaledWeight N μ D) F
    (originalScaledWeight_bounds hN μ D hdata.2.2.1) hFgrid hFbound hgood
  intro x j hlocal
  exact hfamily N q (smoothingRadius N a) hN hℓ _
    (modulatedCyclicField_norm_le N q (liftGridSize N E) (originalScaledWeight N μ D) F
      (originalScaledWeight_bounds hN μ D hdata.2.2.1) x j) hlocal

end GMZP0
