import GMZP0.UniformOriginalRealSeven
import GMZP0.PreparedSevenFibers

/-! Uniform preparation for the external structural input, starting from the
original response. The only deep input here is the explicit concatenation
hypothesis inherited from F21; no approximate-polynomial theorem is assumed. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

theorem uniform_original_prepared_seven_of_concatenation (hconcat : CyclicConcatenationInput)
    (κ η : ℝ) (hκ : 0 < κ) (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ M : ℕ, ∃ c : ℝ, ∃ d : ℕ, ∃ E χ : ℝ, ∃ N₀ : ℕ,
      0 < M ∧ 0 < c ∧ 0 < d ∧ 0 < E ∧ 0 < χ ∧ 0 < N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ (q : ℕ) [Fact q.Prime], 64 * N ^ 2 < q → q ≤ 128 * N ^ 2 →
        ∀ (f : ℤ × ℤ → ℂ) (θ : Base N → Frequency) (lam : Base N → ℂ) (μ : Base N → ℝ),
          Admissible N κ η f θ lam μ →
        ∃ X : Finset (Fin N), ∃ D : Finset (Base N), ∃ b : ℕ,
        ∃ F : Fin N → ZMod q → ℝ, ∃ H : Finset (Fin N),
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
          χ / 4 * N ≤ H.card ∧
          (∀ x ∈ H, χ / 4 * (q : ℝ) ^ 8 ≤ globalDistinctThresholdCubeCount 7
            (fun Y => cyclicField N q (originalScaledWeight N μ D) 0 x Y) (F x) (χ / 512)) ∧
          (∀ z ∈ D, μ z ≠ 0 → η ≤ (lam z * response N f z (θ z)).re) := by
  obtain ⟨M, c, d, E, χ, B, hM, hc, hd, hE, hχ, hB, hseven⟩ :=
    uniform_original_real_seven_of_concatenation hconcat κ η hκ hη hη1
  obtain ⟨L, hL, hcollision⟩ := uniform_seven_collision_threshold χ hχ
  refine ⟨M, c, d, E, χ, max B L, hM, hc, hd, hE, hχ, hB.trans_le (le_max_left _ _), ?_⟩
  intro N hNN q _ hq hqUpper f θ lam μ hdata
  have hBN : B ≤ N := (le_max_left _ _).trans hNN
  have hLN : L ≤ N := (le_max_right _ _).trans hNN
  have hN : 0 < N := hB.trans_le hBN
  have hqsmall : N ^ 2 < q := by omega
  obtain ⟨X, D, b, F, hDX, hinterval, hmass, hgap, hsafe, hR, hsize,
    hFgrid, hFbound, hFzero, hFerror, hFmass, hresponse⟩ :=
    hseven N hBN q (by omega : 4 * N ^ 2 < q) hqUpper f θ lam μ hdata
  let H := preparedSevenFibers N q (originalScaledWeight N μ D) F χ
  have hprepared := cyclic_prepared_seven_lower hN (originalScaledWeight N μ D) F
    (originalScaledWeight_bounds hN μ D hdata.2.2.1) χ hχ hFmass (hcollision N hLN q hqsmall)
  refine ⟨X, D, b, F, H, hDX, hinterval, hmass, hgap, hsafe, hR, hsize,
    hFgrid, hFbound, hFzero, hFerror, hFmass, ?_, ?_, hresponse⟩
  · exact preparedSevenFibers_card hN _ F χ hχ hprepared
  · exact fun x hx => preparedSevenFibers_cube_count _ F χ x hx

end GMZP0
