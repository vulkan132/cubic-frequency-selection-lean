import GMZP0.CyclicCubePhase

/-! Original admissible data give a positive fully expanded and rerooted cube average. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

theorem uniform_positive_cube_average (κ η : ℝ) (hκ : 0 < κ) (hη : 0 < η) (hη1 : η ≤ 1) :
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
          (a / 4) ^ 16 ≤ (cyclicRerootedCubeAverage N q (smoothingRadius N a)
            θ (originalScaledWeight N μ D) lam).re ∧
          (∀ z ∈ D, μ z ≠ 0 → η ≤ (lam z * response N f z (θ z)).re) := by
  obtain ⟨M, c, a, N₀, hM, hc, ha, hN₀, hwindow⟩ := uniform_positive_box_average κ η hκ hη hη1
  refine ⟨M, c, a, N₀, hM, hc, ha, hN₀, ?_⟩
  intro N hNth q _ hq hqUpper f θ lam μ hdata
  obtain ⟨X, D, b, hDX, hinterval, hmass, hgap, hsafe, hR, hbox, hresponse⟩ :=
    hwindow N hNth q hq hqUpper f θ lam μ hdata
  refine ⟨X, D, b, hDX, hinterval, hmass, hgap, hsafe, hR, ?_, hresponse⟩
  rw [cyclicRerootedCubeAverage_eq_moment, Complex.ofReal_re]
  exact hbox

end GMZP0
