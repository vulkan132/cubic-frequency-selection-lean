import GMZP0.CyclicBounds

/-! Uniformly positive cyclic weighted averages for all original admissible data. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

/-- The constants precede N, the cyclic modulus, and all original data. No primality is needed for this step. -/
theorem uniform_positive_cyclic_average (κ η : ℝ) (hκ : 0 < κ) (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ M : ℕ, ∃ c ζ : ℝ, ∃ N₀ : ℕ,
      0 < M ∧ 0 < c ∧ 0 < ζ ∧ 0 < N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ (q : ℕ) [NeZero q], N ^ 2 < q → q ≤ 128 * N ^ 2 →
        ∀ (f : ℤ × ℤ → ℂ) (θ : Base N → Frequency) (lam : Base N → ℂ) (μ : Base N → ℝ),
          Admissible N κ η f θ lam μ →
        ∃ X : Finset (Fin N), ∃ D : Finset (Base N), ∃ a : ℕ,
          D = X ×ˢ safeRows N (N / M) ∧
          (∀ x : Fin N, x ∈ X ↔ a ≤ x.val ∧ x.val ≤ a + N / M) ∧
          c ≤ ∑ z ∈ D, μ z ∧
          (∀ x ∈ X, ∀ x' ∈ X, |(x'.val : ℤ) - (x.val : ℤ)| ≤ (N / M : ℕ)) ∧
          (∀ z ∈ D, SafeVertical (N : ℤ) (N / M : ℕ) (basePoint z).2) ∧
          η * (∑ z ∈ D, μ z) ≤ ‖weightedOriginalResponse N f θ (originalScaledWeight N μ D) lam‖ ∧
          ζ / 128 ≤ cyclicModulusAverage N q θ X (originalScaledWeight N μ D) lam ∧
          (∀ z ∈ D, μ z ≠ 0 → η ≤ (lam z * response N f z (θ z)).re) := by
  obtain ⟨M, c, ζ, N₀, hM, hc, hζ, hN₀, hwindow⟩ := uniform_positive_rerooted_average κ η hκ hη hη1
  refine ⟨M, c, ζ, N₀, hM, hc, hζ, hN₀, ?_⟩
  intro N hNth q _ hq hqUpper f θ lam μ hdata
  have hN : 0 < N := hN₀.trans_le hNth
  obtain ⟨X, D, a, hDX, hinterval, hmass, hgap, hsafe, hR, hA, hresponse⟩ :=
    hwindow N hNth f θ lam μ hdata
  refine ⟨X, D, a, hDX, hinterval, hmass, hgap, hsafe, hR, ?_, hresponse⟩
  apply cyclic_average_positive_of_finite hN hq hqUpper (N / M) θ X
    (originalScaledWeight N μ D) lam ζ hζ (Nat.div_le_self N M) hgap _ hA
  intro x y hσ
  exact hsafe (x, y) (originalScaledWeight_support μ D (x, y) hσ).1

end GMZP0
