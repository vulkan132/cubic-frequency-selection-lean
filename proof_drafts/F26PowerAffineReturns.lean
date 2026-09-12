import GMZP0.UniformAffineReturns
import GMZP0.DenominatorFiber
import Mathlib.Tactic.Module

/-! Scale-explicit affine returns, including the actual bounded-denominator fiber. -/
noncomputable section
namespace GMZP0

/-- The recurrence constants work for every positive integer error exponent. -/
theorem uniform_affine_power_returns (ρ C : ℝ) (hρ : 0 < ρ) (hC : 0 < C) :
    ∃ Q : ℕ, ∃ E : ℝ, ∃ N₀ : ℕ, 0 < Q ∧ 0 < E ∧ 0 < N₀ ∧
      ∀ m : ℕ, 1 ≤ m → ∀ N : ℕ, N₀ ≤ N → ∀ a b : Frequency, ∀ s : Finset ℤ,
        s ⊆ Finset.Icc (-(N : ℤ)) N → ρ * (N : ℝ) ≤ s.card →
        (∀ k ∈ s, ‖k • a + b‖ ≤ C / (N : ℝ) ^ m) →
        ∃ q : ℕ, 0 < q ∧ q ≤ Q ∧ ‖q • a‖ ≤ E / (N : ℝ) ^ (m + 1) := by
  obtain ⟨Q, E, N₀, hQ, hE, hN₀, hr⟩ := uniform_affine_dense_returns ρ C hρ hC.le
  refine ⟨Q, E * C, N₀, hQ, by positivity, hN₀, ?_⟩
  intro m hm N hN a b s hs hd hp
  have hn : 0 < N := hN₀.trans_le hN
  have hnR : (0 : ℝ) < N := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hn
  have hpN : (N : ℝ) ≤ (N : ℝ) ^ m := by
    simpa only [pow_one] using pow_le_pow_right₀ hn1 hm
  have heps : (C / (N : ℝ) ^ m) * N ≤ C := by
    calc
      _ = (C * N) / (N : ℝ) ^ m := by ring
      _ ≤ C := (div_le_iff₀ (pow_pos hnR m)).2 (mul_le_mul_of_nonneg_left hpN hC.le)
  obtain ⟨q, hq, hqQ, hb⟩ := hr N hN a b (C / (N : ℝ) ^ m) s
    (by positivity) heps hs hd hp
  refine ⟨q, hq, hqQ, ?_⟩
  convert hb using 1
  rw [pow_succ]
  ring

/-- Pigeonholing actual bounded positive multipliers preserves a quantitative affine return conclusion. -/
theorem uniform_bounded_multiplier_affine_returns (ρ C : ℝ) (hρ : 0 < ρ) (hC : 0 < C)
    (D : ℕ) (hD : 0 < D) :
    ∃ Q : ℕ, ∃ E : ℝ, ∃ N₀ : ℕ, 0 < Q ∧ 0 < E ∧ 0 < N₀ ∧
      ∀ m : ℕ, 1 ≤ m → ∀ N : ℕ, N₀ ≤ N → ∀ a b : Frequency, ∀ s : Finset ℤ,
        s ⊆ Finset.Icc (-(N : ℤ)) N → ρ * (N : ℝ) ≤ s.card →
        (∀ k ∈ s, ∃ d : ℕ, 0 < d ∧ d ≤ D ∧ ‖d • (k • a + b)‖ ≤ C / (N : ℝ) ^ m) →
        ∃ q : ℕ, 0 < q ∧ q ≤ Q ∧ ‖q • a‖ ≤ E / (N : ℝ) ^ (m + 1) := by
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  obtain ⟨Q, E, N₀, hQ, hE, hN₀, hr⟩ := uniform_affine_power_returns (ρ / D) C (by positivity) hC
  refine ⟨Q * D, E, N₀, by positivity, hE, hN₀, ?_⟩
  intro m hm N hN a b s hs hd hp
  obtain ⟨d, hd0, hdD, t, hts, hcard, ht⟩ := finite_positive_denominator_fiber hD s
    (fun k d => ‖d • (k • a + b)‖ ≤ C / (N : ℝ) ^ m) hp
  have hden : (ρ / D) * (N : ℝ) ≤ t.card := by
    calc
      _ = (ρ * N) / D := by ring
      _ ≤ (s.card : ℝ) / D := div_le_div_of_nonneg_right hd hDR.le
      _ ≤ _ := hcard
  have hret : ∀ k ∈ t, ‖k • (d • a) + d • b‖ ≤ C / (N : ℝ) ^ m := by
    intro k hk
    have he : k • (d • a) + d • b = d • (k • a + b) := by module
    rw [he]
    exact ht k hk
  obtain ⟨q, hq, hqQ, hb⟩ := hr m hm N hN (d • a) (d • b) t (hts.trans hs) hden hret
  have he : (q * d) • a = q • (d • a) := by module
  exact ⟨q * d, by positivity, Nat.mul_le_mul hqQ hdD, by simpa only [he] using hb⟩

end GMZP0
