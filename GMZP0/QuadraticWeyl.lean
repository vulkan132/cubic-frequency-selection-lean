import GMZP0.UniformAffineReturns
import GMZP0.PolynomialDifferencing

/-! Quantitative quadratic inverse Weyl, with uniform constants and all circle coefficients. -/

noncomputable section
namespace GMZP0

theorem uniform_quadratic_weyl_large (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ Q : ℕ, ∃ E : ℝ, ∃ N₀ : ℕ, 0 < Q ∧ 0 < E ∧ 0 < N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ a₂ a₁ a₀ : Frequency,
        ρ ≤ ‖integerIntervalMean N (fun t => circleCharacter (quadraticCirclePolynomial a₂ a₁ a₀ t))‖ →
        ∃ q : ℕ, 0 < q ∧ q ≤ Q ∧ ‖q • a₂‖ ≤ E / (N : ℝ) ^ 2 := by
  obtain ⟨Q, E, N₁, hQ, hE, hN₁, hrec⟩ :=
    uniform_affine_dense_returns (ρ ^ 2 / 4) (4 / ρ ^ 2) (by positivity) (by positivity)
  let N₀ := max N₁ (Nat.ceil (2 / ρ ^ 2) + 1)
  have hN₀ : 0 < N₀ := lt_of_lt_of_le hN₁ (le_max_left _ _)
  refine ⟨2 * Q, 4 * E / ρ ^ 2, N₀, by omega, by positivity, hN₀, ?_⟩
  intro N hNN a₂ a₁ a₀ hlarge
  have hN : 0 < N := lt_of_lt_of_le hN₀ hNN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hNN₁ : N₁ ≤ N := le_trans (le_max_left _ _) hNN
  have hscale : 2 ≤ (N : ℝ) * ρ ^ 2 := by
    have hc : Nat.ceil (2 / ρ ^ 2) ≤ N := by dsimp [N₀] at hNN; omega
    have hr : 2 / ρ ^ 2 ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hc)
    exact (div_le_iff₀ (by positivity : 0 < ρ ^ 2)).mp hr
  obtain ⟨s, hs, hcard, hreturn⟩ := quadratic_many_returns hN a₂ a₁ a₀ hρ hlarge hscale
  have hs' : s ⊆ Finset.Icc (-(N : ℤ)) N :=
    hs.trans (Finset.erase_subset _ _)
  have hε : 0 ≤ 4 / (ρ ^ 2 * (N : ℝ)) := by positivity
  have hεN : (4 / (ρ ^ 2 * (N : ℝ))) * (N : ℝ) ≤ 4 / ρ ^ 2 := by
    field_simp
    norm_num
  have hreturns : ∀ h ∈ s, ‖h • ((2 : ℤ) • a₂) + (0 : Frequency)‖ ≤ 4 / (ρ ^ 2 * (N : ℝ)) := by
    intro h hh
    simpa only [add_zero, ← mul_zsmul, mul_comm h 2] using hreturn h hh
  obtain ⟨q, hq, hqQ, hb⟩ := hrec N hNN₁ ((2 : ℤ) • a₂) 0
    (4 / (ρ ^ 2 * (N : ℝ))) s hε hεN hs' (by nlinarith [hcard]) hreturns
  have heq : (2 * q : ℕ) • a₂ = q • ((2 : ℤ) • a₂) := by
    rw [mul_comm 2 q, mul_nsmul]
    norm_cast
    exact smul_comm _ _ _
  refine ⟨2 * q, by omega, Nat.mul_le_mul_left 2 hqQ, ?_⟩
  rw [heq]
  convert hb using 1; field_simp

/-- Small scales are absorbed by the circle half-period bound, so every N>0 is covered. -/
theorem uniform_quadratic_weyl (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ Q : ℕ, ∃ E : ℝ, 0 < Q ∧ 0 < E ∧
      ∀ N : ℕ, 0 < N → ∀ a₂ a₁ a₀ : Frequency,
        ρ ≤ ‖integerIntervalMean N (fun t => circleCharacter (quadraticCirclePolynomial a₂ a₁ a₀ t))‖ →
        ∃ q : ℕ, 0 < q ∧ q ≤ Q ∧ ‖q • a₂‖ ≤ E / (N : ℝ) ^ 2 := by
  obtain ⟨Q, E, N₀, hQ, hE, _, hlarge⟩ := uniform_quadratic_weyl_large ρ hρ
  refine ⟨Q, max E ((N₀ : ℝ) ^ 2), hQ, hE.trans_le (le_max_left _ _), ?_⟩
  intro N hN a₂ a₁ a₀ hmean
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  by_cases hNN : N₀ ≤ N
  · obtain ⟨q, hq, hqQ, hb⟩ := hlarge N hNN a₂ a₁ a₀ hmean
    exact ⟨q, hq, hqQ, hb.trans (div_le_div_of_nonneg_right (le_max_left _ _) (sq_nonneg _))⟩
  · have hNle : (N : ℝ) ≤ N₀ := by exact_mod_cast (le_of_lt (lt_of_not_ge hNN))
    have hNsq : (N : ℝ) ^ 2 ≤ (N₀ : ℝ) ^ 2 := pow_le_pow_left₀ hNR.le hNle 2
    have hhalf : ‖a₂‖ ≤ (1 : ℝ) / 2 := by
      simpa using AddCircle.norm_le_half_period (1 : ℝ) (x := a₂) one_ne_zero
    refine ⟨1, by omega, hQ, ?_⟩
    rw [one_nsmul]
    calc
      ‖a₂‖ ≤ 1 := by linarith
      _ ≤ max E ((N₀ : ℝ) ^ 2) / (N : ℝ) ^ 2 := by
        apply (le_div_iff₀ (by positivity : 0 < (N : ℝ) ^ 2)).2
        simpa only [one_mul] using hNsq.trans (le_max_right E _)

end GMZP0
