import GMZP0.CubicWeylReturns

/-! The cubic leading-coefficient inverse theorem at scale N⁻³, uniformly before all data. -/

noncomputable section
namespace GMZP0

theorem uniform_cubic_weyl_large (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ Q : ℕ, ∃ E : ℝ, ∃ N₀ : ℕ, 0 < Q ∧ 0 < E ∧ 0 < N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ a₃ a₂ a₁ a₀ : Frequency,
        ρ ≤ ‖integerIntervalMean N (fun t => circleCharacter (cubicCirclePolynomial a₃ a₂ a₁ a₀ t))‖ →
        ∃ q : ℕ, 0 < q ∧ q ≤ Q ∧ ‖q • a₃‖ ≤ E / (N : ℝ) ^ 3 := by
  obtain ⟨Q, E, hQ, hE, hret⟩ := uniform_cubic_dense_returns ρ hρ
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  obtain ⟨Q₁, E₁, N₁, hQ₁, hE₁, hN₁, hrec⟩ :=
    uniform_affine_dense_returns (ρ ^ 2 / (4 * (Q : ℝ))) E (by positivity) hE.le
  let N₀ := max N₁ (Nat.ceil (2 / ρ ^ 2) + 1)
  have hN₀ : 0 < N₀ := lt_of_lt_of_le hN₁ (le_max_left _ _)
  refine ⟨3 * Q * Q₁, E₁ * E, N₀, by positivity, by positivity, hN₀, ?_⟩
  intro N hNN a₃ a₂ a₁ a₀ hlarge
  have hN : 0 < N := lt_of_lt_of_le hN₀ hNN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNN₁ : N₁ ≤ N := le_trans (le_max_left _ _) hNN
  have hscale : 2 ≤ (N : ℝ) * ρ ^ 2 := by
    have hc : Nat.ceil (2 / ρ ^ 2) ≤ N := by dsimp [N₀] at hNN; omega
    have hr : 2 / ρ ^ 2 ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hc)
    exact (div_le_iff₀ (by positivity : 0 < ρ ^ 2)).mp hr
  obtain ⟨q, hq, hqQ, s, hs, hcard, hreturn⟩ := hret N hN hscale a₃ a₂ a₁ a₀ hlarge
  have hs' : s ⊆ Finset.Icc (-(N : ℤ)) N := hs.trans (Finset.erase_subset _ _)
  have hεN : (E / (N : ℝ) ^ 2) * (N : ℝ) ≤ E := by
    calc
      _ = E / (N : ℝ) := by field_simp
      _ ≤ E := (div_le_self hE.le hN1)
  obtain ⟨q₁, hq₁, hq₁Q, hb⟩ := hrec N hNN₁ ((3 * (q : ℤ)) • a₃) 0
    (E / (N : ℝ) ^ 2) s (by positivity) hεN hs' hcard
    (by simpa only [add_zero] using hreturn)
  have heq : (3 * q * q₁ : ℕ) • a₃ = q₁ • ((3 * (q : ℤ)) • a₃) := by
    have hleft : (3 * q * q₁ : ℕ) • a₃ = ((3 * q * q₁ : ℕ) : ℤ) • a₃ := by rw [natCast_zsmul]
    have hright : q₁ • ((3 * (q : ℤ)) • a₃) = (q₁ : ℤ) • ((3 * (q : ℤ)) • a₃) := by rw [natCast_zsmul]
    rw [hleft, hright, ← mul_zsmul]
    push_cast
    congr 1
    ring
  refine ⟨3 * q * q₁, by positivity, Nat.mul_le_mul (Nat.mul_le_mul_left 3 hqQ) hq₁Q, ?_⟩
  rw [heq]
  convert hb using 1; field_simp

/-- Every positive scale is covered; the bound and finite denominator range depend only on rho. -/
theorem uniform_cubic_weyl (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ Q : ℕ, ∃ E : ℝ, 0 < Q ∧ 0 < E ∧
      ∀ N : ℕ, 0 < N → ∀ a₃ a₂ a₁ a₀ : Frequency,
        ρ ≤ ‖integerIntervalMean N (fun t => circleCharacter (cubicCirclePolynomial a₃ a₂ a₁ a₀ t))‖ →
        ∃ q : ℕ, 0 < q ∧ q ≤ Q ∧ ‖q • a₃‖ ≤ E / (N : ℝ) ^ 3 := by
  obtain ⟨Q, E, N₀, hQ, hE, _, hlarge⟩ := uniform_cubic_weyl_large ρ hρ
  refine ⟨Q, max E ((N₀ : ℝ) ^ 3), hQ, hE.trans_le (le_max_left _ _), ?_⟩
  intro N hN a₃ a₂ a₁ a₀ hmean
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  by_cases hNN : N₀ ≤ N
  · obtain ⟨q, hq, hqQ, hb⟩ := hlarge N hNN a₃ a₂ a₁ a₀ hmean
    exact ⟨q, hq, hqQ, hb.trans (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity))⟩
  · have hNle : (N : ℝ) ≤ N₀ := by exact_mod_cast (le_of_lt (lt_of_not_ge hNN))
    have hNcube : (N : ℝ) ^ 3 ≤ (N₀ : ℝ) ^ 3 := pow_le_pow_left₀ hNR.le hNle 3
    have hhalf : ‖a₃‖ ≤ (1 : ℝ) / 2 := by
      simpa using AddCircle.norm_le_half_period (1 : ℝ) (x := a₃) one_ne_zero
    refine ⟨1, by omega, hQ, ?_⟩
    rw [one_nsmul]
    calc
      ‖a₃‖ ≤ 1 := by linarith
      _ ≤ max E ((N₀ : ℝ) ^ 3) / (N : ℝ) ^ 3 := by
        apply (le_div_iff₀ (by positivity : 0 < (N : ℝ) ^ 3)).2
        simpa only [one_mul] using hNcube.trans (le_max_right E _)

end GMZP0
