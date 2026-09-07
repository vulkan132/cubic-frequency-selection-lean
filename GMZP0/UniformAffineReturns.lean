import GMZP0.AffineReturnAmplification

/-! Uniform quantitative affine recurrence: all constants precede the scale and data. -/

noncomputable section
namespace GMZP0

theorem dense_returns_seed_card {N Q : ℕ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hQ : 8 ≤ (Q : ℝ) * ρ) (hN : 4 ≤ (N : ℝ) * ρ)
    (s : Finset ℤ) (hs : (N : ℝ) * ρ ≤ (s.card : ℝ)) :
    2 * N / Q + 1 < s.card := by
  have hd : ((2 * N / Q : ℕ) : ℝ) * (Q : ℝ) ≤ 2 * (N : ℝ) := by
    exact_mod_cast Nat.div_mul_le_self (2 * N) Q
  have h1 := mul_le_mul_of_nonneg_right hd hρ
  have h2 := mul_le_mul_of_nonneg_left hQ (Nat.cast_nonneg (2 * N / Q) : (0 : ℝ) ≤ (2 * N / Q : ℕ))
  have hr : ((2 * N / Q : ℕ) : ℝ) + 1 < (s.card : ℝ) := by nlinarith
  exact_mod_cast hr

/-- For errors with epsilon*N bounded, density improves the error by a factor N.
The denominator bound, error factor and scale threshold precede every input. -/
theorem uniform_affine_dense_returns (ρ C : ℝ) (hρ : 0 < ρ) (hC : 0 ≤ C) :
    ∃ Q : ℕ, ∃ E : ℝ, ∃ N₀ : ℕ, 0 < Q ∧ 0 < E ∧ 0 < N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ a b : Frequency, ∀ ε : ℝ, ∀ s : Finset ℤ,
        0 ≤ ε → ε * (N : ℝ) ≤ C → s ⊆ Finset.Icc (-(N : ℤ)) N →
        ρ * (N : ℝ) ≤ (s.card : ℝ) → (∀ h ∈ s, ‖h • a + b‖ ≤ ε) →
        ∃ q : ℕ, 0 < q ∧ q ≤ Q ∧ ‖q • a‖ ≤ E * ε / (N : ℝ) := by
  let Q : ℕ := Nat.ceil (8 / ρ)
  let K : ℕ := Nat.ceil (2 * C + 1)
  let B : ℕ := 2 * K + 1
  let E : ℝ := 4 * (B : ℝ) * (Q : ℝ) / ρ
  let N₀ : ℕ := Nat.ceil (4 * (B : ℝ) / ρ) + 1
  have hQ0 : 0 < Q := by
    have hh : (0 : ℝ) < Q := (div_pos (by norm_num) hρ).trans_le (Nat.le_ceil (8 / ρ))
    exact_mod_cast hh
  have hK0 : 0 < K := by
    have hh : (0 : ℝ) < K := (by linarith : 0 < 2 * C + 1).trans_le (Nat.le_ceil (2 * C + 1))
    exact_mod_cast hh
  have hB0 : 0 < B := by dsimp [B]; omega
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ0
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB0
  have hE0 : 0 < E := by dsimp [E]; positivity
  have hN₀ : 0 < N₀ := by dsimp [N₀]; omega
  refine ⟨Q, E, N₀, hQ0, hE0, hN₀, ?_⟩
  intro N hNN a b ε s hε hscale hs hdensity hreturn
  have hN0 : 0 < N := lt_of_lt_of_le hN₀ hNN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN0
  have hlarge : 4 * (B : ℝ) ≤ (N : ℝ) * ρ := by
    have hceil : Nat.ceil (4 * (B : ℝ) / ρ) ≤ N := by dsimp [N₀] at hNN; omega
    have hh : 4 * (B : ℝ) / ρ ≤ (N : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hceil)
    exact (div_le_iff₀ hρ).mp hh
  have hQbudget : 8 ≤ (Q : ℝ) * ρ := (div_le_iff₀ hρ).mp (Nat.le_ceil (8 / ρ))
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB0
  have hseed := dense_returns_seed_card (N := N) (Q := Q) hρ.le hQbudget (by nlinarith [hlarge]) s
    (by simpa only [mul_comm] using hdensity)
  have hsize : 2 * (2 * K + 1) ≤ s.card := by
    have hr : 2 * (B : ℝ) ≤ (s.card : ℝ) := by nlinarith
    have hn : 2 * B ≤ s.card := by exact_mod_cast hr
    exact hn
  have hK : 2 * C + 1 ≤ (K : ℝ) := Nat.le_ceil _
  obtain ⟨q, hq0, hqQ, hqbound⟩ :=
    affine_return_amplification hQ0 s hs hseed hsize a b hε hscale hK hreturn
  have hqn : (q.toNat : ℤ) = q := by omega
  have hqeq : q.toNat • a = q • a := by rw [← natCast_zsmul, hqn]
  refine ⟨q.toNat, by omega, by omega, ?_⟩
  rw [hqeq]
  have hmass := mul_le_mul_of_nonneg_left hdensity (norm_nonneg (q • a))
  have hb : ‖q • a‖ * (N : ℝ) ≤ 4 * (B : ℝ) * (Q : ℝ) * ε / ρ := by
    apply (le_div_iff₀ hρ).2
    have hBcast : (B : ℝ) = 2 * (K : ℝ) + 1 := by simp [B]
    rw [hBcast]
    nlinarith
  apply (le_div_iff₀ hNR).2
  calc
    ‖q • a‖ * (N : ℝ) ≤ 4 * (B : ℝ) * (Q : ℝ) * ε / ρ := hb
    _ = E * ε := by dsimp [E]; ring

end GMZP0
