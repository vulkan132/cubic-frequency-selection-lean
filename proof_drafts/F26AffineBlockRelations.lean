import GMZP0.CubicIntervalWeyl
import GMZP0.AffineBlockPhase
import GMZP0.PowerAffineReturns

/-! Actual large affine-profile blocks force quantitative slope relations in both directions. -/
noncomputable section
namespace GMZP0

/-- One actual large block forces the root-independent directional slope relation at scale N^(-4). -/
theorem uniform_affine_block_direction (v : ℝ) (hv : 0 < v) :
    ∃ Q : ℕ, ∃ E : ℝ, ∃ N₀ : ℕ, 0 < Q ∧ 0 < E ∧ 0 < N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ a b : Fin N → Frequency, ∀ m : Base N → ℂ,
      (∀ z, ‖m z‖ ≤ 1) → ∀ x x' : Fin N, x ≠ x' →
      (¬ KernelEnergyBound (blockGramKernel
        (outputMaskedKernel (responseKernel N (affineOriginalProfile a b)) m) x x') (v / N)) →
      ∃ n : ℕ, 0 < n ∧ n ≤ Q ∧
        ‖n • (horizontalGap x x' • (a x + 3 • a x'))‖ ≤ E / (N : ℝ) ^ 4 := by
  obtain ⟨D, E, hD, hE, hw⟩ := uniform_cubic_lag_common_denominator (v ^ 2 / 8) (by positivity)
  obtain ⟨Q, E₁, N₁, hQ, hE₁, hN₁, hr⟩ :=
    uniform_affine_power_returns (v ^ 2 / 4) E (by positivity) hE
  let N₀ := max N₁ (Nat.ceil (2 / v ^ 2) + 1)
  have hN₀ : 0 < N₀ := hN₁.trans_le (le_max_left _ _)
  refine ⟨2 * D * Q, E₁, N₀, by positivity, hE₁, hN₀, ?_⟩
  intro N hNN a b m hm x x' hx hlarge
  have hN : 0 < N := hN₀.trans_le hNN
  have hnR : (0 : ℝ) < N := by exact_mod_cast hN
  have hNN₁ : N₁ ≤ N := (le_max_left _ _).trans hNN
  have hscale : 2 ≤ (N : ℝ) * v ^ 2 := by
    have hc : Nat.ceil (2 / v ^ 2) ≤ N := by dsimp [N₀] at hNN; omega
    have hn : 2 / v ^ 2 ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hc)
    exact (div_le_iff₀ (sq_pos_of_pos hv)).1 hn
  obtain ⟨K, root, hcard, hK⟩ := masked_large_block_many_lags hN (affineVerticalProfile a b)
    (affineOriginalProfile a b) (affine_profile_agreement a b) m hm x x' hx v hv hscale hlarge
  have hs : K ⊆ Finset.Icc (-(N : ℤ)) N := by
    intro k hk
    have hh := abs_lt.mp (hK k hk).2.1
    exact Finset.mem_Icc.mpr ⟨hh.1.le, hh.2.le⟩
  have hd : (v ^ 2 / 4) * (N : ℝ) ≤ K.card := by
    convert hcard using 1
    ring
  have hret : ∀ k ∈ K,
      ‖k • (D • ((-2 * horizontalGap x x') • (a x + 3 • a x'))) + 0‖ ≤ E / (N : ℝ) ^ 3 := by
    intro k hk
    have hsum : v ^ 2 / 8 ≤
        ‖wideLagSum (affineVerticalProfile a b) x x' (label (root k)) k / (N : ℂ)‖ := by
      rw [norm_div, Complex.norm_natCast, le_div_iff₀ hnR]
      exact (hK k hk).2.2
    rw [affine_wideLagSum] at hsum
    have hb := hw N hN (horizontalGap x x') k _ _ _ _ hsum
    have he : k • (D • ((-2 * horizontalGap x x') • (a x + 3 • a x'))) + 0 =
        D • affineBlockCubic (a x) (a x') (horizontalGap x x') k := by
      simp only [affineBlockCubic]
      module
    rw [he]
    exact hb
  obtain ⟨q, hq, hqQ, hb⟩ := hr 3 (by norm_num) N hNN₁
    (D • ((-2 * horizontalGap x x') • (a x + 3 • a x'))) 0 K hs hd hret
  have he : q • (D • ((-2 * horizontalGap x x') • (a x + 3 • a x'))) =
      -((2 * D * q) • (horizontalGap x x' • (a x + 3 • a x'))) := by module
  exact ⟨2 * D * q, by positivity, Nat.mul_le_mul_left (2 * D) hqQ,
    by simpa only [he, norm_neg] using hb⟩

/-- Quantitative elimination retains all multipliers and bounds the exact factor-eight combination. -/
theorem affine_two_direction_norm_bound (a c : Frequency) (h : ℤ) (n₁ n₂ Q : ℕ)
    (hn₁ : n₁ ≤ Q) (hn₂ : n₂ ≤ Q) (ε : ℝ) (hε : 0 ≤ ε)
    (h₁ : ‖n₁ • (h • (a + 3 • c))‖ ≤ ε)
    (h₂ : ‖n₂ • (h • (3 • a + c))‖ ≤ ε) :
    ‖(8 * n₁ * n₂) • (h • a)‖ ≤ 4 * (Q : ℝ) * ε := by
  rw [← affine_two_direction_elimination a c h n₁ n₂]
  calc
    _ ≤ ‖(3 * n₁) • (n₂ • (h • (3 • a + c)))‖ + ‖n₂ • (n₁ • (h • (a + 3 • c)))‖ :=
      norm_sub_le _ _
    _ ≤ (3 * n₁ : ℕ) * ‖n₂ • (h • (3 • a + c))‖ + (n₂ : ℝ) * ‖n₁ • (h • (a + 3 • c))‖ :=
      add_le_add norm_nsmul_le norm_nsmul_le
    _ ≤ (3 * n₁ : ℕ) * ε + (n₂ : ℝ) * ε := add_le_add
      (mul_le_mul_of_nonneg_left h₂ (Nat.cast_nonneg _))
      (mul_le_mul_of_nonneg_left h₁ (Nat.cast_nonneg _))
    _ = ((3 * n₁ : ℕ) + (n₂ : ℝ)) * ε := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast (show 3 * n₁ + n₂ ≤ 4 * Q by omega)) hε

/-- Both actual directions give a bounded positive multiple of the current original row's slope. -/
theorem uniform_affine_block_row_relation (v : ℝ) (hv : 0 < v) :
    ∃ Q : ℕ, ∃ E : ℝ, ∃ N₀ : ℕ, 0 < Q ∧ 0 < E ∧ 0 < N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ a b : Fin N → Frequency, ∀ m : Base N → ℂ,
      (∀ z, ‖m z‖ ≤ 1) → ∀ x x' : Fin N, x ≠ x' →
      (¬ KernelEnergyBound (blockGramKernel
        (outputMaskedKernel (responseKernel N (affineOriginalProfile a b)) m) x x') (v / N)) →
      ∃ n : ℕ, 0 < n ∧ n ≤ Q ∧ ‖n • (horizontalGap x x' • a x)‖ ≤ E / (N : ℝ) ^ 4 := by
  obtain ⟨Q, E, N₀, hQ, hE, hN₀, hd⟩ := uniform_affine_block_direction v hv
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  refine ⟨8 * Q * Q, 4 * (Q : ℝ) * E, N₀, by positivity, by positivity, hN₀, ?_⟩
  intro N hN a b m hm x x' hx hlarge
  obtain ⟨n₁, hn₁, hn₁Q, hb₁⟩ := hd N hN a b m hm x x' hx hlarge
  have hlarge' : ¬ KernelEnergyBound (blockGramKernel
      (outputMaskedKernel (responseKernel N (affineOriginalProfile a b)) m) x' x) (v / N) := by
    intro hh
    exact hlarge ((blockGramKernel_energy_bound_symm _ (v / N) x x').2 hh)
  obtain ⟨n₂, hn₂, hn₂Q, hb₂⟩ := hd N hN a b m hm x' x hx.symm hlarge'
  have hg : horizontalGap x' x = -horizontalGap x x' := by simp only [horizontalGap]; ring
  rw [hg, neg_zsmul, smul_neg, norm_neg] at hb₂
  have hb₂' : ‖n₂ • (horizontalGap x x' • (3 • a x + a x'))‖ ≤ E / (N : ℝ) ^ 4 := by
    simpa only [add_comm] using hb₂
  have hb := affine_two_direction_norm_bound (a x) (a x') (horizontalGap x x') n₁ n₂ Q
    hn₁Q hn₂Q (E / (N : ℝ) ^ 4) (by positivity) hb₁ hb₂'
  refine ⟨8 * n₁ * n₂, by positivity, Nat.mul_le_mul (Nat.mul_le_mul_left 8 hn₁Q) hn₂Q, ?_⟩
  convert hb using 1
  ring

end GMZP0
