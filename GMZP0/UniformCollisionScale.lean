import GMZP0.WeightedCollisionRemoval

/-! The collision budget and short modular intervals hold beyond one data-independent scale. -/

noncomputable section
namespace GMZP0

theorem uniform_collision_scale (a γ : ℝ) (ha : 0 < a) (hγ : 0 < γ) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ q : ℕ, N ^ 2 < q →
      2 * N < q ∧ 2 * smoothingRadius N a < q ∧
        120 / (2 * (smoothingRadius N a : ℝ) + 1) ≤ γ := by
  let N₀ : ℕ := max (Nat.ceil a + 2) (Nat.ceil (64 * (120 / γ + 1) / a) + 1)
  have hN₀ : 0 < N₀ := by dsimp [N₀]; omega
  refine ⟨N₀, hN₀, ?_⟩
  intro N hNN q hq
  have hNa : Nat.ceil a + 2 ≤ N := (le_max_left _ _).trans hNN
  have hNb : Nat.ceil (64 * (120 / γ + 1) / a) + 1 ≤ N := (le_max_right _ _).trans hNN
  have hN2 : 2 ≤ N := by omega
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have haN : a < (N : ℝ) := by
    have hc : (Nat.ceil a : ℝ) + 2 ≤ (N : ℝ) := by exact_mod_cast hNa
    linarith [Nat.le_ceil a]
  have hfloor : (smoothingRadius N a : ℝ) ≤ a * (N : ℝ) / 64 :=
    Nat.floor_le (by positivity)
  have hℓq : 2 * smoothingRadius N a < q := by
    have hp := mul_lt_mul_of_pos_right haN hN
    have hl : 2 * (smoothingRadius N a : ℝ) < (N : ℝ) ^ 2 := by
      nlinarith [show (0 : ℝ) ≤ smoothingRadius N a from Nat.cast_nonneg _]
    exact (by exact_mod_cast hl : 2 * smoothingRadius N a < N ^ 2).trans hq
  have hstep : 2 * N < q := by
    have hs := Nat.mul_le_mul_right N hN2
    rw [← pow_two] at hs
    exact hs.trans_lt hq
  have hlarge : 120 / γ + 1 ≤ a * (N : ℝ) / 64 := by
    have hc : Nat.ceil (64 * (120 / γ + 1) / a) ≤ N := by omega
    have hd : 64 * (120 / γ + 1) / a ≤ (N : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hc)
    have hm := (div_le_iff₀ ha).mp hd
    nlinarith
  have hlow := Nat.lt_floor_add_one (a * (N : ℝ) / 64)
  have hbudget : 120 / γ < (smoothingRadius N a : ℝ) := by
    dsimp only [smoothingRadius]
    linarith
  have hb := (div_lt_iff₀ hγ).mp hbudget
  refine ⟨hstep, hℓq, ?_⟩
  apply (div_le_iff₀ (show 0 < 2 * (smoothingRadius N a : ℝ) + 1 by positivity)).2
  nlinarith

end GMZP0
