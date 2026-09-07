import GMZP0.LiftChoices

/-! Uniform scale bounds for the single lift grid M=floor(N^3/E). -/

noncomputable section
namespace GMZP0

def liftGridSize (N : ℕ) (E : ℝ) : ℕ := ⌊(N : ℝ) ^ 3 / E⌋₊

theorem liftGridSize_bounds {N : ℕ} (hN : 0 < N) (E : ℝ) (hE : 0 < E)
    (hlarge : 10 * E ≤ (N : ℝ) ^ 3) :
    9 ≤ liftGridSize N E ∧ (liftGridSize N E : ℝ) * (E / (N : ℝ) ^ 3) ≤ 1 ∧
      19 / (2 * (liftGridSize N E : ℝ)) ≤ 19 * E / (N : ℝ) ^ 3 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hx : 10 ≤ (N : ℝ) ^ 3 / E := (le_div_iff₀ hE).mpr hlarge
  have hm10 : 10 ≤ liftGridSize N E := Nat.le_floor hx
  have hm : (0 : ℝ) < liftGridSize N E := by exact_mod_cast (show 0 < liftGridSize N E by omega)
  have hf := Nat.floor_le (show 0 ≤ (N : ℝ) ^ 3 / E by positivity)
  have hupper : (liftGridSize N E : ℝ) * E ≤ (N : ℝ) ^ 3 := (le_div_iff₀ hE).mp hf
  have hlower := Nat.lt_floor_add_one ((N : ℝ) ^ 3 / E)
  have hlow : (N : ℝ) ^ 3 ≤ 2 * (liftGridSize N E : ℝ) * E := by
    have hh := (div_lt_iff₀ hE).mp hlower
    change (N : ℝ) ^ 3 < ((liftGridSize N E : ℝ) + 1) * E at hh
    have hm1 : (1 : ℝ) ≤ liftGridSize N E := by exact_mod_cast (show 1 ≤ liftGridSize N E by omega)
    have hh' := mul_le_mul_of_nonneg_right hm1 hE.le
    nlinarith
  refine ⟨by omega, ?_, ?_⟩
  · rw [← mul_div_assoc]
    exact (div_le_iff₀ (pow_pos hn 3)).mpr (by simpa using hupper)
  · apply (div_le_div_iff₀ (show 0 < 2 * (liftGridSize N E : ℝ) by positivity) (pow_pos hn 3)).mpr
    nlinarith

theorem uniform_lift_grid_scale (E : ℝ) (hE : 0 < E) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      9 ≤ liftGridSize N E ∧ (liftGridSize N E : ℝ) * (E / (N : ℝ) ^ 3) ≤ 1 ∧
        19 / (2 * (liftGridSize N E : ℝ)) ≤ 19 * E / (N : ℝ) ^ 3 := by
  let N₀ : ℕ := Nat.ceil (10 * E) + 1
  have hN₀ : 0 < N₀ := by dsimp [N₀]; omega
  refine ⟨N₀, hN₀, ?_⟩
  intro N hNN
  have hN : 0 < N := hN₀.trans_le hNN
  apply liftGridSize_bounds hN E hE
  have hc : Nat.ceil (10 * E) ≤ N := by dsimp [N₀] at hNN; omega
  have he : 10 * E ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hc)
  have hp : N ≤ N ^ 3 := le_self_pow (by omega) (by decide)
  exact he.trans (by exact_mod_cast hp)

end GMZP0
