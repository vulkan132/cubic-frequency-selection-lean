import GMZP0.CubeRounding

/-! Grid integrality and size of real cube sums, with every vertex occurrence retained. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

def realSignedCubeSum (d : ℕ) (F : (Fin d → Bool) → ℝ) : ℝ :=
  ∑ ω, (cubeSign d ω : ℝ) * F ω

theorem realSignedCubeSum_grid (d M : ℕ) (F : (Fin d → Bool) → ℝ)
    (hF : ∀ ω, ∃ k : ℤ, F ω = (k : ℝ) / M) :
    ∃ k : ℤ, realSignedCubeSum d F = (k : ℝ) / M := by
  classical
  choose n hn using hF
  refine ⟨∑ ω, cubeSign d ω * n ω, ?_⟩
  simp only [realSignedCubeSum, hn, Int.cast_sum, Int.cast_mul, div_eq_mul_inv,
    ← mul_assoc, ← Finset.sum_mul]

theorem realSignedCubeSum_abs_le (d : ℕ) (F : (Fin d → Bool) → ℝ) (B : ℝ)
    (hF : ∀ ω, |F ω| ≤ B) : |realSignedCubeSum d F| ≤ (2 : ℝ) ^ d * B := by
  unfold realSignedCubeSum
  calc
    _ ≤ ∑ ω, |(cubeSign d ω : ℝ) * F ω| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ω : Fin d → Bool, B := by
      apply Finset.sum_le_sum
      intro ω _
      have hs : |(cubeSign d ω : ℝ)| = 1 := by exact_mod_cast cubeSign_abs d ω
      rw [abs_mul, hs, one_mul]
      exact hF ω
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, card_booleanVertices,
        nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]

theorem realSignedCubeSum_abs_le_384 {d : ℕ} (hd : d ≤ 7)
    (F : (Fin d → Bool) → ℝ) (hF : ∀ ω, |F ω| ≤ 3) :
    |realSignedCubeSum d F| ≤ 384 := by
  have hb := realSignedCubeSum_abs_le d F 3 hF
  have hp : (2 : ℝ) ^ d ≤ (2 : ℝ) ^ 7 := pow_le_pow_right₀ (by norm_num) hd
  norm_num at hp
  linarith

theorem realSignedCubeSum_grid_bound {d M : ℕ} (hd : d ≤ 7) (hM : 0 < M)
    (F : (Fin d → Bool) → ℝ) (hgrid : ∀ ω, ∃ k : ℤ, F ω = (k : ℝ) / M)
    (hF : ∀ ω, |F ω| ≤ 3) :
    ∃ k : ℤ, realSignedCubeSum d F = (k : ℝ) / M ∧
      |k| ≤ 384 * (M : ℤ) ∧ |k| < 1024 * (M : ℤ) := by
  have hm : (0 : ℝ) < M := by exact_mod_cast hM
  obtain ⟨k, hk⟩ := realSignedCubeSum_grid d M F hgrid
  have hb := mul_le_mul_of_nonneg_right (realSignedCubeSum_abs_le_384 hd F hF) hm.le
  rw [hk, abs_div, abs_of_pos hm, div_mul_cancel₀ _ hm.ne'] at hb
  have hki : |k| ≤ 384 * (M : ℤ) := by exact_mod_cast hb
  have hmi : (0 : ℤ) < M := by exact_mod_cast hM
  exact ⟨k, hk, hki, by omega⟩

end GMZP0
