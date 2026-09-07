import GMZP0.FiniteCharacterOrthogonality
import GMZP0.RealCubeGrid

/-! The complete j/1024 mesh detects real zero for bounded differences on the actual lift grid. -/

noncomputable section
namespace GMZP0

def meshFrequency (M : ℕ) (j : Fin (1024 * M)) : ℝ := (j.val : ℝ) / 1024

def frequencyMeshMean (M : ℕ) (t : ℝ) : ℂ :=
  complexUniformMean (fun j : Fin (1024 * M) => circleCharacter ((meshFrequency M j * t : ℝ) : Frequency))

theorem meshFrequency_mul_grid (M : ℕ) (j : Fin (1024 * M)) (k : ℤ) :
    meshFrequency M j * ((k : ℝ) / M) = (j.val : ℝ) * k / ((1024 * M : ℕ) : ℝ) := by
  simp only [meshFrequency, Nat.cast_mul, Nat.cast_ofNat]
  ring

theorem frequencyMeshMean_grid_integer {M : ℕ} (hM : 0 < M) (k : ℤ)
    (hk : |k| < 1024 * (M : ℤ)) :
    frequencyMeshMean M ((k : ℝ) / M) = if k = 0 then 1 else 0 := by
  have hB : 0 < 1024 * M := Nat.mul_pos (by decide) hM
  have hkB : |k| < ((1024 * M : ℕ) : ℤ) := by exact_mod_cast hk
  simpa only [frequencyMeshMean, meshFrequency_mul_grid] using rational_character_orthogonality hB k hkB

theorem frequencyMeshMean_real_zero {M : ℕ} (hM : 0 < M) (t : ℝ)
    (hgrid : ∃ k : ℤ, t = (k : ℝ) / M) (ht : |t| < 1024) :
    frequencyMeshMean M t = if t = 0 then 1 else 0 := by
  have hm : (0 : ℝ) < M := by exact_mod_cast hM
  obtain ⟨k, hk⟩ := hgrid
  have hb := mul_lt_mul_of_pos_right ht hm
  rw [hk, abs_div, abs_of_pos hm, div_mul_cancel₀ _ hm.ne'] at hb
  have hki : |k| < 1024 * (M : ℤ) := by exact_mod_cast hb
  rw [hk, frequencyMeshMean_grid_integer hM k hki]
  simp only [div_eq_zero_iff, hm.ne', or_false, Int.cast_eq_zero]

theorem frequencyMeshMean_realCube {d M : ℕ} (hd : d ≤ 7) (hM : 0 < M)
    (F : (Fin d → Bool) → ℝ) (hgrid : ∀ ω, ∃ k : ℤ, F ω = (k : ℝ) / M)
    (hF : ∀ ω, |F ω| ≤ 3) :
    frequencyMeshMean M (realSignedCubeSum d F) = if realSignedCubeSum d F = 0 then 1 else 0 :=
  frequencyMeshMean_real_zero hM _ (realSignedCubeSum_grid d M F hgrid)
    ((realSignedCubeSum_abs_le_384 hd F hF).trans_lt (by norm_num))

end GMZP0
