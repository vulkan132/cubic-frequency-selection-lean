import GMZP0.FrequencyMesh

/-! Exact frequency averaging of all original weight factors in a real cube. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

theorem weighted_real_cube_character (d : ℕ) (σ F : (Fin d → Bool) → ℝ) (α : ℝ) :
    (∏ ω, cubeConj d ω ((σ ω : ℂ) * circleCharacter ((α * F ω : ℝ) : Frequency))) =
      ((∏ ω, σ ω : ℝ) : ℂ) * circleCharacter ((α * realSignedCubeSum d F : ℝ) : Frequency) := by
  simp only [cubeConj_mul, cubeConj_ofReal, cubeConj_character, Finset.prod_mul_distrib,
    ← Complex.ofReal_prod, ← circleCharacter_sum]
  congr 2
  simp only [← AddCircle.coe_zsmul, zsmul_eq_mul]
  rw [← frequency_coe_sum]
  congr 1
  simp only [realSignedCubeSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  ring

theorem weighted_frequency_cube_exact {d M : ℕ} (hd : d ≤ 7) (hM : 0 < M)
    (σ F : (Fin d → Bool) → ℝ) (hgrid : ∀ ω, ∃ k : ℤ, F ω = (k : ℝ) / M)
    (hF : ∀ ω, |F ω| ≤ 3) :
    complexUniformMean (fun j : Fin (1024 * M) =>
      ∏ ω, cubeConj d ω ((σ ω : ℂ) * circleCharacter ((meshFrequency M j * F ω : ℝ) : Frequency))) =
        if realSignedCubeSum d F = 0 then ((∏ ω, σ ω : ℝ) : ℂ) else 0 := by
  simp only [weighted_real_cube_character]
  rw [complexUniformMean_const_mul]
  change ((∏ ω, σ ω : ℝ) : ℂ) * frequencyMeshMean M (realSignedCubeSum d F) = _
  rw [frequencyMeshMean_realCube hd hM F hgrid hF]
  split_ifs <;> simp

theorem weighted_frequency_cube_real {d M : ℕ} (hd : d ≤ 7) (hM : 0 < M)
    (σ F : (Fin d → Bool) → ℝ) (hgrid : ∀ ω, ∃ k : ℤ, F ω = (k : ℝ) / M)
    (hF : ∀ ω, |F ω| ≤ 3) :
    realUniformMean (fun j : Fin (1024 * M) =>
      (∏ ω, cubeConj d ω ((σ ω : ℂ) * circleCharacter ((meshFrequency M j * F ω : ℝ) : Frequency))).re) =
        if realSignedCubeSum d F = 0 then ∏ ω, σ ω else 0 := by
  rw [← complexUniformMean_re, weighted_frequency_cube_exact hd hM σ F hgrid hF]
  split_ifs <;> simp only [Complex.ofReal_re, Complex.zero_re]

end GMZP0
