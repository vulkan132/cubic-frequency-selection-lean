import GMZP0.FrequencyMesh

/-! Exact obstructions to replacing the mesh by integers or deleting the size condition. -/

noncomputable section
namespace GMZP0

theorem integer_frequency_alias_obstruction :
    (1 : ℝ) ≠ 0 ∧ ∀ j : ℤ, circleCharacter (((j : ℝ) * 1 : ℝ) : Frequency) = 1 := by
  refine ⟨by norm_num, ?_⟩
  intro j
  simp only [mul_one, integer_cast_frequency, circleCharacter, AddCircle.toCircle_zero, Circle.coe_one]

theorem frequencyMeshMean_period {M : ℕ} (hM : 0 < M) : frequencyMeshMean M 1024 = 1 := by
  let : Nonempty (Fin (1024 * M)) := ⟨⟨0, Nat.mul_pos (by decide) hM⟩⟩
  have he (j : Fin (1024 * M)) : circleCharacter ((meshFrequency M j * 1024 : ℝ) : Frequency) = 1 := by
    have hv : meshFrequency M j * 1024 = (j.val : ℝ) := by unfold meshFrequency; ring
    rw [hv]
    simpa only [Int.cast_natCast, mul_one] using (integer_frequency_alias_obstruction.2 (j.val : ℤ))
  simp only [frequencyMeshMean, he, complexUniformMean_const]

theorem frequency_mesh_size_obstruction {M : ℕ} (hM : 0 < M) :
    (∃ k : ℤ, (1024 : ℝ) = (k : ℝ) / M) ∧ (1024 : ℝ) ≠ 0 ∧ frequencyMeshMean M 1024 = 1 := by
  have hm : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  refine ⟨⟨1024 * (M : ℤ), ?_⟩, by norm_num, frequencyMeshMean_period hM⟩
  push_cast
  field_simp

end GMZP0
