import GMZP0.CubeCollision

/-! An exact obstruction to dropping the nonzero modular-step hypothesis. -/

noncomputable section
namespace GMZP0

theorem cyclicCubeVertex_zero_step (q ℓ : ℕ) (h : ℤ) (hs : ((2 * h : ℤ) : ZMod q) = 0)
    (Y : ZMod q) (u : CubeShiftPairs ℓ) (ω : Fin 4 → Bool) :
    cyclicCubeVertex q ℓ h Y u ω = Y := by
  unfold cyclicCubeVertex
  rw [Int.cast_mul, hs, zero_mul, add_zero]

theorem cube_pair_collision_zero_step (q ℓ : ℕ) (h : ℤ)
    (hs : ((2 * h : ℤ) : ZMod q) = 0) (Y : ZMod q) (ω ω' : Fin 4 → Bool) :
    realUniformMean (fun u : CubeShiftPairs ℓ =>
      if cyclicCubeVertex q ℓ h Y u ω = cyclicCubeVertex q ℓ h Y u ω' then 1 else 0) = 1 := by
  simp only [cyclicCubeVertex_zero_step q ℓ h hs, ite_true, realUniformMean_const]

/-- The interval embeds in Z/7Z and h is a nonzero integer, but 2h is zero modulo 7. -/
theorem cube_pair_collision_zero_step_obstruction :
    Nat.Prime 7 ∧ 2 * 1 < 7 ∧ (7 : ℤ) ≠ 0 ∧
      (fun _ : Fin 4 => false) ≠ (fun _ : Fin 4 => true) ∧
      (1 : ℝ) / (2 * 1 + 1) <
        realUniformMean (fun u : CubeShiftPairs 1 =>
          if cyclicCubeVertex 7 1 7 0 u (fun _ => false) =
            cyclicCubeVertex 7 1 7 0 u (fun _ => true) then 1 else 0) := by
  refine ⟨by decide, by norm_num, by norm_num, ?_, ?_⟩
  · intro he
    have hf := congrFun he (0 : Fin 4)
    cases hf
  · rw [cube_pair_collision_zero_step 7 1 7 (by decide) 0]
    norm_num

end GMZP0
