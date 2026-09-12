import GMZP0.GlobalCubeCollision
import GMZP0.GlobalCubeThreshold

/-! Unweighted, distinct seven-cubes on high-weight vertices, with positive
horizontal fibre density. No structural theorem is assumed or applied here. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

theorem global_seven_threshold_collision_removal {G : Type*} [AddCommGroup G]
    [Fintype G] (σ F : G → ℝ) (τ : ℝ) :
    globalThresholdCubeDensity 7 σ F τ - 8128 / (Fintype.card G : ℝ) ≤
      globalDistinctThresholdCubeDensity 7 σ F τ := by
  classical
  have hrow (Y : G) :
      realUniformMean (fun v : Fin 7 → G => if realCubeThresholdGood 7 σ F τ Y v then (1 : ℝ) else 0) ≤
        realUniformMean (fun v : Fin 7 → G =>
          if Function.Injective (additiveCubeVertex 7 Y v) ∧ realCubeThresholdGood 7 σ F τ Y v
          then (1 : ℝ) else 0) + 8128 / (Fintype.card G : ℝ) := by
    have hp (v : Fin 7 → G) :
        (if realCubeThresholdGood 7 σ F τ Y v then (1 : ℝ) else 0) ≤
          (if Function.Injective (additiveCubeVertex 7 Y v) ∧ realCubeThresholdGood 7 σ F τ Y v
            then (1 : ℝ) else 0) + (if ¬ Function.Injective (additiveCubeVertex 7 Y v) then 1 else 0) := by
      by_cases hi : Function.Injective (additiveCubeVertex 7 Y v)
      · simp only [hi, true_and, not_true_eq_false, if_false, add_zero, le_refl]
      · simp only [hi, false_and, if_false, not_false_eq_true, if_true, zero_add]
        split_ifs <;> norm_num
    have hr := realUniformMean_mono _ _ hp
    rw [realUniformMean_add] at hr
    have hc := global_seven_collision_probability Y
    unfold globalCubeCollisionProbability at hc
    linarith only [hr, hc]
  have hm := realUniformMean_mono _ _ hrow
  rw [realUniformMean_add, realUniformMean_const] at hm
  change globalThresholdCubeDensity 7 σ F τ ≤ globalDistinctThresholdCubeDensity 7 σ F τ + _ at hm
  linarith

theorem weighted_real_seven_to_distinct_threshold {G : Type*} [AddCommGroup G]
    [Fintype G] (σ F : G → ℝ) (hσ : ∀ y, 0 ≤ σ y ∧ σ y ≤ 1)
    (τ : ℝ) (hτ : 0 ≤ τ) :
    globalRealCubeMass 6 σ F - τ - 8128 / (Fintype.card G : ℝ) ≤
      globalDistinctThresholdCubeDensity 7 σ F τ := by
  linarith [global_threshold_density_lower 6 σ F hσ τ hτ,
    global_seven_threshold_collision_removal σ F τ]

def cyclicPreparedSevenMean (N q : ℕ) [NeZero q] (σ : Base N → ℝ)
    (F : Fin N → ZMod q → ℝ) (τ : ℝ) : ℝ :=
  realUniformMean (fun x : Fin N =>
    globalDistinctThresholdCubeDensity 7 (fun Y => cyclicField N q σ 0 x Y) (F x) τ)

theorem cyclic_prepared_seven_lower {N q : ℕ} [NeZero q] (hN : 0 < N)
    (σ : Base N → ℝ) (F : Fin N → ZMod q → ℝ) (hσ : ∀ z, 0 ≤ σ z ∧ σ z ≤ 1)
    (χ : ℝ) (hχ : 0 < χ) (hmass : χ ≤ cyclicGlobalRealSevenMass N q σ F)
    (hq : 8128 / (q : ℝ) ≤ χ / 4) :
    χ / 2 ≤ cyclicPreparedSevenMean N q σ F (χ / 512) := by
  let : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hrow (x : Fin N) :
      globalRealCubeMass 6 (fun Y => cyclicField N q σ 0 x Y) (F x) ≤
        globalDistinctThresholdCubeDensity 7 (fun Y => cyclicField N q σ 0 x Y) (F x) (χ / 512) +
          χ / 512 + 8128 / (q : ℝ) := by
    have he := weighted_real_seven_to_distinct_threshold
      (fun Y => cyclicField N q σ 0 x Y) (F x)
      (fun Y => cyclicField_property N q σ 0 (fun t : ℝ => 0 ≤ t ∧ t ≤ 1)
        hσ ⟨le_rfl, zero_le_one⟩ x Y) (χ / 512) (by positivity)
    rw [ZMod.card] at he
    linarith
  have hm := realUniformMean_mono _ _ hrow
  simp only [realUniformMean_add, realUniformMean_const] at hm
  change cyclicGlobalRealSevenMass N q σ F ≤ cyclicPreparedSevenMean N q σ F (χ / 512) + χ / 512 + _ at hm
  linarith

def preparedSevenFibers (N q : ℕ) [NeZero q] (σ : Base N → ℝ)
    (F : Fin N → ZMod q → ℝ) (χ : ℝ) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter (fun x =>
    χ / 4 ≤ globalDistinctThresholdCubeDensity 7 (fun Y => cyclicField N q σ 0 x Y) (F x) (χ / 512))

theorem preparedSevenFibers_card {N q : ℕ} [NeZero q] (hN : 0 < N)
    (σ : Base N → ℝ) (F : Fin N → ZMod q → ℝ) (χ : ℝ) (hχ : 0 < χ)
    (hmass : χ / 2 ≤ cyclicPreparedSevenMean N q σ F (χ / 512)) :
    χ / 4 * N ≤ (preparedSevenFibers N q σ F χ).card := by
  classical
  let : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  let T (x : Fin N) := globalDistinctThresholdCubeDensity 7
    (fun Y => cyclicField N q σ 0 x Y) (F x) (χ / 512)
  have he := weighted_condition_mass (fun _ : Fin N => (1 : ℝ)) T
    (fun x => χ / 4 ≤ T x) (by positivity : 0 < χ / 2)
    (fun _ => ⟨zero_le_one, le_rfl⟩)
    (fun x => (globalDistinctThresholdCubeDensity_bounds 7 _ _ _).2)
    (by simpa only [one_mul, T, cyclicPreparedSevenMean] using hmass) (fun _ hx => by linarith)
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hmean : realUniformMean (fun x : Fin N => if χ / 4 ≤ T x then (1 : ℝ) else 0) =
      (preparedSevenFibers N q σ F χ).card / (N : ℝ) := by
    simp only [realUniformMean, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one,
      Fintype.card_fin, preparedSevenFibers, T]
  change χ / 2 / 2 ≤ realUniformMean (fun x : Fin N => if χ / 4 ≤ T x then (1 : ℝ) else 0) at he
  rw [hmean] at he
  have ht := (le_div_iff₀ hn).mp he
  nlinarith

theorem preparedSevenFibers_cube_count {N q : ℕ} [NeZero q]
    (σ : Base N → ℝ) (F : Fin N → ZMod q → ℝ) (χ : ℝ)
    (x : Fin N) (hx : x ∈ preparedSevenFibers N q σ F χ) :
    χ / 4 * (q : ℝ) ^ 8 ≤ globalDistinctThresholdCubeCount 7
      (fun Y => cyclicField N q σ 0 x Y) (F x) (χ / 512) := by
  apply distinct_seven_cube_count_lower
  exact (Finset.mem_filter.mp hx).2

theorem uniform_seven_collision_threshold (χ : ℝ) (hχ : 0 < χ) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ q : ℕ, N ^ 2 < q →
      8128 / (q : ℝ) ≤ χ / 4 := by
  obtain ⟨B, hB⟩ := exists_nat_gt (32512 / χ)
  refine ⟨B + 1, by omega, ?_⟩
  intro N hN q hq
  have hN0 : 0 < N := by omega
  have hNN : N ≤ N ^ 2 := by nlinarith
  have hBq : (B : ℝ) ≤ q := by exact_mod_cast (show B ≤ q by omega)
  have hp := (div_lt_iff₀ hχ).mp (hB.trans_le hBq)
  have hqr : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  apply (div_le_iff₀ hqr).mpr
  nlinarith

end GMZP0
