import GMZP0.CubeRounding

/-! An allowed correction makes the real cube sum zero while retaining the actual integer branch. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

theorem cube_choice_sum_eq (M : ℕ) (a : (Fin 4 → Bool) → Frequency)
    (c : (Fin 4 → Bool) → LiftChoice) :
    (∑ ω, (cubeSign 4 ω : ℝ) * liftChoiceValue M (a ω) (c ω)) =
      ((cubeRoundedSum M a : ℝ) + ∑ ω, (cubeSign 4 ω : ℝ) * ((c ω).1.val : ℝ)) / M +
        ∑ ω, (cubeSign 4 ω : ℝ) * ((c ω).2.val : ℝ) := by
  simp only [liftChoiceValue, cubeRoundedSum, Int.cast_sum, Int.cast_mul, div_eq_mul_inv,
    mul_add, add_mul, ← mul_assoc, Finset.sum_add_distrib, Finset.sum_mul]

theorem exists_cube_integer_correction (l r : ℤ) (hl : |l| ≤ 8) (hr : |r| ≤ 9) :
    ∃ c : (Fin 4 → Bool) → LiftChoice,
      (∑ ω, cubeSign 4 ω * (c ω).1.val) = -r ∧
      (∑ ω, cubeSign 4 ω * (c ω).2.val) = -l := by
  classical
  let ω₀ : Fin 4 → Bool := fun _ => false
  have hω₀ : cubeSign 4 ω₀ = 1 := by decide
  have hcard : l.natAbs ≤ positiveCubeVertices.card := by
    rw [card_positiveCubeVertices]
    exact_mod_cast (show (l.natAbs : ℤ) ≤ 8 by simpa only [Int.natCast_natAbs] using hl)
  obtain ⟨T, hT, hTcard⟩ := Finset.exists_subset_card_eq hcard
  let v₀ : ℤ := if 0 ≤ l then -1 else 1
  have hv₀ : -1 ≤ v₀ ∧ v₀ ≤ 1 := by dsimp [v₀]; split_ifs <;> omega
  have hvl : (l.natAbs : ℤ) * v₀ = -l := by
    rw [Int.natCast_natAbs]
    dsimp [v₀]
    split_ifs with h
    · rw [abs_of_nonneg h]; ring
    · rw [abs_of_neg (lt_of_not_ge h)]; ring
  let U : (Fin 4 → Bool) → smoothingShiftLabels 9 := fun ω =>
    ⟨if ω = ω₀ then -r else 0, by
      simp only [smoothingShiftLabels, Finset.mem_Icc]
      have hb := abs_le.mp hr
      split_ifs <;> omega⟩
  let V : (Fin 4 → Bool) → smoothingShiftLabels 1 := fun ω =>
    ⟨if ω ∈ T then v₀ else 0, by
      simp only [smoothingShiftLabels, Finset.mem_Icc]
      split_ifs <;> omega⟩
  refine ⟨fun ω => (U ω, V ω), ?_, ?_⟩
  · change (∑ ω, cubeSign 4 ω * (if ω = ω₀ then -r else 0)) = -r
    rw [Finset.sum_eq_single ω₀]
    · simp only [ite_true, hω₀, one_mul]
    · intro ω _ hne
      simp only [if_neg hne, mul_zero]
    · simp
  · have he (ω : Fin 4 → Bool) : cubeSign 4 ω * (V ω).val = if ω ∈ T then v₀ else 0 := by
      by_cases hω : ω ∈ T
      · have hs : cubeSign 4 ω = 1 := (Finset.mem_filter.mp (hT hω)).2
        simp only [V, if_pos hω, hs, one_mul]
      · simp only [V, if_neg hω, mul_zero]
    simp only [he]
    rw [← Finset.sum_filter]
    simpa [Finset.filter_mem_eq_inter, hTcard, nsmul_eq_mul] using hvl

theorem exists_cube_lift_zero {M : ℕ} (hM : 0 < M)
    (a : (Fin 4 → Bool) → Frequency) (ε : ℝ) (hscale : (M : ℝ) * ε ≤ 1)
    (hnear : ‖∑ ω, cubeSign 4 ω • a ω‖ ≤ ε) :
    ∃ c : (Fin 4 → Bool) → LiftChoice,
      (∑ ω, (cubeSign 4 ω : ℝ) * liftChoiceValue M (a ω) (c ω)) = 0 := by
  obtain ⟨l, r, hS, hl, hr⟩ := cube_rounding_branch hM a ε hscale hnear
  obtain ⟨c, hU, hV⟩ := exists_cube_integer_correction l r hl hr
  refine ⟨c, ?_⟩
  have hUr : (∑ ω, (cubeSign 4 ω : ℝ) * ((c ω).1.val : ℝ)) = -(r : ℝ) := by exact_mod_cast hU
  have hVr : (∑ ω, (cubeSign 4 ω : ℝ) * ((c ω).2.val : ℝ)) = -(l : ℝ) := by exact_mod_cast hV
  have hSr : (cubeRoundedSum M a : ℝ) = (l : ℝ) * M + r := by exact_mod_cast hS
  have hm : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  rw [cube_choice_sum_eq, hUr, hVr, hSr]
  field_simp
  ring

end GMZP0
