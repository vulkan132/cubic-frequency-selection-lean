import GMZP0.PhaseScale

/-! Every root of multiplication on R/Z, with the integer branch retained. -/

noncomputable section
namespace GMZP0

@[simp] theorem integer_cast_frequency (k : ℤ) : ((k : ℝ) : Frequency) = 0 := by
  apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).2
  exact ⟨k, by simp⟩

/-- Exact counterexample to dividing a circle error while keeping only the zero branch. -/
theorem zero_branch_division_counterexample :
    (2 : ℕ) • ((1 / 2 : ℝ) : Frequency) = 0 ∧
      ‖((1 / 2 : ℝ) : Frequency)‖ = (1 / 2 : ℝ) := by
  constructor
  · rw [← AddCircle.coe_nsmul]
    norm_num [nsmul_eq_mul, AddCircle.coe_period]
  · rw [UnitAddCircle.norm_eq]
    norm_num [round_eq]

/-- Any solution of q a = u mod 1 has one of all q integer root branches. -/
theorem circle_root_decomposition (q : ℕ) (hq : 0 < q) (a : Frequency) (u : ℝ)
    (hroot : q • a = (u : Frequency)) :
    ∃ j : ℤ, 0 ≤ j ∧ j < (q : ℤ) ∧ a = (((u + j) / (q : ℝ) : ℝ) : Frequency) := by
  induction a using QuotientAddGroup.induction_on
  rename_i x
  have hzero : (((q : ℝ) * x - u : ℝ) : Frequency) = 0 := by
    rw [AddCircle.coe_sub, ← nsmul_eq_mul, AddCircle.coe_nsmul, hroot, sub_self]
  obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hzero
  simp only [zsmul_eq_mul, mul_one] at hk
  have hqz : (0 : ℤ) < q := by exact_mod_cast hq
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  refine ⟨k % (q : ℤ), Int.emod_nonneg _ hqz.ne', Int.emod_lt_of_pos _ hqz, ?_⟩
  have hdivision : ((k % (q : ℤ) : ℤ) : ℝ) +
      (q : ℝ) * ((k / (q : ℤ) : ℤ) : ℝ) = (k : ℝ) := by
    exact_mod_cast Int.emod_add_mul_ediv k (q : ℤ)
  have hx : x = (u + ((k % (q : ℤ) : ℤ) : ℝ)) / (q : ℝ) +
      ((k / (q : ℤ) : ℤ) : ℝ) := by
    field_simp [hqr.ne']
    nlinarith
  rw [hx, AddCircle.coe_add, integer_cast_frequency, add_zero]

/-- A real error divides by q only after retaining the actual integer root branch. -/
theorem circle_root_with_real_error (q : ℕ) (hq : 0 < q) (a : Frequency) (u t : ℝ)
    (hroot : q • a = ((u + t : ℝ) : Frequency)) :
    ∃ j : ℤ, 0 ≤ j ∧ j < (q : ℤ) ∧
      a = (((u + j) / (q : ℝ) : ℝ) : Frequency) + ((t / (q : ℝ) : ℝ) : Frequency) := by
  obtain ⟨j, hj0, hjq, hj⟩ := circle_root_decomposition q hq a (u + t) hroot
  refine ⟨j, hj0, hjq, ?_⟩
  rw [hj, ← AddCircle.coe_add]
  congr 1
  ring

/-- Approximate division on the circle retains all q branches before obtaining a norm bound. -/
theorem circle_approx_root_decomposition (q : ℕ) (hq : 0 < q) (a : Frequency) (u E : ℝ)
    (herror : ‖q • a - (u : Frequency)‖ ≤ E) :
    ∃ j : ℤ, 0 ≤ j ∧ j < (q : ℤ) ∧
      ‖a - (((u + j) / (q : ℝ) : ℝ) : Frequency)‖ ≤ E / (q : ℝ) := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  obtain ⟨t, ht, hnorm⟩ := exists_nearest_frequency_lift (q • a - (u : Frequency))
  have hroot : q • a = ((u + t : ℝ) : Frequency) := by
    rw [AddCircle.coe_add]
    simpa only [add_comm] using (sub_eq_iff_eq_add).mp ht.symm
  obtain ⟨j, hj0, hjq, hj⟩ := circle_root_with_real_error q hq a u t hroot
  refine ⟨j, hj0, hjq, ?_⟩
  rw [hj, add_sub_cancel_left]
  calc
    ‖((t / (q : ℝ) : ℝ) : Frequency)‖ ≤ ‖t / (q : ℝ)‖ :=
      QuotientAddGroup.norm_mk_le_norm
    _ = |t| / (q : ℝ) := by rw [Real.norm_eq_abs, abs_div, abs_of_pos hqr]
    _ ≤ E / (q : ℝ) := div_le_div_of_nonneg_right (hnorm.le.trans herror) hqr.le

/-- The same retained root controls the complete cubic-label metric. -/
theorem circle_approx_root_fullLabel {N : ℕ} (hN : 0 < N) (q : ℕ) (hq : 0 < q)
    (a : Frequency) (u E : ℝ) (herror : ‖q • a - (u : Frequency)‖ ≤ E) :
    ∃ j : ℤ, 0 ≤ j ∧ j < (q : ℤ) ∧
      cubicDistance N a (((u + j) / (q : ℝ) : ℝ) : Frequency) ≤
        2 * Real.pi * (N : ℝ) ^ 3 * (E / (q : ℝ)) := by
  obtain ⟨j, hj0, hjq, hj⟩ := circle_approx_root_decomposition q hq a u E herror
  refine ⟨j, hj0, hjq, ?_⟩
  exact (cubicDistance_le_circle_scale hN a _).trans
    (mul_le_mul_of_nonneg_left hj (by positivity))

end GMZP0
