import GMZP0.MajorArcGrid

/-! The explicit major-arc grid at its exact circle-error scale, retaining all root branches. -/
noncomputable section
namespace GMZP0

/-- Every major-arc point has an actual branch and bounded grid index with the sharp circle error. -/
theorem majorArc_grid_circle_approximation {N : ℕ} (hN : 0 < N) (Q : ℕ)
    (b : ℝ) (hb : 0 < b) (a : Frequency) (ha : MajorArc Q N a) :
    ∃ i ∈ gridIndices Q b, ‖a - gridValue N b i‖ ≤ b / (2 * (N : ℝ) ^ 3) := by
  obtain ⟨q, hq1, hqQ, hqa⟩ := ha
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq1
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hqa' : ‖q • a - ((0 : ℝ) : Frequency)‖ ≤ (Q : ℝ) / (N : ℝ) ^ 3 := by
    simpa using hqa
  obtain ⟨j, hj0, hjq, hj⟩ := circle_approx_root_decomposition q hq1 a 0
    ((Q : ℝ) / (N : ℝ) ^ 3) hqa'
  simp only [zero_add] at hj
  obtain ⟨t, ht, htnorm⟩ := exists_nearest_frequency_lift
    (a - (((j : ℝ) / (q : ℝ) : ℝ) : Frequency))
  have htbound : |t| ≤ ((Q : ℝ) / (N : ℝ) ^ 3) / (q : ℝ) := htnorm.le.trans hj
  obtain ⟨l, herr, hl⟩ := cubic_scale_grid_rounding hN b hb t
  have hlreal : |(l : ℝ)| ≤ (gridRadius Q b q : ℝ) := by
    have hsize : |t| * (N : ℝ) ^ 3 / b ≤ (Q : ℝ) / ((q : ℝ) * b) := by
      calc
        |t| * (N : ℝ) ^ 3 / b ≤
            (((Q : ℝ) / (N : ℝ) ^ 3) / (q : ℝ)) * (N : ℝ) ^ 3 / b := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right htbound (by positivity)) hb.le
        _ = _ := by field_simp
    have hceil := Nat.le_ceil ((Q : ℝ) / ((q : ℝ) * b))
    simp only [gridRadius, Nat.cast_add, Nat.cast_one]
    linarith
  have hlint : -(gridRadius Q b q : ℤ) ≤ l ∧ l ≤ (gridRadius Q b q : ℤ) := by
    obtain ⟨hlo, hhi⟩ := abs_le.mp hlreal
    constructor
    · exact_mod_cast hlo
    · exact_mod_cast hhi
  refine ⟨(q, j, l), grid_index_mem Q q b j l hq1 hqQ hj0 hjq hlint, ?_⟩
  have haeq : a = (((j : ℝ) / (q : ℝ) : ℝ) : Frequency) + (t : Frequency) := by
    simpa only [add_comm] using (sub_eq_iff_eq_add).mp ht.symm
  have hdiff : a - gridValue N b (q, j, l) =
      ((t - (l : ℝ) * b / (N : ℝ) ^ 3 : ℝ) : Frequency) := by
    change a - ((((j : ℝ) / (q : ℝ) + (l : ℝ) * b / (N : ℝ) ^ 3 : ℝ)) : Frequency) = _
    rw [haeq, ← AddCircle.coe_add, ← AddCircle.coe_sub]
    congr 1
    ring
  have hclose : ‖a - gridValue N b (q, j, l)‖ ≤ b / (2 * (N : ℝ) ^ 3) := by
    rw [hdiff]
    exact (QuotientAddGroup.norm_mk_le_norm.trans (by simpa only [Real.norm_eq_abs] using herr))
  exact hclose

/-- The explicit circle grid is fixed before the captured frequency and every original field. -/
theorem majorArc_universal_circle_list (Q : ℕ) (hQ : 0 < Q) (ε : ℝ) (hε : 0 < ε) :
    ∃ J : ℕ, 0 < J ∧ ∀ N : ℕ, 0 < N → ∃ β : Fin J → Frequency,
      ∀ a : Frequency, MajorArc Q N a → ∃ i : Fin J,
        ‖a - β i‖ ≤ ε / (2 * (N : ℝ) ^ 3) := by
  classical
  let I := gridIndices Q ε
  let e := I.equivFin
  refine ⟨I.card, Finset.card_pos.mpr (gridIndices_nonempty Q hQ ε), ?_⟩
  intro N hN
  refine ⟨fun i => gridValue N ε (e.symm i).val, ?_⟩
  intro a ha
  obtain ⟨i, hi, hclose⟩ := majorArc_grid_circle_approximation hN Q ε hε a ha
  exact ⟨e ⟨i, hi⟩, by simpa only [Equiv.symm_apply_apply] using hclose⟩

end GMZP0
