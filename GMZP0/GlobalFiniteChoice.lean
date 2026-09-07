import GMZP0.IndependentAssignments

/-! One global choice realizes the weighted expectation; different events may share coordinates. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

theorem exists_ge_realUniformMean {I : Type*} [Fintype I] [Nonempty I] (F : I → ℝ) :
    ∃ i, realUniformMean F ≤ F i := by
  classical
  have hc : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hs : (∑ _i : I, realUniformMean F) ≤ ∑ i : I, F i := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, realUniformMean]
    field_simp
    exact le_rfl
  obtain ⟨i, _, hi⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hs
  exact ⟨i, hi⟩

theorem mean_constant_event_weight {I : Type*} [Fintype I] (P : I → Prop) [DecidablePred P]
    (w : ℝ) :
    realUniformMean (fun i => if P i then w else 0) =
      w * realUniformMean (fun i => if P i then 1 else 0) := by
  simpa only [mul_ite, mul_one, mul_zero] using
    realUniformMean_const_mul (fun i => if P i then 1 else 0) w

theorem exists_global_weighted_success {I C : Type*} [Fintype I] [Fintype C] [Nonempty C]
    (W : I → ℝ) (hW : ∀ i, 0 ≤ W i) (P : I → Prop) [DecidablePred P]
    (Q : I → C → Prop) [∀ i, DecidablePred (Q i)] (ν : ℝ)
    (hprob : ∀ i, P i → ν ≤ realUniformMean (fun c => if Q i c then 1 else 0)) :
    ∃ c : C, ν * realUniformMean (fun i => if P i then W i else 0) ≤
      realUniformMean (fun i => if Q i c then W i else 0) := by
  have hpoint (i : I) : ν * (if P i then W i else 0) ≤
      realUniformMean (fun c => if Q i c then W i else 0) := by
    by_cases hi : P i
    · rw [if_pos hi, mean_constant_event_weight]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hprob i hi) (hW i)
    · rw [if_neg hi, mul_zero]
      apply realUniformMean_nonneg
      intro c
      split_ifs <;> simp only [hW i, le_refl]
  have hm := realUniformMean_mono
    (fun i => ν * (if P i then W i else 0))
    (fun i => realUniformMean (fun c => if Q i c then W i else 0)) hpoint
  rw [realUniformMean_const_mul, realUniformMean_comm] at hm
  obtain ⟨c, hc⟩ := exists_ge_realUniformMean
    (fun c : C => realUniformMean (fun i => if Q i c then W i else 0))
  exact ⟨c, hm.trans hc⟩

end GMZP0
