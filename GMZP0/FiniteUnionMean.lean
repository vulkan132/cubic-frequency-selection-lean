import GMZP0.CoordinateMean

/-! The union bound in normalized finite averages. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

theorem realUniformMean_sum {A I : Type*} [Fintype A] [Fintype I] (F : A → I → ℝ) :
    realUniformMean (fun a => ∑ i, F a i) = ∑ i, realUniformMean (fun a => F a i) := by
  unfold realUniformMean
  rw [Finset.sum_comm]
  simp only [div_eq_mul_inv, Finset.sum_mul]

theorem uniform_event_union_le {A I : Type*} [Fintype A] [Fintype I]
    (P : A → Prop) [DecidablePred P] (Q : A → I → Prop) [∀ a, DecidablePred (Q a)]
    (hcover : ∀ a, P a → ∃ i, Q a i) :
    realUniformMean (fun a => if P a then 1 else 0) ≤
      ∑ i, realUniformMean (fun a => if Q a i then 1 else 0) := by
  rw [← realUniformMean_sum]
  apply realUniformMean_mono
  intro a
  by_cases ha : P a
  · obtain ⟨i, hi⟩ := hcover a ha
    rw [if_pos ha]
    have hsum := Finset.single_le_sum
      (fun j (_ : j ∈ (Finset.univ : Finset I)) => show (0 : ℝ) ≤ if Q a j then 1 else 0 by
        split_ifs <;> norm_num)
      (Finset.mem_univ i)
    simpa only [if_pos hi] using hsum
  · rw [if_neg ha]
    exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)

end GMZP0
