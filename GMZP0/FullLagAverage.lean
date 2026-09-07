import GMZP0.CyclicBoxNorm

/-! Nonnegative interval sums and the exact cost of extending to all lags in [-N,N]. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

def fullLagLabels (N : ℕ) : Finset ℤ := Finset.Icc (-(N : ℤ)) N

instance fullLagLabels_nonempty (N : ℕ) : Nonempty (fullLagLabels N) :=
  ⟨⟨0, by simp [fullLagLabels]⟩⟩

theorem fullLagLabels_card (N : ℕ) : (fullLagLabels N).card = 2 * N + 1 := by
  rw [fullLagLabels, Int.card_Icc]
  omega

theorem lagInnerInterval_subset_full (N : ℕ) (h t : ℤ) (ht : 1 ≤ t ∧ t ≤ N) :
    lagInnerInterval N h t ⊆ fullLagLabels N := by
  intro k hk
  simp only [lagInnerInterval, Finset.mem_inter, Finset.mem_Icc] at hk
  simp only [fullLagLabels, Finset.mem_Icc]
  omega

theorem fullLag_sum_eq_card_mean (N : ℕ) (B : ℤ → ℝ) :
    (∑ k ∈ fullLagLabels N, B k) =
      (2 * (N : ℝ) + 1) * realUniformMean (fun k : fullLagLabels N => B k.val) := by
  rw [realUniformMean, Finset.sum_coe_sort (fullLagLabels N) B, Fintype.card_coe, fullLagLabels_card]
  push_cast
  have hc : (2 * (N : ℝ) + 1) ≠ 0 := by positivity
  field_simp

theorem weighted_lag_sum_le_three_mean {N : ℕ} (hN : 0 < N) (h t : ℤ)
    (ht : 1 ≤ t ∧ t ≤ N) (B : ℤ → ℝ) (hB : ∀ k, 0 ≤ B k)
    (W : ℝ) (hW : W ≤ 1) :
    W * ((∑ k ∈ lagInnerInterval N h t, B k) / N) ≤
      3 * realUniformMean (fun k : fullLagLabels N => B k.val) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hb : 0 ≤ (∑ k ∈ lagInnerInterval N h t, B k) / (N : ℝ) :=
    div_nonneg (Finset.sum_nonneg fun k _ => hB k) hn.le
  have hmean : 0 ≤ realUniformMean (fun k : fullLagLabels N => B k.val) :=
    realUniformMean_nonneg _ fun k => hB k.val
  have hratio : (2 * (N : ℝ) + 1) / N ≤ 3 := by
    rw [div_le_iff₀ hn]
    linarith only [hn1]
  calc
    W * ((∑ k ∈ lagInnerInterval N h t, B k) / N) ≤
        (∑ k ∈ lagInnerInterval N h t, B k) / N := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hW hb
    _ ≤ (∑ k ∈ fullLagLabels N, B k) / N := by
      apply div_le_div_of_nonneg_right _ hn.le
      exact Finset.sum_le_sum_of_subset_of_nonneg (lagInnerInterval_subset_full N h t ht)
        (fun k _ _ => hB k)
    _ = ((2 * (N : ℝ) + 1) / N) * realUniformMean (fun k : fullLagLabels N => B k.val) := by
      rw [fullLag_sum_eq_card_mean]
      ring
    _ ≤ 3 * realUniformMean (fun k : fullLagLabels N => B k.val) :=
      mul_le_mul_of_nonneg_right hratio hmean

end GMZP0
