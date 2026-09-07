import GMZP0.CyclicBounds

/-! Translation of a bounded sequence over a whole integer interval.
The interval may be empty and the translation may have either sign. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

theorem norm_sum_bounded (s : Finset ℤ) (f : ℤ → ℂ) (hf : ∀ k, ‖f k‖ ≤ 1) :
    ‖∑ k ∈ s, f k‖ ≤ (s.card : ℝ) := by
  calc
    ‖∑ k ∈ s, f k‖ ≤ ∑ k ∈ s, ‖f k‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ s, (1 : ℝ) := Finset.sum_le_sum fun k _ => hf k
    _ = (s.card : ℝ) := by simp

theorem norm_sum_sub_sum_le_sdiff (s t : Finset ℤ) (f : ℤ → ℂ)
    (hf : ∀ k, ‖f k‖ ≤ 1) :
    ‖(∑ k ∈ s, f k) - ∑ k ∈ t, f k‖ ≤
      ((s \ t).card : ℝ) + ((t \ s).card : ℝ) := by
  rw [← Finset.sum_sdiff_sub_sum_sdiff (s₁ := t) (s₂ := s)]
  exact (norm_sub_le _ _).trans
    (add_le_add (norm_sum_bounded _ f hf) (norm_sum_bounded _ f hf))

theorem sum_Icc_translate (a b d : ℤ) (f : ℤ → ℂ) :
    (∑ k ∈ Finset.Icc a b, f (k + d)) =
      ∑ k ∈ Finset.Icc (a + d) (b + d), f k := by
  refine Finset.sum_bij (fun k _ => k + d) ?_ ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_Icc] at hk ⊢
    omega
  · intro k hk l hl he
    omega
  · intro k hk
    refine ⟨k - d, ?_, by omega⟩
    simp only [Finset.mem_Icc] at hk ⊢
    omega
  · intro k _
    rfl

theorem norm_Icc_translate_nonneg (a b d : ℤ) (hd : 0 ≤ d)
    (f : ℤ → ℂ) (hf : ∀ k, ‖f k‖ ≤ 1) :
    ‖(∑ k ∈ Finset.Icc a b, f (k + d)) - ∑ k ∈ Finset.Icc a b, f k‖ ≤
      2 * (d : ℝ) := by
  have hleft : Finset.Icc a b \ Finset.Icc (a + d) (b + d) ⊆
      Finset.Icc a (a + d - 1) := by
    intro k hk
    simp only [Finset.mem_sdiff, Finset.mem_Icc] at hk ⊢
    omega
  have hright : Finset.Icc (a + d) (b + d) \ Finset.Icc a b ⊆
      Finset.Icc (b + 1) (b + d) := by
    intro k hk
    simp only [Finset.mem_sdiff, Finset.mem_Icc] at hk ⊢
    omega
  have hcl : ((Finset.Icc a (a + d - 1)).card : ℝ) = (d : ℝ) := by
    rw [Int.card_Icc]
    have he : a + d - 1 + 1 - a = d := by omega
    rw [he]
    exact_mod_cast Int.toNat_of_nonneg hd
  have hcr : ((Finset.Icc (b + 1) (b + d)).card : ℝ) = (d : ℝ) := by
    rw [Int.card_Icc]
    have he : b + d + 1 - (b + 1) = d := by omega
    rw [he]
    exact_mod_cast Int.toNat_of_nonneg hd
  rw [sum_Icc_translate]
  calc
    ‖(∑ k ∈ Finset.Icc (a + d) (b + d), f k) - ∑ k ∈ Finset.Icc a b, f k‖ ≤
        ((Finset.Icc (a + d) (b + d) \ Finset.Icc a b).card : ℝ) +
        ((Finset.Icc a b \ Finset.Icc (a + d) (b + d)).card : ℝ) :=
      norm_sum_sub_sum_le_sdiff _ _ f hf
    _ ≤ ((Finset.Icc (b + 1) (b + d)).card : ℝ) +
        ((Finset.Icc a (a + d - 1)).card : ℝ) := by
      exact_mod_cast add_le_add (Finset.card_le_card hright) (Finset.card_le_card hleft)
    _ = 2 * (d : ℝ) := by rw [hcl, hcr]; ring

theorem norm_Icc_translate (a b d : ℤ) (f : ℤ → ℂ) (hf : ∀ k, ‖f k‖ ≤ 1) :
    ‖(∑ k ∈ Finset.Icc a b, f (k + d)) - ∑ k ∈ Finset.Icc a b, f k‖ ≤
      2 * |(d : ℝ)| := by
  by_cases hd : 0 ≤ d
  · simpa only [abs_of_nonneg (show (0 : ℝ) ≤ d by exact_mod_cast hd)] using
      norm_Icc_translate_nonneg a b d hd f hf
  · have hdn : 0 ≤ -d := by omega
    have hb := norm_Icc_translate_nonneg a b (-d) hdn (fun k => f (k + d))
      (fun k => hf (k + d))
    simp only [neg_add_cancel_right, Int.cast_neg] at hb
    rw [norm_sub_rev] at hb
    simpa only [abs_of_nonpos (show (d : ℝ) ≤ 0 by exact_mod_cast (show d ≤ 0 by omega))]
      using hb

theorem lagInnerInterval_eq_Icc (N : ℕ) (h t : ℤ) :
    lagInnerInterval N h t =
      Finset.Icc (max (t - N) (t + h - N)) (min (t - 1) (t + h - 1)) := by
  ext k
  simp only [lagInnerInterval, Finset.mem_inter, Finset.mem_Icc, max_le_iff, le_min_iff]
  tauto

theorem norm_lag_sum_translate {N : ℕ} (hN : 0 < N) (h t d : ℤ)
    (f : ℤ → ℂ) (hf : ∀ k, ‖f k‖ ≤ 1) :
    ‖(∑ k ∈ lagInnerInterval N h t, f (k + d)) / (N : ℂ) -
      (∑ k ∈ lagInnerInterval N h t, f k) / (N : ℂ)‖ ≤ 2 * |(d : ℝ)| / N := by
  rw [← sub_div, norm_div, Complex.norm_natCast, lagInnerInterval_eq_Icc]
  exact div_le_div_of_nonneg_right (norm_Icc_translate _ _ d f hf) (by positivity)

end GMZP0
