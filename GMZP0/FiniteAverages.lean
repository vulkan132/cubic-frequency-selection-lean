import GMZP0.IntervalTranslation

/-! Exact finite means and perturbation bounds used in lag smoothing. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

def complexUniformMean {I : Type*} [Fintype I] (F : I → ℂ) : ℂ :=
  (∑ i, F i) / (Fintype.card I : ℂ)

def realUniformMean {I : Type*} [Fintype I] (F : I → ℝ) : ℝ :=
  (∑ i, F i) / (Fintype.card I : ℝ)

theorem complexUniformMean_const {I : Type*} [Fintype I] [Nonempty I] (c : ℂ) :
    complexUniformMean (fun _ : I => c) = c := by
  have hn : (Fintype.card I : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [complexUniformMean, hn]

theorem complexUniformMean_sub {I : Type*} [Fintype I] (F G : I → ℂ) :
    complexUniformMean (fun i => F i - G i) = complexUniformMean F - complexUniformMean G := by
  simp only [complexUniformMean, Finset.sum_sub_distrib, sub_div]

theorem norm_complexUniformMean_le {I : Type*} [Fintype I] [Nonempty I]
    (F : I → ℂ) (C : ℝ) (hF : ∀ i, ‖F i‖ ≤ C) :
    ‖complexUniformMean F‖ ≤ C := by
  have hn : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  rw [complexUniformMean, norm_div, Complex.norm_natCast, div_le_iff₀ hn]
  calc
    ‖∑ i, F i‖ ≤ ∑ i, ‖F i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : I, C := Finset.sum_le_sum fun i _ => hF i
    _ = C * (Fintype.card I : ℝ) := by simp [mul_comm]

theorem norm_complexUniformMean_sub_le {I : Type*} [Fintype I] [Nonempty I]
    (F : I → ℂ) (c : ℂ) (ε : ℝ) (hF : ∀ i, ‖F i - c‖ ≤ ε) :
    ‖complexUniformMean F - c‖ ≤ ε := by
  rw [← complexUniformMean_const (I := I) c, ← complexUniformMean_sub]
  exact norm_complexUniformMean_le _ ε (by simpa only [complexUniformMean_const] using hF)

theorem complexUniformMean_sum_div {I J : Type*} [Fintype I]
    (s : Finset J) (F : I → J → ℂ) (d : ℂ) :
    complexUniformMean (fun i => (∑ j ∈ s, F i j) / d) =
      (∑ j ∈ s, complexUniformMean (fun i => F i j)) / d := by
  simp only [complexUniformMean, div_eq_mul_inv, ← Finset.sum_mul]
  rw [Finset.sum_comm]
  ring

theorem weighted_norm_mean_stability {I : Type*} [Fintype I] [Nonempty I]
    (W : I → ℝ) (F G : I → ℂ) (ε : ℝ) (hε : 0 ≤ ε)
    (hW : ∀ i, 0 ≤ W i ∧ W i ≤ 1) (hFG : ∀ i, ‖G i - F i‖ ≤ ε) :
    realUniformMean (fun i => W i * ‖F i‖) - ε ≤
      realUniformMean (fun i => W i * ‖G i‖) := by
  have hn : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  have hi (i : I) : W i * ‖F i‖ ≤ W i * ‖G i‖ + ε := by
    have hb : ‖F i‖ ≤ ‖G i‖ + ε := by
      calc
        ‖F i‖ = ‖G i - (G i - F i)‖ := by congr 1; abel
        _ ≤ ‖G i‖ + ‖G i - F i‖ := norm_sub_le _ _
        _ ≤ ‖G i‖ + ε := add_le_add le_rfl (hFG i)
    calc
      W i * ‖F i‖ ≤ W i * (‖G i‖ + ε) := mul_le_mul_of_nonneg_left hb (hW i).1
      _ = W i * ‖G i‖ + W i * ε := by ring
      _ ≤ W i * ‖G i‖ + ε := by
        apply add_le_add le_rfl
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (hW i).2 hε
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hi i)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
  have hd := (div_le_div_of_nonneg_right hs hn.le)
  rw [add_div, mul_div_cancel_left₀ _ (ne_of_gt hn)] at hd
  exact sub_le_iff_le_add.mpr hd

end GMZP0
