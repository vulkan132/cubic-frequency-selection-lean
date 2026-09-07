import GMZP0.WeylDifferencing

/-! Linear inverse estimates on every actual overlap interval, normalized by the original N. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

/-- This covers empty intervals as well as arbitrary signed endpoints. -/
theorem sum_Icc_as_fin (L U : ℤ) (F : ℤ → ℂ) :
    (∑ k ∈ Finset.Icc L U, F k) =
      ∑ r : Fin ((U - L + 1).toNat), F (L - 1 + (label r : ℤ)) := by
  rw [sum_fin_labels ((U - L + 1).toNat) (fun r => F (L - 1 + r))]
  by_cases hLU : L ≤ U
  · have hm : ((U - L + 1).toNat : ℤ) = U - L + 1 := by omega
    have hh := sum_Icc_translate 1 ((U - L + 1).toNat : ℤ) (L - 1) F
    have h1 : (1 : ℤ) + (L - 1) = L := by omega
    have h2 : ((U - L + 1).toNat : ℤ) + (L - 1) = U := by omega
    rw [h1, h2] at hh
    simpa only [add_comm] using hh.symm
  · have hm : (U - L + 1).toNat = 0 := by omega
    have he : Finset.Icc L U = ∅ := Finset.Icc_eq_empty_of_lt (lt_of_not_ge hLU)
    simp [he, hm]

theorem linear_phase_sum_geometric (N : ℕ) (a b : Frequency) :
    (∑ r : Fin N, circleCharacter (label r • a + b)) =
      circleCharacter (a + b) * ∑ r ∈ Finset.range N, circleCharacter a ^ r := by
  simp only [label, succ_nsmul, circleCharacter_add, circleCharacter_nsmul]
  rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_range]
  ring

theorem linear_phase_sum_chord_bound (N : ℕ) (a b : Frequency) :
    ‖∑ r : Fin N, circleCharacter (label r • a + b)‖ * ‖circleCharacter a - 1‖ ≤ 2 := by
  rw [linear_phase_sum_geometric, norm_mul, norm_circleCharacter, one_mul,
    ← norm_mul, geom_sum_mul]
  calc
    ‖circleCharacter a ^ N - 1‖ ≤ ‖circleCharacter a ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by norm_num [norm_pow, norm_circleCharacter]

theorem linear_interval_sum_chord_bound (L U : ℤ) (a b : Frequency) :
    ‖∑ t ∈ Finset.Icc L U, circleCharacter (t • a + b)‖ *
      ‖circleCharacter a - 1‖ ≤ 2 := by
  rw [sum_Icc_as_fin]
  have he (r : Fin ((U - L + 1).toNat)) :
      (L - 1 + (label r : ℤ)) • a + b = label r • a + ((L - 1) • a + b) := by
    rw [add_zsmul, natCast_zsmul]
    abel
  simp only [he]
  exact linear_phase_sum_chord_bound _ a _

/-- The denominator is the original N, even when the interval has fewer than N labels. -/
theorem linear_interval_weyl_inverse {N : ℕ} (hN : 0 < N) (L U : ℤ) (a b : Frequency)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hlarge : ρ ≤ ‖(∑ t ∈ Finset.Icc L U, circleCharacter (t • a + b)) / (N : ℂ)‖) :
    ‖a‖ ≤ 1 / (2 * ρ * (N : ℝ)) := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  rw [norm_div, Complex.norm_natCast, le_div_iff₀ hNreal] at hlarge
  have hchord := circle_norm_le_chord a
  have hbound := linear_interval_sum_chord_bound L U a b
  have h1 := mul_le_mul_of_nonneg_left hchord
    (norm_nonneg (∑ t ∈ Finset.Icc L U, circleCharacter (t • a + b)))
  have h2 := mul_le_mul_of_nonneg_right hlarge (norm_nonneg a)
  apply (le_div_iff₀ (by positivity : 0 < 2 * ρ * (N : ℝ))).2
  nlinarith

end GMZP0
