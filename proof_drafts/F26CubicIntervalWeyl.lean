import GMZP0.CubicCommonDenominator
import GMZP0.IntervalRescaling
import GMZP0.WideLagBounds

/-! Cubic leading-coefficient estimates on actual shorter intervals, with the original N denominator. -/
noncomputable section
open scoped BigOperators
namespace GMZP0

/-- Integer translation preserves the cubic coefficient exactly on the circle. -/
theorem cubicCirclePolynomial_translate (a₃ a₂ a₁ a₀ : Frequency) (d t : ℤ) :
    cubicCirclePolynomial a₃ a₂ a₁ a₀ (d + t) =
      cubicCirclePolynomial a₃ ((3 * d) • a₃ + a₂)
        ((3 * d ^ 2) • a₃ + (2 * d) • a₂ + a₁)
        (d ^ 3 • a₃ + d ^ 2 • a₂ + d • a₁ + a₀) t := by
  have h3 : (d + t) ^ 3 = t ^ 3 + t ^ 2 * (3 * d) + t * (3 * d ^ 2) + d ^ 3 := by ring
  have h2 : (d + t) ^ 2 = t ^ 2 + t * (2 * d) + d ^ 2 := by ring
  simp only [cubicCirclePolynomial, h3, h2, add_zsmul, mul_zsmul, smul_add]
  abel

/-- A single denominator works for every actual integer interval and every cubic coefficient tuple. -/
theorem uniform_cubic_interval_common_denominator (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ D : ℕ, ∃ E : ℝ, 0 < D ∧ 0 < E ∧
      ∀ N : ℕ, 0 < N → ∀ L U : ℤ, (U - L + 1).toNat ≤ N →
      ∀ a₃ a₂ a₁ a₀ : Frequency,
        ρ ≤ ‖(∑ t ∈ Finset.Icc L U, circleCharacter (cubicCirclePolynomial a₃ a₂ a₁ a₀ t)) /
          (N : ℂ)‖ → ‖D • a₃‖ ≤ E / (N : ℝ) ^ 3 := by
  obtain ⟨D, E, hD, hE, hw⟩ := uniform_cubic_common_denominator ρ hρ
  refine ⟨D, E / ρ ^ 3, hD, by positivity, ?_⟩
  intro N hN L U hMN a₃ a₂ a₁ a₀ hlarge
  obtain ⟨hM, hlen, hmean⟩ := interval_large_rescaling hN L U
    (fun t => circleCharacter (cubicCirclePolynomial a₃ a₂ a₁ a₀ t))
    (fun _ => (norm_circleCharacter _).le) hMN hρ hlarge
  simp only [cubicCirclePolynomial_translate] at hmean
  have hb := hw (U - L + 1).toNat hM a₃ ((3 * (L - 1)) • a₃ + a₂)
    ((3 * (L - 1) ^ 2) • a₃ + (2 * (L - 1)) • a₂ + a₁)
    ((L - 1) ^ 3 • a₃ + (L - 1) ^ 2 • a₂ + (L - 1) • a₁ + a₀) hmean
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hpow := pow_le_pow_left₀ (mul_pos hρ hNR).le hlen 3
  calc
    ‖D • a₃‖ ≤ E / ((U - L + 1).toNat : ℝ) ^ 3 := hb
    _ ≤ E / (ρ * (N : ℝ)) ^ 3 := div_le_div_of_nonneg_left hE.le (by positivity) hpow
    _ = (E / ρ ^ 3) / (N : ℝ) ^ 3 := by rw [mul_pow, div_mul_eq_div_div]

/-- Every complete lag-label set is one exact integer interval, including empty cases. -/
theorem lagLabels_eq_interval (N : ℕ) (h k : ℤ) :
    lagLabels N h k = Finset.Icc (max (max 1 (1 + h)) (max (1 - k) (1 + h - k)))
      (min (min (N : ℤ) (N + h)) (min (N - k) (N + h - k))) := by
  ext r
  simp only [mem_lagLabels_iff, Finset.mem_Icc, max_le_iff, le_min_iff]
  omega

/-- The actual lag interval has at most N labels. -/
theorem lagLabels_interval_length_le (N : ℕ) (h k : ℤ) :
    ((min (min (N : ℤ) (N + h)) (min (N - k) (N + h - k))) -
      (max (max 1 (1 + h)) (max (1 - k) (1 + h - k))) + 1).toNat ≤ N := by
  rw [← interval_length_card, ← lagLabels_eq_interval]
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (blockLabels_card_le N h)

/-- A common denominator captures the cubic coefficient on any exact lag interval. -/
theorem uniform_cubic_lag_common_denominator (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ D : ℕ, ∃ E : ℝ, 0 < D ∧ 0 < E ∧
      ∀ N : ℕ, 0 < N → ∀ h k : ℤ, ∀ a₃ a₂ a₁ a₀ : Frequency,
        ρ ≤ ‖(∑ r ∈ lagLabels N h k, circleCharacter (cubicCirclePolynomial a₃ a₂ a₁ a₀ r)) /
          (N : ℂ)‖ → ‖D • a₃‖ ≤ E / (N : ℝ) ^ 3 := by
  obtain ⟨D, E, hD, hE, hw⟩ := uniform_cubic_interval_common_denominator ρ hρ
  refine ⟨D, E, hD, hE, ?_⟩
  intro N hN h k a₃ a₂ a₁ a₀ hlarge
  rw [lagLabels_eq_interval] at hlarge
  exact hw N hN _ _ (lagLabels_interval_length_le N h k) a₃ a₂ a₁ a₀ hlarge

end GMZP0
