import GMZP0.QuadraticWeyl
import GMZP0.IntervalRescaling

/-! Quadratic inverse estimates on the exact signed overlap intervals, still divided by N. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

theorem quadraticCirclePolynomial_translate (a₂ a₁ a₀ : Frequency) (d t : ℤ) :
    quadraticCirclePolynomial a₂ a₁ a₀ (d + t) =
      quadraticCirclePolynomial a₂ ((2 * d) • a₂ + a₁)
        (d ^ 2 • a₂ + d • a₁ + a₀) t := by
  have h2 : (d + t) ^ 2 = t ^ 2 + t * (2 * d) + d ^ 2 := by ring
  simp only [quadraticCirclePolynomial, h2, add_zsmul, mul_zsmul, smul_add]
  abel

theorem uniform_quadratic_interval_weyl (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ Q : ℕ, ∃ E : ℝ, 0 < Q ∧ 0 < E ∧
      ∀ N : ℕ, 0 < N → ∀ L U : ℤ, (U - L + 1).toNat ≤ N →
      ∀ a₂ a₁ a₀ : Frequency,
        ρ ≤ ‖(∑ t ∈ Finset.Icc L U, circleCharacter (quadraticCirclePolynomial a₂ a₁ a₀ t)) /
          (N : ℂ)‖ → ∃ q : ℕ, 0 < q ∧ q ≤ Q ∧ ‖q • a₂‖ ≤ E / (N : ℝ) ^ 2 := by
  obtain ⟨Q, E, hQ, hE, hw⟩ := uniform_quadratic_weyl ρ hρ
  refine ⟨Q, E / ρ ^ 2, hQ, by positivity, ?_⟩
  intro N hN L U hMN a₂ a₁ a₀ hlarge
  obtain ⟨hM, hlen, hmean⟩ := interval_large_rescaling hN L U
    (fun t => circleCharacter (quadraticCirclePolynomial a₂ a₁ a₀ t))
    (fun _ => (norm_circleCharacter _).le) hMN hρ hlarge
  simp only [quadraticCirclePolynomial_translate] at hmean
  obtain ⟨q, hq, hqQ, hb⟩ := hw (U - L + 1).toNat hM a₂
    ((2 * (L - 1)) • a₂ + a₁) ((L - 1) ^ 2 • a₂ + (L - 1) • a₁ + a₀) hmean
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hsq := pow_le_pow_left₀ (mul_pos hρ hNR).le hlen 2
  refine ⟨q, hq, hqQ, hb.trans ?_⟩
  calc
    E / ((U - L + 1).toNat : ℝ) ^ 2 ≤ E / (ρ * (N : ℝ)) ^ 2 :=
      div_le_div_of_nonneg_left hE.le (by positivity) hsq
    _ = (E / ρ ^ 2) / (N : ℝ) ^ 2 := by rw [mul_pow, div_mul_eq_div_div]

theorem weylOverlap_card_le (N : ℕ) (h : ℤ) : (weylOverlap N h).card ≤ N := by
  have hs : weylOverlap N h ⊆ Finset.Icc (1 : ℤ) N := by
    intro t ht
    simp only [weylOverlap, Finset.mem_Icc, max_le_iff, le_min_iff] at ht ⊢
    exact ⟨ht.1.1, ht.2.1⟩
  have hc := Finset.card_le_card hs
  simpa only [Int.card_Icc, add_sub_cancel_right, Int.toNat_natCast] using hc

end GMZP0
