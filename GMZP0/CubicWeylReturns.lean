import GMZP0.QuadraticIntervalWeyl
import GMZP0.DenominatorFiber

/-! Cubic differencing and one dense fiber of actual bounded quadratic denominators. -/

noncomputable section
namespace GMZP0

theorem uniform_cubic_dense_returns (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ Q : ℕ, ∃ E : ℝ, 0 < Q ∧ 0 < E ∧
      ∀ N : ℕ, 0 < N → 2 ≤ (N : ℝ) * ρ ^ 2 → ∀ a₃ a₂ a₁ a₀ : Frequency,
        ρ ≤ ‖integerIntervalMean N (fun t => circleCharacter (cubicCirclePolynomial a₃ a₂ a₁ a₀ t))‖ →
        ∃ q : ℕ, 0 < q ∧ q ≤ Q ∧ ∃ s : Finset ℤ, s ⊆ horizontalShiftLabels N ∧
          (ρ ^ 2 / (4 * (Q : ℝ))) * (N : ℝ) ≤ (s.card : ℝ) ∧
          ∀ h ∈ s, ‖h • ((3 * (q : ℤ)) • a₃)‖ ≤ E / (N : ℝ) ^ 2 := by
  obtain ⟨Q, E, hQ, hE, hw⟩ := uniform_quadratic_interval_weyl (ρ ^ 2 / 8) (by positivity)
  refine ⟨Q, E, hQ, hE, ?_⟩
  intro N hN hscale a₃ a₂ a₁ a₀ hlarge
  let F := fun t => circleCharacter (cubicCirclePolynomial a₃ a₂ a₁ a₀ t)
  let S := largeWeylShifts N F (ρ ^ 2 / 8)
  have hcard : (N : ℝ) * ρ ^ 2 / 4 ≤ (S.card : ℝ) :=
    many_large_weyl_correlations hN F (fun t => (norm_circleCharacter _).le) hρ.le hlarge hscale
  have hreturns : ∀ h ∈ S, ∃ q : ℕ, 0 < q ∧ q ≤ Q ∧
      ‖q • ((3 * h) • a₃)‖ ≤ E / (N : ℝ) ^ 2 := by
    intro h hh
    have hcor := (largeWeylShifts_mem hh).2.2.2
    dsimp [F] at hcor
    rw [cubic_weyl_correlation] at hcor
    have hlen : ((min (N : ℤ) (N - h)) - max 1 (1 - h) + 1).toNat ≤ N := by
      have hc := weylOverlap_card_le N h
      rwa [weylOverlap, interval_length_card] at hc
    exact hw N hN (max 1 (1 - h)) (min (N : ℤ) (N - h)) hlen
      ((3 * h) • a₃) ((3 * h ^ 2) • a₃ + (2 * h) • a₂)
      (h ^ 3 • a₃ + h ^ 2 • a₂ + h • a₁) hcor
  obtain ⟨q, hq, hqQ, s, hsS, hscard, hsq⟩ :=
    finite_positive_denominator_fiber hQ S
      (fun h q => ‖q • ((3 * h) • a₃)‖ ≤ E / (N : ℝ) ^ 2) hreturns
  refine ⟨q, hq, hqQ, s, hsS.trans (Finset.filter_subset _ _), ?_, ?_⟩
  · have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
    have hd := div_le_div_of_nonneg_right hcard hQR.le
    have he : (N : ℝ) * ρ ^ 2 / 4 / (Q : ℝ) = (ρ ^ 2 / (4 * (Q : ℝ))) * (N : ℝ) := by ring
    rw [he] at hd
    exact hd.trans hscard
  · intro h hh
    have he : h • ((3 * (q : ℤ)) • a₃) = q • ((3 * h) • a₃) := by
      have hcast : q • ((3 * h) • a₃) = (q : ℤ) • ((3 * h) • a₃) := by rw [natCast_zsmul]
      rw [hcast, ← mul_zsmul, ← mul_zsmul]
      congr 1
      ring
    rw [he]
    exact hsq h hh

end GMZP0
