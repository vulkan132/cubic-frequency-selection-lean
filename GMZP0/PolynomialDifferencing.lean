import GMZP0.IntervalWeyl
import GMZP0.WeylLargeCorrelations

/-! Exact circle-valued quadratic and cubic derivatives on the actual overlap intervals. -/

noncomputable section
open scoped BigOperators ComplexConjugate
namespace GMZP0

def quadraticCirclePolynomial (a₂ a₁ a₀ : Frequency) (t : ℤ) : Frequency :=
  t ^ 2 • a₂ + t • a₁ + a₀

def cubicCirclePolynomial (a₃ a₂ a₁ a₀ : Frequency) (t : ℤ) : Frequency :=
  t ^ 3 • a₃ + t ^ 2 • a₂ + t • a₁ + a₀

theorem quadraticCirclePolynomial_difference (a₂ a₁ a₀ : Frequency) (h t : ℤ) :
    quadraticCirclePolynomial a₂ a₁ a₀ (t + h) - quadraticCirclePolynomial a₂ a₁ a₀ t =
      t • ((2 * h) • a₂) + (h ^ 2 • a₂ + h • a₁) := by
  calc
    _ = ((t + h) ^ 2 - t ^ 2) • a₂ + ((t + h) - t) • a₁ := by
      simp only [quadraticCirclePolynomial, sub_zsmul]
      abel
    _ = (t * (2 * h) + h ^ 2) • a₂ + h • a₁ := by
      congr 2 <;> ring
    _ = _ := by rw [add_zsmul, mul_zsmul]; abel

theorem cubicCirclePolynomial_difference (a₃ a₂ a₁ a₀ : Frequency) (h t : ℤ) :
    cubicCirclePolynomial a₃ a₂ a₁ a₀ (t + h) - cubicCirclePolynomial a₃ a₂ a₁ a₀ t =
      quadraticCirclePolynomial ((3 * h) • a₃)
        ((3 * h ^ 2) • a₃ + (2 * h) • a₂) (h ^ 3 • a₃ + h ^ 2 • a₂ + h • a₁) t := by
  calc
    _ = ((t + h) ^ 3 - t ^ 3) • a₃ + ((t + h) ^ 2 - t ^ 2) • a₂ + h • a₁ := by
      simp only [cubicCirclePolynomial, sub_zsmul, add_zsmul]
      abel
    _ = (t ^ 2 * (3 * h) + t * (3 * h ^ 2) + h ^ 3) • a₃ +
        (t * (2 * h) + h ^ 2) • a₂ + h • a₁ := by
      congr 2 <;> congr 1 <;> ring
    _ = _ := by
      simp only [quadraticCirclePolynomial, add_zsmul, mul_zsmul, smul_add]
      abel

def weylOverlap (N : ℕ) (h : ℤ) : Finset ℤ :=
  Finset.Icc (max 1 (1 - h)) (min (N : ℤ) (N - h))

/-- Only labels for which both original times lie in [N] occur. -/
theorem weylCorrelation_phase_interval (N : ℕ) (P : ℤ → Frequency) (h : ℤ) :
    weylCorrelation N (fun t => circleCharacter (P t)) h =
      (∑ t ∈ weylOverlap N h, circleCharacter (P (t + h) - P t)) / (N : ℂ) := by
  have hs : ((Finset.Icc (1 : ℤ) N).filter
      (fun t => t + h ∈ Finset.Icc (1 : ℤ) N)) = weylOverlap N h := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_Icc, weylOverlap, max_le_iff, le_min_iff]
    omega
  rw [weylCorrelation, ← Finset.sum_filter, hs]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  exact (circleCharacter_sub _ _).symm

theorem quadratic_weyl_correlation (N : ℕ) (a₂ a₁ a₀ : Frequency) (h : ℤ) :
    weylCorrelation N (fun t => circleCharacter (quadraticCirclePolynomial a₂ a₁ a₀ t)) h =
      (∑ t ∈ weylOverlap N h,
        circleCharacter (t • ((2 * h) • a₂) + (h ^ 2 • a₂ + h • a₁))) / (N : ℂ) := by
  rw [weylCorrelation_phase_interval]
  simp only [quadraticCirclePolynomial_difference]

theorem cubic_weyl_correlation (N : ℕ) (a₃ a₂ a₁ a₀ : Frequency) (h : ℤ) :
    weylCorrelation N (fun t => circleCharacter (cubicCirclePolynomial a₃ a₂ a₁ a₀ t)) h =
      (∑ t ∈ weylOverlap N h,
        circleCharacter (quadraticCirclePolynomial ((3 * h) • a₃)
          ((3 * h ^ 2) • a₃ + (2 * h) • a₂) (h ^ 3 • a₃ + h ^ 2 • a₂ + h • a₁) t)) /
            (N : ℂ) := by
  rw [weylCorrelation_phase_interval]
  simp only [cubicCirclePolynomial_difference]

/-- A large actual quadratic correlation controls 2h*a₂ at scale N⁻¹. -/
theorem quadratic_large_shift_control {N : ℕ} (hN : 0 < N)
    (a₂ a₁ a₀ : Frequency) {ρ : ℝ} (hρ : 0 < ρ) {h : ℤ}
    (hh : h ∈ largeWeylShifts N
      (fun t => circleCharacter (quadraticCirclePolynomial a₂ a₁ a₀ t)) (ρ ^ 2 / 8)) :
    ‖(2 * h) • a₂‖ ≤ 4 / (ρ ^ 2 * (N : ℝ)) := by
  have hc := (largeWeylShifts_mem hh).2.2.2
  rw [quadratic_weyl_correlation] at hc
  have he := linear_interval_weyl_inverse hN (max 1 (1 - h)) (min (N : ℤ) (N - h))
    ((2 * h) • a₂) (h ^ 2 • a₂ + h • a₁) (by positivity : 0 < ρ ^ 2 / 8) hc
  convert he using 1; ring

/-- The actual quadratic sum produces a dense family of small leading multiples.
This is the input to recurrence amplification, not yet the quadratic inverse theorem. -/
theorem quadratic_many_returns {N : ℕ} (hN : 0 < N)
    (a₂ a₁ a₀ : Frequency) {ρ : ℝ} (hρ : 0 < ρ)
    (hlarge : ρ ≤ ‖integerIntervalMean N
      (fun t => circleCharacter (quadraticCirclePolynomial a₂ a₁ a₀ t))‖)
    (hscale : 2 ≤ (N : ℝ) * ρ ^ 2) :
    ∃ s : Finset ℤ, s ⊆ horizontalShiftLabels N ∧ (N : ℝ) * ρ ^ 2 / 4 ≤ s.card ∧
      ∀ h ∈ s, ‖(2 * h) • a₂‖ ≤ 4 / (ρ ^ 2 * (N : ℝ)) := by
  refine ⟨largeWeylShifts N
    (fun t => circleCharacter (quadraticCirclePolynomial a₂ a₁ a₀ t)) (ρ ^ 2 / 8),
    Finset.filter_subset _ _, ?_, ?_⟩
  · exact many_large_weyl_correlations hN _ (fun t => (norm_circleCharacter _).le)
      hρ.le hlarge hscale
  · intro h hh
    exact quadratic_large_shift_control hN a₂ a₁ a₀ hρ hh

end GMZP0
