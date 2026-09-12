import GMZP0.OrdinaryProfiles

/-! Actual large ordinary-profile blocks force current-row top-coefficient returns.
The general-degree Weyl estimate is an explicit external analytic premise. -/
noncomputable section
open scoped BigOperators
open Polynomial
namespace GMZP0

/-- The leading-coefficient specialization of the manuscript's external Weyl estimate.
This proposition is not proved and is not declared as an axiom. -/
def PolynomialLeadingWeylInput : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∀ c : ℝ, 0 < c →
    ∃ Q : ℕ, ∃ E : ℝ, ∃ N₀ : ℕ, 0 < Q ∧ 0 < E ∧ 0 < N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ L U : ℤ, 1 ≤ L → U ≤ N → ∀ P : ℝ[X], P.natDegree ≤ d →
        c * (N : ℝ) ≤ ‖∑ r ∈ Finset.Icc L U, circleCharacter ((P.eval (r : ℝ) : ℝ) : Frequency)‖ →
        ∃ q : ℕ, 0 < q ∧ q ≤ Q ∧ ‖q • (P.coeff d : Frequency)‖ ≤ E / (N : ℝ) ^ d

/-- The external input applies to the actual shorter lag interval with the original N normalization. -/
theorem uniform_polynomial_lag_leading_coefficient (hW : PolynomialLeadingWeylInput)
    (d : ℕ) (hd : 1 ≤ d) (c : ℝ) (hc : 0 < c) :
    ∃ Q : ℕ, ∃ E : ℝ, ∃ N₀ : ℕ, 0 < Q ∧ 0 < E ∧ 0 < N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ h k : ℤ, ∀ P : ℝ[X], P.natDegree ≤ d →
        c * (N : ℝ) ≤ ‖∑ r ∈ lagLabels N h k, circleCharacter ((P.eval (r : ℝ) : ℝ) : Frequency)‖ →
        ∃ q : ℕ, 0 < q ∧ q ≤ Q ∧ ‖q • (P.coeff d : Frequency)‖ ≤ E / (N : ℝ) ^ d := by
  obtain ⟨Q, E, N₀, hQ, hE, hN₀, hw⟩ := hW d hd c hc
  refine ⟨Q, E, N₀, hQ, hE, hN₀, ?_⟩
  intro N hN h k P hP hsum
  rw [lagLabels_eq_interval] at hsum
  exact hw N hN _ _ (by omega) (by omega) P hP hsum

/-- The fixed integer factor is absorbed into a positive multiplier, never cancelled on the circle. -/
theorem ordinary_top_scalar_factor (a : Frequency) (D q : ℕ) (h : ℤ) :
    q • ((-3 * (2 * h) ^ D) • a) = -((3 * 2 ^ D * q) • (h ^ D • a)) := by
  simp only [mul_pow]
  module

/-- Reversal changes only a sign in the power return, without changing its norm. -/
theorem ordinary_power_return_reverse (a : Frequency) (D q : ℕ) (h : ℤ) :
    ‖q • ((-h) ^ D • a)‖ = ‖q • (h ^ D • a)‖ := by
  rcases Nat.even_or_odd D with he | ho
  · rw [he.neg_pow]
  · rw [ho.neg_pow, neg_zsmul, smul_neg, norm_neg]

/-- One actual large block gives the partner-row top-coefficient relation at N^(-(D+3)). -/
theorem uniform_ordinary_block_partner_relation (hW : PolynomialLeadingWeylInput)
    (D : ℕ) (hD : 2 ≤ D) (v : ℝ) (hv : 0 < v) :
    ∃ Q : ℕ, ∃ E : ℝ, ∃ N₀ : ℕ, 0 < Q ∧ 0 < E ∧ 0 < N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ P : Fin N → ℝ[X], (∀ x, (P x).natDegree ≤ D) →
      ∀ m : Base N → ℂ, (∀ z, ‖m z‖ ≤ 1) → ∀ x x' : Fin N, x ≠ x' →
      (¬ KernelEnergyBound (blockGramKernel
        (outputMaskedKernel (responseKernel N (ordinaryOriginalProfile P)) m) x x') (v / N)) →
      ∃ n : ℕ, 0 < n ∧ n ≤ Q ∧
        ‖n • (horizontalGap x x' ^ D • ((P x').coeff D : Frequency))‖ ≤ E / (N : ℝ) ^ (D + 3) := by
  obtain ⟨c, hc, N₁, hN₁, hlags⟩ := uniform_masked_large_block_many_lags v hv
  obtain ⟨B, C, N₂, hB, hC, hN₂, hw⟩ := uniform_polynomial_lag_leading_coefficient hW (D + 2) (by omega) c hc
  obtain ⟨Q, E, N₃, hQ, hE, hN₃, hr⟩ := uniform_bounded_multiplier_affine_returns c C hc hC B hB
  refine ⟨3 * 2 ^ D * Q, E, max N₁ (max N₂ N₃), by positivity, hE,
    hN₁.trans_le (le_max_left _ _), ?_⟩
  intro N hN P hP m hm x x' hx hlarge
  have h1 : N₁ ≤ N := (le_max_left _ _).trans hN
  have h2 : N₂ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have h3 : N₃ ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  obtain ⟨K, root, hcard, hK⟩ := hlags N h1 (ordinaryVerticalProfile P) (ordinaryOriginalProfile P)
    (ordinary_profile_agreement P) m hm x x' hx hlarge
  let a : Frequency := (-3 * (2 * horizontalGap x x') ^ D) • ((P x').coeff D : Frequency)
  have hsub : K ⊆ Finset.Icc (-(N : ℤ)) N := by
    intro k hk
    have hh := abs_lt.mp (hK k hk).2.1
    exact Finset.mem_Icc.mpr ⟨hh.1.le, hh.2.le⟩
  have hreturns : ∀ k ∈ K, ∃ q : ℕ, 0 < q ∧ q ≤ B ∧ ‖q • (k • a + 0)‖ ≤ C / (N : ℝ) ^ (D + 2) := by
    intro k hk
    have hsum := (hK k hk).2.2
    rw [ordinary_wideLagSum] at hsum
    obtain ⟨q, hq, hqB, hb⟩ := hw N h2 (horizontalGap x x') k
      (ordinaryDoublePhasePolynomial (P x) (P x') (label (root k) : ℝ) (horizontalGap x x' : ℝ) (k : ℝ))
      (ordinaryDoublePhasePolynomial_degree (P x) (P x') D (by omega) (hP x') _ _ _) hsum
    have hcoeff := ordinary_wide_top_coefficient P D hD hP x x' (label (root k)) k
    simp only [Int.cast_natCast] at hcoeff
    rw [hcoeff] at hb
    have he : k • a + 0 = (-3 * k * (2 * horizontalGap x x') ^ D) • ((P x').coeff D : Frequency) := by
      dsimp only [a]
      module
    exact ⟨q, hq, hqB, by simpa only [he] using hb⟩
  obtain ⟨q, hq, hqQ, hb⟩ := hr (D + 2) (by omega) N h3 a 0 K hsub hcard hreturns
  refine ⟨3 * 2 ^ D * q, by positivity, Nat.mul_le_mul_left (3 * 2 ^ D) hqQ, ?_⟩
  dsimp only [a] at hb
  simpa only [ordinary_top_scalar_factor, norm_neg, Nat.add_assoc] using hb

/-- Apply the argument to the reversed actual compressed block to read the original current row. -/
theorem uniform_ordinary_block_row_relation (hW : PolynomialLeadingWeylInput)
    (D : ℕ) (hD : 2 ≤ D) (v : ℝ) (hv : 0 < v) :
    ∃ Q : ℕ, ∃ E : ℝ, ∃ N₀ : ℕ, 0 < Q ∧ 0 < E ∧ 0 < N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ P : Fin N → ℝ[X], (∀ x, (P x).natDegree ≤ D) →
      ∀ m : Base N → ℂ, (∀ z, ‖m z‖ ≤ 1) → ∀ x x' : Fin N, x ≠ x' →
      (¬ KernelEnergyBound (blockGramKernel
        (outputMaskedKernel (responseKernel N (ordinaryOriginalProfile P)) m) x x') (v / N)) →
      ∃ n : ℕ, 0 < n ∧ n ≤ Q ∧
        ‖n • (horizontalGap x x' ^ D • ((P x).coeff D : Frequency))‖ ≤ E / (N : ℝ) ^ (D + 3) := by
  obtain ⟨Q, E, N₀, hQ, hE, hN₀, hp⟩ := uniform_ordinary_block_partner_relation hW D hD v hv
  refine ⟨Q, E, N₀, hQ, hE, hN₀, ?_⟩
  intro N hN P hP m hm x x' hx hlarge
  have hreverse : ¬ KernelEnergyBound (blockGramKernel
      (outputMaskedKernel (responseKernel N (ordinaryOriginalProfile P)) m) x' x) (v / N) := by
    intro hh
    exact hlarge ((blockGramKernel_energy_bound_symm _ (v / N) x x').2 hh)
  obtain ⟨q, hq, hqQ, hb⟩ := hp N hN P hP m hm x' x hx.symm hreverse
  have he : horizontalGap x' x = -horizontalGap x x' := by unfold horizontalGap; ring
  rw [he, ordinary_power_return_reverse] at hb
  exact ⟨q, hq, hqQ, hb⟩

end GMZP0
