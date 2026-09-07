import GMZP0.UniformSafeWindow

/-! Uniform positivity of the original finite signed statistic on a positive-mass safe window. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

theorem original_weight_mass_le_one {N : ℕ} (hN : 0 < N) (μ : Base N → ℝ)
    (D : Finset (Base N)) (hμ : ∀ z, μ z ≤ (N : ℝ)⁻¹ ^ 3) :
    (∑ z ∈ D, μ z) ≤ 1 := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hcard : D.card ≤ N ^ 3 := by simpa only [card_base] using Finset.card_le_univ D
  have hc : (D.card : ℝ) ≤ (N : ℝ) ^ 3 := by
    exact_mod_cast hcard
  calc
    (∑ z ∈ D, μ z) ≤ ∑ _z ∈ D, (N : ℝ)⁻¹ ^ 3 := Finset.sum_le_sum fun z _ => hμ z
    _ = (D.card : ℝ) * (N : ℝ)⁻¹ ^ 3 := by simp
    _ ≤ (N : ℝ) ^ 3 * (N : ℝ)⁻¹ ^ 3 :=
      mul_le_mul_of_nonneg_right hc (pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N)) 3)
    _ = 1 := by field_simp

/-- Explicit arithmetic converting the two diagonal error bounds into a positive statistic. -/
theorem positive_from_signed_bound (a R S d : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hR : a ≤ R ^ 2) (hd : d ≤ a ^ 2 / 128)
    (hS : max (R ^ 2 / 4 - d) 0 ^ 2 ≤ S + d) : a ^ 2 / 128 ≤ S := by
  have haSq : a ^ 2 ≤ a := by nlinarith only [ha0, ha1]
  have hsmall : d ≤ a / 8 := by nlinarith only [hd, haSq, ha0]
  have hmax : a / 8 ≤ max (R ^ 2 / 4 - d) 0 := by
    apply le_trans _ (le_max_left _ _)
    linarith only [hR, hsmall]
  have hsquare := pow_le_pow_left₀ (div_nonneg ha0 (by norm_num : (0 : ℝ) ≤ 8)) hmax 2
  nlinarith only [hsquare, hS, hd]

def finiteStatisticThreshold (η c : ℝ) : ℕ := Nat.ceil (128 / (η ^ 4 * c ^ 4)) + 1

theorem finiteStatisticThreshold_pos (η c : ℝ) : 0 < finiteStatisticThreshold η c := Nat.succ_pos _

/-- The large-scale threshold depends only on eta and the fixed retained-mass lower bound. -/
theorem uniform_positive_from_signed_bound {N : ℕ} (η c m R S : ℝ)
    (hη : 0 < η) (hη1 : η ≤ 1) (hc : 0 < c) (hcm : c ≤ m) (hm1 : m ≤ 1)
    (hN : finiteStatisticThreshold η c ≤ N) (hR : η * m ≤ R)
    (hS : max (R ^ 2 / 4 - m / (N : ℝ)) 0 ^ 2 ≤ S + m / (N : ℝ)) :
    η ^ 4 * m ^ 4 / 128 ≤ S := by
  have hNpos : 0 < N := (finiteStatisticThreshold_pos η c).trans_le hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hm0 : 0 < m := hc.trans_le hcm
  have hprod0 : 0 ≤ η * m := mul_nonneg hη.le hm0.le
  have hprod1 : η * m ≤ 1 := by
    calc
      η * m ≤ 1 * m := mul_le_mul_of_nonneg_right hη1 hm0.le
      _ ≤ 1 := by simpa using hm1
  have ha1 : (η * m) ^ 2 ≤ 1 := by
    simpa using pow_le_pow_left₀ hprod0 hprod1 2
  have hR2 := pow_le_pow_left₀ hprod0 hR 2
  have hceil : Nat.ceil (128 / (η ^ 4 * c ^ 4)) ≤ N := by
    unfold finiteStatisticThreshold at hN
    omega
  have hscale : 128 / (η ^ 4 * c ^ 4) ≤ (N : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hceil)
  have hden : 0 < η ^ 4 * c ^ 4 := mul_pos (pow_pos hη 4) (pow_pos hc 4)
  have hcross := (div_le_iff₀ hden).1 hscale
  have hone : 1 / (N : ℝ) ≤ (η ^ 4 * c ^ 4) / 128 := by
    apply (div_le_iff₀ hNr).2
    nlinarith only [hcross]
  have hd : m / (N : ℝ) ≤ η ^ 4 * m ^ 4 / 128 := by
    calc
      m / (N : ℝ) ≤ 1 / (N : ℝ) := div_le_div_of_nonneg_right hm1 hNr.le
      _ ≤ (η ^ 4 * c ^ 4) / 128 := hone
      _ ≤ (η ^ 4 * m ^ 4) / 128 := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hc.le hcm 4) (pow_nonneg hη.le 4))
          (by norm_num)
  have heq : η ^ 4 * m ^ 4 = ((η * m) ^ 2) ^ 2 := by ring
  rw [heq] at hd ⊢
  exact positive_from_signed_bound ((η * m) ^ 2) R S (m / (N : ℝ))
    (sq_nonneg _) ha1 hR2 hd hS

/-- Uniform positive safe finite statistics for all original admissible data.
No equality with the paper's lag-indexed statistic is included in this statement. -/
theorem uniform_positive_safe_statistic (κ η : ℝ) (hκ : 0 < κ) (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ M : ℕ, ∃ c ζ : ℝ, ∃ N₀ : ℕ,
      0 < M ∧ 0 < c ∧ 0 < ζ ∧ 0 < N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ (f : ℤ × ℤ → ℂ) (θ : Base N → Frequency)
        (lam : Base N → ℂ) (μ : Base N → ℝ), Admissible N κ η f θ lam μ →
        ∃ X : Finset (Fin N), ∃ D : Finset (Base N), ∃ a : ℕ,
          D = X ×ˢ safeRows N (N / M) ∧
          (∀ x : Fin N, x ∈ X ↔ a ≤ x.val ∧ x.val ≤ a + N / M) ∧
          c ≤ ∑ z ∈ D, μ z ∧
          (∀ x ∈ X, ∀ x' ∈ X, |(x'.val : ℤ) - (x.val : ℤ)| ≤ (N / M : ℕ)) ∧
          (∀ z ∈ D, SafeVertical (N : ℤ) (N / M : ℕ) (basePoint z).2) ∧
          η * (∑ z ∈ D, μ z) ≤ ‖weightedOriginalResponse N f θ (originalScaledWeight N μ D) lam‖ ∧
          2 * ζ ≤ finiteSignedDoubleStatistic N θ X (alignedWeightVector (originalScaledWeight N μ D) lam) ∧
          (∀ z ∈ D, μ z ≠ 0 → η ≤ (lam z * response N f z (θ z)).re) := by
  obtain ⟨M, c, hM, hc, _, hwindow⟩ := uniform_safe_window κ hκ
  refine ⟨M, c, η ^ 4 * c ^ 4 / 256, finiteStatisticThreshold η c, hM, hc,
    div_pos (mul_pos (pow_pos hη 4) (pow_pos hc 4)) (by norm_num),
    finiteStatisticThreshold_pos η c, ?_⟩
  intro N hNth f θ lam μ hdata
  have hN : 0 < N := (finiteStatisticThreshold_pos η c).trans_le hNth
  obtain ⟨hf, hlam, hμ, hmass, hresponse⟩ := hdata
  obtain ⟨X, D, a, hDX, hinterval, hmassD, hgap, hsafe⟩ := hwindow N hN μ hμ hmass
  have hDX' : ∀ z ∈ D, z.1 ∈ X := by
    intro z hz
    rw [hDX] at hz
    exact (Finset.mem_product.mp hz).1
  have hR := original_window_response_lower hN μ D hμ f θ lam η hresponse
  have hS := original_window_finite_signed_lower hN f hf θ μ D X hDX' lam hlam hμ
  have hmass1 := original_weight_mass_le_one hN μ D (fun z => (hμ z).2)
  have hpositive := uniform_positive_from_signed_bound η c (∑ z ∈ D, μ z)
    ‖weightedOriginalResponse N f θ (originalScaledWeight N μ D) lam‖
    (finiteSignedDoubleStatistic N θ X (alignedWeightVector (originalScaledWeight N μ D) lam))
    hη hη1 hc hmassD hmass1 hNth hR hS
  refine ⟨X, D, a, hDX, hinterval, hmassD, hgap, hsafe, hR, ?_, ?_⟩
  · have hp := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hc.le hmassD 4) (pow_nonneg hη.le 4)
    linarith only [hp, hpositive]
  · exact fun z _ hz => hresponse z hz

end GMZP0
