import GMZP0.FiniteSelection

/-!
The fully quantified reduction from weighted finite capture to P0.
Weighted capture remains an explicit hypothesis, not a new axiom.
-/

noncomputable section
open scoped BigOperators
namespace GMZP0

/-- Alignment exists also when the original complex response vanishes. -/
theorem exists_response_alignment (w : ℂ) :
    ∃ lam : ℂ, ‖lam‖ = 1 ∧ (lam * w).re = ‖w‖ := by
  obtain ⟨lam, hlam, heq⟩ := Complex.exists_norm_eq_mul_self w
  refine ⟨lam, hlam, ?_⟩
  rw [← heq]
  rfl

/-- Uniform counting weight restricted using the prescribed original response. -/
def thresholdWeight {Z : Type*} [Fintype Z] (δ : ℝ) (v : Z → ℝ) (z : Z) : ℝ :=
  if δ / 2 ≤ v z then (Fintype.card Z : ℝ)⁻¹ else 0

theorem thresholdWeight_bounds {Z : Type*} [Fintype Z] (δ : ℝ) (v : Z → ℝ) (z : Z) :
    0 ≤ thresholdWeight δ v z ∧ thresholdWeight δ v z ≤ (Fintype.card Z : ℝ)⁻¹ := by
  unfold thresholdWeight
  split_ifs <;> constructor <;> first | exact le_rfl | positivity

theorem thresholdWeight_support {Z : Type*} [Fintype Z] (δ : ℝ) (v : Z → ℝ) (z : Z)
    (hz : thresholdWeight δ v z ≠ 0) : δ / 2 ≤ v z := by
  by_contra h
  exact hz (by simp [thresholdWeight, h])

/-- A mean at least delta puts mass at least delta/2 on original responses >= delta/2. -/
theorem thresholdWeight_mass {Z : Type*} [Fintype Z] [Nonempty Z]
    (δ : ℝ) (hδ : 0 < δ) (v : Z → ℝ) (hv : ∀ z, v z ≤ 1)
    (hmean : δ ≤ (∑ z, v z) / (Fintype.card Z : ℝ)) :
    δ / 2 ≤ ∑ z, thresholdWeight δ v z := by
  have hc : (0 : ℝ) < Fintype.card Z := by exact_mod_cast Fintype.card_pos
  have hpoint (z : Z) : v z ≤ δ / 2 + (Fintype.card Z : ℝ) * thresholdWeight δ v z := by
    unfold thresholdWeight
    split_ifs with hz
    · rw [mul_inv_cancel₀ hc.ne']
      linarith [hv z]
    · simp only [mul_zero, add_zero]
      exact (lt_of_not_ge hz).le
  have hsum := Finset.sum_le_sum (fun z (_ : z ∈ (Finset.univ : Finset Z)) => hpoint z)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, ← Finset.mul_sum] at hsum
  have hinput := (le_div_iff₀ hc).mp hmean
  nlinarith

/-- Construct admissible data from the original prescribed response, without a model. -/
theorem original_admissible_data {N : ℕ} (hN : 0 < N) (δ : ℝ) (hδ : 0 < δ)
    (f : ℤ × ℤ → ℂ) (hf : ∀ w, ‖f w‖ ≤ 1) (θ : Base N → Frequency)
    (hmean : δ ≤ meanResponse N f θ) :
    ∃ (lam : Base N → ℂ) (μ : Base N → ℝ), Admissible N (δ / 2) (δ / 2) f θ lam μ := by
  classical
  let : Nonempty (Base N) := ⟨(⟨0, hN⟩, ⟨0, pow_pos hN 2⟩)⟩
  choose lam hlam halign using fun z : Base N => exists_response_alignment (response N f z (θ z))
  let v : Base N → ℝ := fun z => ‖response N f z (θ z)‖
  refine ⟨lam, thresholdWeight δ v, hf, hlam, ?_, ?_, ?_⟩
  · intro z
    simpa only [card_base, Nat.cast_pow, inv_pow] using thresholdWeight_bounds δ v z
  · apply thresholdWeight_mass δ hδ v (fun z => norm_response_le_one hN f hf z (θ z))
    simpa only [meanResponse, card_base, Nat.cast_pow] using hmean
  · intro z hz
    rw [halign z]
    exact thresholdWeight_support δ v z hz

/-- Weighted finite capture implies P0, with the scale-uniform constant chosen before all data. -/
theorem p0_of_weightedCapture (hcapture : WeightedCapture) : P0 := by
  intro δ hδ hδ1
  obtain ⟨c, hc, L, N₀, hL, hN₀, hcap⟩ :=
    hcapture (δ / 2) (δ / 2) (δ / 4) (by positivity) (by linarith)
      (by positivity) (by linarith) (by positivity) (by linarith)
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hN₀r : (0 : ℝ) < N₀ := by exact_mod_cast hN₀
  have hlargepos : 0 < (δ / 2 - δ / 4) * c / (L : ℝ) :=
    div_pos (mul_pos (by linarith) hc) hLr
  have hsmallpos : 0 < δ / (N₀ : ℝ) ^ 3 := div_pos hδ (pow_pos hN₀r _)
  refine ⟨min ((δ / 2 - δ / 4) * c / (L : ℝ)) (δ / (N₀ : ℝ) ^ 3),
    lt_min hlargepos hsmallpos, ?_⟩
  intro N hN f θ hf hmean
  have hNpos : 0 < N := hN
  by_cases hlarge : N₀ ≤ N
  · obtain ⟨β, hβ⟩ := hcap N hlarge
    obtain ⟨lam, μ, hadm⟩ := original_admissible_data hNpos δ hδ f hf θ hmean
    obtain ⟨A, j, hsupp, hmass, hclose⟩ := hβ f θ lam μ hadm
    obtain ⟨b, hb⟩ := captured_response_lower_bound hNpos hL f hf θ lam μ β A j
      (δ / 2) (δ / 4) c (by linarith)
      (fun z _ => hadm.2.2.1 z) hmass (fun z _ => hadm.2.1 z)
      (fun z hz => hadm.2.2.2.2 z (hsupp z hz)) hclose
    exact ⟨b, (min_le_left _ _).trans hb⟩
  · obtain ⟨b, hb⟩ := small_scale_selection hNpos f θ δ hmean
    have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
    have hNN₀ : (N : ℝ) ≤ N₀ := by exact_mod_cast (lt_of_not_ge hlarge).le
    have hdenom : (N : ℝ) ^ 3 ≤ (N₀ : ℝ) ^ 3 := pow_le_pow_left₀ hNr.le hNN₀ 3
    have hsmall : δ / (N₀ : ℝ) ^ 3 ≤ δ / (N : ℝ) ^ 3 :=
      div_le_div_of_nonneg_left hδ.le (pow_pos hNr _) hdenom
    exact ⟨b, (min_le_right _ _).trans (hsmall.trans hb)⟩

end GMZP0
