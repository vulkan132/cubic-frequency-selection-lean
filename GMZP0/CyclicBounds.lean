import GMZP0.CyclicNormalization

/-! Bounds hold on the entire cyclic group, including the shifts used later in smoothing. -/

noncomputable section
open scoped BigOperators ComplexConjugate
namespace GMZP0

theorem cyclicField_property {V : Type*} (N q : ℕ) (F : Base N → V) (fallback : V)
    (P : V → Prop) (hF : ∀ z, P (F z)) (hdefault : P fallback) (x : Fin N) (v : ZMod q) :
    P (cyclicField N q F fallback x v) :=
  originalFieldExtension_property N F fallback P hF hdefault _

theorem cyclicLagG_norm_le (N q : ℕ) (p : Base N → Frequency) (σ : Base N → ℝ)
    (lam : Base N → ℂ) (x : Fin N) (v : ZMod q) (h t k : ℤ)
    (hσ : ∀ z, 0 ≤ σ z ∧ σ z ≤ 1) (hlam : ∀ z, ‖lam z‖ = 1) :
    ‖cyclicLagG N q p σ lam x v h t k‖ ≤ 1 := by
  let z := v + ((2 * h * k : ℤ) : ZMod q)
  have hs := cyclicField_property N q σ 0 (fun a : ℝ => 0 ≤ a ∧ a ≤ 1)
    hσ ⟨le_rfl, zero_le_one⟩ x z
  have hl := cyclicField_property N q lam 1 (fun a : ℂ => ‖a‖ = 1) hlam (by simp) x z
  dsimp only [cyclicLagG]
  change ‖((cyclicField N q σ 0 x z : ℝ) : ℂ) * conj (cyclicField N q lam 1 x z) *
    circleCharacter (-((t + h - k) ^ 3 • cyclicField N q p 0 x z))‖ ≤ 1
  simp only [norm_mul, Complex.norm_conj, hl, norm_circleCharacter, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]
  exact hs.2

theorem cyclicShiftLagB_norm_le {N : ℕ} (hN : 0 < N) (q : ℕ)
    (p : Base N → Frequency) (σ : Base N → ℝ) (lam : Base N → ℂ)
    (x : Fin N) (v : ZMod q) (h t : ℤ)
    (hσ : ∀ z, 0 ≤ σ z ∧ σ z ≤ 1) (hlam : ∀ z, ‖lam z‖ = 1) :
    ‖cyclicShiftLagB N q p σ lam x v h t‖ ≤ 1 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [cyclicShiftLagB, norm_div, Complex.norm_natCast]
  apply (div_le_iff₀ hNr).2
  rw [one_mul]
  calc
    ‖∑ k ∈ lagInnerInterval N h t, cyclicLagG N q p σ lam x v h t k *
        circleCharacter (cyclicShiftLagP N q p x v h t k)‖ ≤
        ∑ k ∈ lagInnerInterval N h t, ‖cyclicLagG N q p σ lam x v h t k *
          circleCharacter (cyclicShiftLagP N q p x v h t k)‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ lagInnerInterval N h t, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul, norm_circleCharacter, mul_one]
      exact cyclicLagG_norm_le N q p σ lam x v h t k hσ hlam
    _ = ((lagInnerInterval N h t).card : ℝ) := by simp
    _ ≤ N := by exact_mod_cast lagInnerInterval_card_le N h t

end GMZP0
