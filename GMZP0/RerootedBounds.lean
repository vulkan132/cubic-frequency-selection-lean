import GMZP0.RerootedStatistic

/-! Pointwise modulus bounds and a weighted positive outer average for the original rerooted B. -/

noncomputable section
open scoped BigOperators ComplexConjugate
namespace GMZP0

theorem originalFieldExtension_property {V : Type*} (N : ℕ) (F : Base N → V)
    (fallback : V) (P : V → Prop) (hF : ∀ z, P (F z)) (hdefault : P fallback) (w : ℤ × ℤ) :
    P (originalFieldExtension N F fallback w) := by
  unfold originalFieldExtension
  split_ifs
  · exact hF _
  · exact hdefault
  · exact hdefault

theorem norm_circleCharacter (a : Frequency) : ‖circleCharacter a‖ = 1 := by
  exact Circle.norm_coe _

theorem rerootedOuterPhase_norm (N : ℕ) (p : Base N → Frequency) (lam : Base N → ℂ)
    (x : Fin N) (y : Fin (N ^ 2)) (h t : ℤ) (hlam : ‖lam (x, y)‖ = 1) :
    ‖rerootedOuterPhase N p lam x y h t‖ = 1 := by
  simp only [rerootedOuterPhase, norm_mul, hlam, norm_circleCharacter, mul_one]

theorem rerootedLagG_norm_le (N : ℕ) (p : Base N → Frequency) (σ : Base N → ℝ)
    (lam : Base N → ℂ) (x : Fin N) (y : Fin (N ^ 2)) (h t k : ℤ)
    (hσ : ∀ z, 0 ≤ σ z ∧ σ z ≤ 1) (hlam : ∀ z, ‖lam z‖ = 1) :
    ‖rerootedLagG N p σ lam x y h t k‖ ≤ 1 := by
  let z : ℤ × ℤ := ((x.val : ℤ) + 1, (y.val : ℤ) + 1 + 2 * h * k)
  have hs := originalFieldExtension_property N σ 0 (fun a : ℝ => 0 ≤ a ∧ a ≤ 1)
    hσ ⟨le_rfl, zero_le_one⟩ z
  have hl := originalFieldExtension_property N lam 1 (fun a : ℂ => ‖a‖ = 1)
    hlam (by simp) z
  dsimp only [rerootedLagG]
  change ‖((originalFieldExtension N σ 0 z : ℝ) : ℂ) * conj (originalFieldExtension N lam 1 z) *
    circleCharacter (-((t + h - k) ^ 3 • originalFieldExtension N p 0 z))‖ ≤ 1
  simp only [norm_mul, Complex.norm_conj, hl, norm_circleCharacter, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]
  exact hs.2

theorem lagInnerInterval_card_le (N : ℕ) (h t : ℤ) : (lagInnerInterval N h t).card ≤ N := by
  calc
    (lagInnerInterval N h t).card ≤ (Finset.Icc (t - N) (t - 1)).card :=
      Finset.card_le_card Finset.inter_subset_left
    _ = N := by
      rw [Int.card_Icc]
      have he : t - 1 + 1 - (t - N) = (N : ℤ) := by ring
      rw [he, Int.toNat_natCast]

theorem rerootedLagB_norm_le {N : ℕ} (hN : 0 < N) (p : Base N → Frequency)
    (σ : Base N → ℝ) (lam : Base N → ℂ) (x x' : Fin N) (y : Fin (N ^ 2)) (t : ℤ)
    (hσ : ∀ z, 0 ≤ σ z ∧ σ z ≤ 1) (hlam : ∀ z, ‖lam z‖ = 1) :
    ‖rerootedLagB N p σ lam x x' y t‖ ≤ 1 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [rerootedLagB, norm_div, Complex.norm_natCast]
  apply (div_le_iff₀ hNr).2
  rw [one_mul]
  calc
    ‖∑ k ∈ lagInnerInterval N (horizontalGap x x') t,
        rerootedLagG N p σ lam x y (horizontalGap x x') t k *
          circleCharacter (rerootedLagP N p x' y (horizontalGap x x') t k)‖ ≤
        ∑ k ∈ lagInnerInterval N (horizontalGap x x') t,
          ‖rerootedLagG N p σ lam x y (horizontalGap x x') t k *
            circleCharacter (rerootedLagP N p x' y (horizontalGap x x') t k)‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ lagInnerInterval N (horizontalGap x x') t, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul, norm_circleCharacter, mul_one]
      exact rerootedLagG_norm_le N p σ lam x y (horizontalGap x x') t k hσ hlam
    _ = ((lagInnerInterval N (horizontalGap x x') t).card : ℝ) := by simp
    _ ≤ N := by exact_mod_cast lagInnerInterval_card_le N (horizontalGap x x') t

def rerootedNormSum (N : ℕ) (p : Base N → Frequency) (X : Finset (Fin N))
    (σ : Base N → ℝ) (lam : Base N → ℂ) : ℝ :=
  ∑ x : Fin N, ∑ x' : Fin N, if x ∈ X ∧ x' ∈ X ∧ x' ≠ x then
    ∑ y : Fin (N ^ 2), ∑ t ∈ rerootLabels N (horizontalGap x x'),
      σ (x, y) * ‖rerootedLagB N p σ lam x x' y t‖ else 0

theorem rerootedWeightedSum_le_normSum (N : ℕ) (p : Base N → Frequency)
    (X : Finset (Fin N)) (σ : Base N → ℝ) (lam : Base N → ℂ)
    (hσ : ∀ z, 0 ≤ σ z) (hlam : ∀ z, ‖lam z‖ = 1) :
    rerootedWeightedSum N p X σ lam ≤ rerootedNormSum N p X σ lam := by
  apply Finset.sum_le_sum
  intro x _
  apply Finset.sum_le_sum
  intro x' _
  split_ifs
  · apply Finset.sum_le_sum
    intro y _
    apply Finset.sum_le_sum
    intro t _
    apply mul_le_mul_of_nonneg_left _ (hσ _)
    calc
      (rerootedOuterPhase N p lam x y (horizontalGap x x') t * rerootedLagB N p σ lam x x' y t).re ≤
          ‖rerootedOuterPhase N p lam x y (horizontalGap x x') t * rerootedLagB N p σ lam x x' y t‖ :=
        Complex.re_le_norm _
      _ = _ := by rw [norm_mul, rerootedOuterPhase_norm N p lam x y _ t (hlam _), one_mul]
  · exact le_rfl

theorem lagSigned_le_rerootedNormSum {N : ℕ} (hN : 0 < N) (p : Base N → Frequency)
    (X : Finset (Fin N)) (σ : Base N → ℝ) (lam : Base N → ℂ)
    (hσ : ∀ z, 0 ≤ σ z) (hlam : ∀ z, ‖lam z‖ = 1) :
    lagSignedDoubleStatistic N p X σ lam ≤ rerootedNormSum N p X σ lam / (N : ℝ) ^ 5 := by
  calc
    lagSignedDoubleStatistic N p X σ lam ≤ fullLagStatistic N p X σ lam := lagSigned_le_full N p X σ lam
    _ = _ := fullLagStatistic_reroot hN p X σ lam
    _ ≤ _ := div_le_div_of_nonneg_right (rerootedWeightedSum_le_normSum N p X σ lam hσ hlam)
      (pow_nonneg (Nat.cast_nonneg _) 5)

end GMZP0
