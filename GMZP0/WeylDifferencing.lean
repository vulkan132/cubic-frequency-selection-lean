import GMZP0.LinearWeyl
import GMZP0.HorizontalShiftReindexing

/-! Exact interval differencing, with the zero shift and the scale threshold explicit. -/

noncomputable section
open scoped BigOperators ComplexConjugate
namespace GMZP0

theorem sum_fin_labels {M : Type*} [AddCommMonoid M] (N : ℕ) (F : ℤ → M) :
    (∑ r : Fin N, F (label r)) = ∑ r ∈ Finset.Icc (1 : ℤ) N, F r := by
  apply Finset.sum_bij (fun r _ => (label r : ℤ))
  · intro r _
    simp only [Finset.mem_Icc, label, Nat.cast_add, Nat.cast_one]
    constructor <;> omega
  · intro r _ s _ he
    apply Fin.ext
    simp only [label, Nat.cast_add, Nat.cast_one] at he
    omega
  · intro k hk
    have hk' := Finset.mem_Icc.mp hk
    refine ⟨⟨(k - 1).toNat, by omega⟩, Finset.mem_univ _, ?_⟩
    simp only [label, Nat.cast_add, Nat.cast_one]
    omega
  · intro r _
    rfl

def integerIntervalMean (N : ℕ) (F : ℤ → ℂ) : ℂ :=
  (∑ r ∈ Finset.Icc (1 : ℤ) N, F r) / (N : ℂ)

def weylCorrelation (N : ℕ) (F : ℤ → ℂ) (h : ℤ) : ℂ :=
  (∑ r ∈ Finset.Icc (1 : ℤ) N,
    if r + h ∈ Finset.Icc (1 : ℤ) N then F (r + h) * conj (F r) else 0) / (N : ℂ)

theorem integerIntervalMean_eq_fin (N : ℕ) (F : ℤ → ℂ) :
    integerIntervalMean N F = complexUniformMean (fun r : Fin N => F (label r)) := by
  rw [integerIntervalMean, complexUniformMean, Fintype.card_fin, sum_fin_labels]

theorem interval_pair_difference_sum {M : Type*} [AddCommMonoid M]
    (N : ℕ) (F : ℤ → ℤ → M) :
    (∑ a ∈ Finset.Icc (1 : ℤ) N, ∑ b ∈ Finset.Icc (1 : ℤ) N, F (a - b) b) =
      ∑ h ∈ Finset.Icc (-(N : ℤ)) N, ∑ b ∈ Finset.Icc (1 : ℤ) N,
        if b + h ∈ Finset.Icc (1 : ℤ) N then F h b else 0 := by
  classical
  let s := Finset.Icc (1 : ℤ) N
  let t := ((Finset.Icc (-(N : ℤ)) N) ×ˢ s).filter (fun hb => hb.2 + hb.1 ∈ s)
  change (∑ a ∈ s, ∑ b ∈ s, F (a - b) b) = _
  rw [← Finset.sum_product']
  calc
    (∑ ab ∈ s ×ˢ s, F (ab.1 - ab.2) ab.2) = ∑ hb ∈ t, F hb.1 hb.2 := by
      apply Finset.sum_bij (fun ab _ => (ab.1 - ab.2, ab.2))
      · intro ab hab
        simp only [s, Finset.mem_product, Finset.mem_Icc] at hab
        simp only [t, s, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
        omega
      · intro a _ b _ he
        have h1 := congrArg Prod.fst he
        have h2 := congrArg Prod.snd he
        apply Prod.ext <;> dsimp at h1 h2 ⊢ <;> omega
      · intro hb hhb
        simp only [t, s, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hhb
        refine ⟨(hb.2 + hb.1, hb.2), ?_, ?_⟩
        · simp only [s, Finset.mem_product, Finset.mem_Icc]
          omega
        · apply Prod.ext
          · change hb.2 + hb.1 - hb.2 = hb.1
            omega
          · rfl
      · intro ab _
        rfl
    _ = _ := by
      dsimp [t]
      rw [Finset.sum_filter, Finset.sum_product]

/-- The zero-extended interval correlation is exactly the original full pair sum. -/
theorem weyl_correlation_sum (N : ℕ) (F : ℤ → ℂ) :
    (∑ h ∈ Finset.Icc (-(N : ℤ)) N, weylCorrelation N F h) =
      ((∑ r ∈ Finset.Icc (1 : ℤ) N, F r) *
        conj (∑ r ∈ Finset.Icc (1 : ℤ) N, F r)) / (N : ℂ) := by
  simp only [weylCorrelation, div_eq_mul_inv, ← Finset.sum_mul]
  rw [← interval_pair_difference_sum N (fun h r => F (r + h) * conj (F r))]
  simp only [add_sub_cancel, map_sum, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

/-- The exact normalization is N times the squared complete mean. -/
theorem weyl_mean_square_identity {N : ℕ} (hN : 0 < N) (F : ℤ → ℂ) :
    (N : ℝ) * ‖integerIntervalMean N F‖ ^ 2 =
      ∑ h ∈ Finset.Icc (-(N : ℤ)) N, (weylCorrelation N F h).re := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hN
  rw [← Complex.re_sum, weyl_correlation_sum, Complex.mul_conj,
    ← Complex.ofReal_natCast, ← Complex.ofReal_div, Complex.ofReal_re,
    integerIntervalMean, norm_div, Complex.norm_natCast, ← Complex.sq_norm]
  field_simp

theorem weylCorrelation_norm_le {N : ℕ} (hN : 0 < N) (F : ℤ → ℂ)
    (hF : ∀ r, ‖F r‖ ≤ 1) (h : ℤ) : ‖weylCorrelation N F h‖ ≤ 1 := by
  let : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  rw [weylCorrelation, ← sum_fin_labels]
  have hb (r : Fin N) :
      ‖if (label r : ℤ) + h ∈ Finset.Icc (1 : ℤ) N then
        F ((label r : ℤ) + h) * conj (F (label r)) else 0‖ ≤ 1 := by
    split_ifs
    · rw [norm_mul, Complex.norm_conj]
      exact mul_le_one₀ (hF _) (norm_nonneg _) (hF _)
    · simp
  simpa only [complexUniformMean, Fintype.card_fin] using norm_complexUniformMean_le _ 1 hb

/-- The h=0 contribution is explicitly retained as a possible error of at most one. -/
theorem weyl_nonzero_correlation_lower {N : ℕ} (hN : 0 < N) (F : ℤ → ℂ)
    (hF : ∀ r, ‖F r‖ ≤ 1) :
    (N : ℝ) * ‖integerIntervalMean N F‖ ^ 2 ≤
      1 + ∑ h ∈ horizontalShiftLabels N, ‖weylCorrelation N F h‖ := by
  rw [weyl_mean_square_identity hN]
  have hz : (0 : ℤ) ∈ Finset.Icc (-(N : ℤ)) N := by simp
  rw [← Finset.sum_erase_add _ _ hz]
  apply le_trans (add_le_add
    (Finset.sum_le_sum (fun h _ => Complex.re_le_norm _))
    ((Complex.re_le_norm _).trans (weylCorrelation_norm_le hN F hF 0)))
  simp only [horizontalShiftLabels, add_comm, le_refl]

end GMZP0
