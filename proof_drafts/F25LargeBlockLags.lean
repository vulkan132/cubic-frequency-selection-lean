import GMZP0.WideLagBounds
import GMZP0.HorizontalShiftReindexing

/-! A genuinely large original compressed block forces many complete nonzero lag sums.
The source root may depend on the lag. All constants precede the original data. -/
noncomputable section
open scoped BigOperators
namespace GMZP0

/-- The nonzero integer interval sum is exactly the erased-zero sum. -/
theorem wide_nonzero_lag_sum (N : ℕ) (M : ℤ → ℝ) :
    (∑ k ∈ Finset.Icc (-(N : ℤ)) N, if k ≠ 0 then M k else 0) =
      ∑ k ∈ horizontalShiftLabels N, M k := by
  classical
  have he : horizontalShiftLabels N = (Finset.Icc (-(N : ℤ)) N).filter (fun k => k ≠ 0) := by
    ext k
    simp only [horizontalShiftLabels, Finset.mem_erase, Finset.mem_filter]
    exact and_comm
  rw [he, Finset.sum_filter]

/-- Every lag has an actual maximizing original source; roots are allowed to vary with k. -/
theorem wide_lag_maximizing_roots {N : ℕ} (hN : 0 < N)
    (P : Fin N → ℤ → Frequency) (x x' : Fin N) :
    ∃ root : ℤ → Fin (N ^ 2), ∀ k (y : Fin (N ^ 2)),
      ‖wideLagSum P x x' (label y) k‖ ≤ ‖wideLagSum P x x' (label (root k)) k‖ := by
  classical
  have hn : (Finset.univ : Finset (Fin (N ^ 2))).Nonempty :=
    ⟨⟨0, pow_pos hN 2⟩, Finset.mem_univ _⟩
  have hm (k : ℤ) := Finset.exists_max_image Finset.univ
    (fun y : Fin (N ^ 2) => ‖wideLagSum P x x' (label y) k‖) hn
  choose root _ hroot using hm
  exact ⟨root, fun k y => hroot k y (Finset.mem_univ _)⟩

/-- Failure of an actual compressed-block bound gives a lower bound on complete lag envelopes. -/
theorem masked_large_block_lag_sum_lower {N : ℕ} (hN : 0 < N)
    (P : Fin N → ℤ → Frequency) (p : Base N → Frequency) (hP : WideProfileAgreement N P p)
    (m : Base N → ℂ) (hm : ∀ z, ‖m z‖ ≤ 1) (x x' : Fin N) (hx : x ≠ x')
    (v : ℝ) (M : ℤ → ℝ) (hM0 : ∀ k, 0 ≤ M k)
    (hM : ∀ y : Fin (N ^ 2), ∀ k ∈ Finset.Icc (-(N : ℤ)) N, k ≠ 0 →
      ‖wideLagSum P x x' (label y) k‖ ≤ M k)
    (hlarge : ¬ KernelEnergyBound (blockGramKernel (outputMaskedKernel (responseKernel N p) m) x x')
      (v / N)) :
    v ^ 2 * (N : ℝ) ^ 2 < (N : ℝ) + ∑ k ∈ horizontalShiftLabels N, M k := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hn0 : (N : ℝ) ≠ 0 := ne_of_gt hn
  have hb : (v / N) ^ 2 <
      ((N : ℝ) + ∑ k ∈ Finset.Icc (-(N : ℤ)) N, if k ≠ 0 then M k else 0) / (N : ℝ) ^ 4 := by
    by_contra! hc
    apply hlarge
    apply masked_original_block_bound_of_wide P p hP m hm x x' hx
    intro g
    exact (wide_block_energy_of_lag_bounds P x x' M hM0 hM g).trans
      (mul_le_mul_of_nonneg_right hc (finiteEnergy_nonneg g))
  have he : (v / N) ^ 2 * (N : ℝ) ^ 4 = v ^ 2 * (N : ℝ) ^ 2 := by
    field_simp
  rw [lt_div_iff₀ (pow_pos hn 4), he, wide_nonzero_lag_sum] at hb
  exact hb

/-- A bounded finite sum controls the number of entries at a given absolute threshold. -/
theorem sum_le_large_card_scaled {I : Type*} (s : Finset I) (M : I → ℝ)
    (B τ : ℝ) (hτ : 0 ≤ τ) (hM : ∀ i ∈ s, M i ≤ B) :
    (∑ i ∈ s, M i) ≤ ((s.filter (fun i => τ ≤ M i)).card : ℝ) * B + (s.card : ℝ) * τ := by
  classical
  calc
    _ ≤ ∑ i ∈ s, ((if τ ≤ M i then B else 0) + τ) := by
      apply Finset.sum_le_sum
      intro i hi
      split_ifs with h
      · linarith [hM i hi]
      · have := le_of_lt (lt_of_not_ge h)
        linarith
    _ = _ := by simp [Finset.sum_add_distrib, ← Finset.sum_filter]

/-- The N term is absorbed only after the explicit scale threshold N*v^2 >= 2. -/
theorem many_large_lag_envelopes {N : ℕ} (hN : 0 < N) (M : ℤ → ℝ) (v : ℝ)
    (hM : ∀ k ∈ horizontalShiftLabels N, M k ≤ N)
    (hscale : 2 ≤ (N : ℝ) * v ^ 2)
    (hlarge : v ^ 2 * (N : ℝ) ^ 2 < (N : ℝ) + ∑ k ∈ horizontalShiftLabels N, M k) :
    (N : ℝ) * v ^ 2 / 4 ≤
      ((horizontalShiftLabels N).filter (fun k => (v ^ 2 / 8) * N ≤ M k)).card := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hs := sum_le_large_card_scaled (horizontalShiftLabels N) M N ((v ^ 2 / 8) * N)
    (by positivity) hM
  rw [horizontalShiftLabels_card, Nat.cast_mul, Nat.cast_ofNat] at hs
  have hscaleN := mul_le_mul_of_nonneg_right hscale hn.le
  have hcount : (N : ℝ) * ((N : ℝ) * v ^ 2 / 4) ≤
      (N : ℝ) * (((horizontalShiftLabels N).filter (fun k => (v ^ 2 / 8) * N ≤ M k)).card : ℝ) := by
    nlinarith
  exact (mul_le_mul_iff_right₀ hn).mp hcount

/-- A large compressed original block produces many actual nonzero lags and original roots. -/
theorem masked_large_block_many_lags {N : ℕ} (hN : 0 < N)
    (P : Fin N → ℤ → Frequency) (p : Base N → Frequency) (hP : WideProfileAgreement N P p)
    (m : Base N → ℂ) (hm : ∀ z, ‖m z‖ ≤ 1) (x x' : Fin N) (hx : x ≠ x')
    (v : ℝ) (hv : 0 < v) (hscale : 2 ≤ (N : ℝ) * v ^ 2)
    (hlarge : ¬ KernelEnergyBound (blockGramKernel (outputMaskedKernel (responseKernel N p) m) x x')
      (v / N)) :
    ∃ K : Finset ℤ, ∃ root : ℤ → Fin (N ^ 2),
      (N : ℝ) * v ^ 2 / 4 ≤ K.card ∧
      ∀ k ∈ K, k ≠ 0 ∧ |k| < N ∧
        (v ^ 2 / 8) * N ≤ ‖wideLagSum P x x' (label (root k)) k‖ := by
  classical
  obtain ⟨root, hr⟩ := wide_lag_maximizing_roots hN P x x'
  let M : ℤ → ℝ := fun k => ‖wideLagSum P x x' (label (root k)) k‖
  have hlo := masked_large_block_lag_sum_lower hN P p hP m hm x x' hx v M
    (fun _ => norm_nonneg _) (fun y k _ _ => hr k y) hlarge
  have hcard := many_large_lag_envelopes hN M v
    (fun k _ => wideLagSum_norm_le P x x' (label (root k)) k) hscale hlo
  refine ⟨(horizontalShiftLabels N).filter (fun k => (v ^ 2 / 8) * N ≤ M k), root, hcard, ?_⟩
  intro k hk
  obtain ⟨hk, hkm⟩ := Finset.mem_filter.mp hk
  have hk0 := (Finset.mem_erase.mp hk).1
  refine ⟨hk0, ?_, hkm⟩
  by_contra! hbad
  have hempty := lagLabels_empty_of_large_lag N (horizontalGap x x') k hbad
  have hz : M k = 0 := by simp [M, wideLagSum, hempty]
  rw [hz] at hkm
  have : 0 < (v ^ 2 / 8) * (N : ℝ) := by positivity
  linarith

/-- The successful-lag proportion and N threshold depend only on v, before profiles, masks and points. -/
theorem uniform_masked_large_block_many_lags (v : ℝ) (hv : 0 < v) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, 0 < N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ P : Fin N → ℤ → Frequency, ∀ p : Base N → Frequency,
      WideProfileAgreement N P p → ∀ m : Base N → ℂ, (∀ z, ‖m z‖ ≤ 1) →
      ∀ x x' : Fin N, x ≠ x' →
      (¬ KernelEnergyBound (blockGramKernel (outputMaskedKernel (responseKernel N p) m) x x') (v / N)) →
      ∃ K : Finset ℤ, ∃ root : ℤ → Fin (N ^ 2), c * N ≤ K.card ∧
        ∀ k ∈ K, k ≠ 0 ∧ |k| < N ∧ c * N ≤ ‖wideLagSum P x x' (label (root k)) k‖ := by
  obtain ⟨B, hB⟩ := exists_nat_gt (2 / v ^ 2)
  refine ⟨v ^ 2 / 8, by positivity, B + 1, by omega, ?_⟩
  intro N hN P p hP m hm x x' hx hlarge
  have hn : 0 < N := by omega
  have hBN : (B : ℝ) ≤ N := by exact_mod_cast (show B ≤ N by omega)
  have hscale : 2 ≤ (N : ℝ) * v ^ 2 :=
    ((div_lt_iff₀ (sq_pos_of_pos hv)).mp (hB.trans_le hBN)).le
  obtain ⟨K, root, hcard, hK⟩ := masked_large_block_many_lags hn P p hP m hm x x' hx v hv hscale hlarge
  refine ⟨K, root, ?_, hK⟩
  have : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  nlinarith [sq_nonneg v]

end GMZP0
