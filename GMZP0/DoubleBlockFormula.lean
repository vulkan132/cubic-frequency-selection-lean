import GMZP0.LagSources
import GMZP0.DoubleKernelPhase

/-! Complete two-label reindexing of a horizontal Gram row and its off-diagonal part. -/

noncomputable section
open scoped BigOperators ComplexConjugate
namespace GMZP0

/-- A whole original column can be summed through its injective family of lag sources. -/
theorem horizontalKernel_lag_weighted_sum {N : ℕ} (H : ℕ) (p : Base N → Frequency)
    (x x' : Fin N) (hx : x ≠ x') (y : Fin (N ^ 2))
    (hy : SafeVertical (N : ℤ) H ((y.val : ℤ) + 1)) (hh : |horizontalGap x x'| ≤ H)
    (hHN : H ≤ N) (r : Fin N) (g : Fin (N ^ 2) → ℂ) :
    (∑ t, conj (horizontalKernel N p x x' t
      (blockTarget H y hy (horizontalGap x x') hh hHN r)) * g t) =
    ∑ s : blockFinLabels N (horizontalGap x x'),
      conj (horizontalKernel N p x x'
        (lagSource H y hy (horizontalGap x x') hh r s.val)
        (blockTarget H y hy (horizontalGap x x') hh hHN r)) *
      g (lagSource H y hy (horizontalGap x x') hh r s.val) := by
  classical
  let T : blockFinLabels N (horizontalGap x x') → Fin (N ^ 2) :=
    fun s => lagSource H y hy (horizontalGap x x') hh r s.val
  have hi : Function.Injective T := by
    intro s u he
    exact Subtype.ext (lagSource_injective H y hy (horizontalGap x x') hh
      (horizontalGap_ne_zero x x' hx) r he)
  symm
  apply Fintype.sum_of_injective T hi
  · intro t ht
    have hn : ∀ s u : Fin N, endpointIndex (x, t) s ≠
        endpointIndex (x', blockTarget H y hy (horizontalGap x x') hh hHN r) u := by
      intro s u he
      obtain ⟨hs, hts⟩ := collision_in_lagSources H x x' y t hy hh hHN r s u he
      exact ht ⟨⟨s, hs⟩, hts⟩
    rw [horizontalKernel_no_collision p x x' t _ hn, map_zero, zero_mul]
  · intro s
    rfl

/-- Exact complete Gram action; both original labels range independently over I_h. -/
theorem horizontalGram_action_labels {N : ℕ} (H : ℕ) (p : Base N → Frequency)
    (x x' : Fin N) (hx : x ≠ x') (y : Fin (N ^ 2))
    (hy : SafeVertical (N : ℤ) H ((y.val : ℤ) + 1)) (hh : |horizontalGap x x'| ≤ H)
    (hHN : H ≤ N) (g : Fin (N ^ 2) → ℂ) :
    kernelAction (gramKernel (horizontalKernel N p x x')) g y =
      ∑ r : blockFinLabels N (horizontalGap x x'),
      ∑ s : blockFinLabels N (horizontalGap x x'),
        horizontalKernel N p x x' y (blockTarget H y hy (horizontalGap x x') hh hHN r.val) *
          conj (horizontalKernel N p x x'
            (lagSource H y hy (horizontalGap x x') hh r.val s.val)
            (blockTarget H y hy (horizontalGap x x') hh hHN r.val)) *
          g (lagSource H y hy (horizontalGap x x') hh r.val s.val) := by
  rw [← kernel_comp_adjoint, horizontalBlock_action_labels H p x x' hx y hy hh hHN]
  apply Finset.sum_congr rfl
  intro r _
  rw [kernelAdjoint, horizontalKernel_lag_weighted_sum H p x x' hx y hy hh hHN]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [horizontalKernel_of_collision p x x' hx y _ r.val
    (shiftedBlockLabel (horizontalGap x x') r) (blockTarget_collision H x x' y hy hh hHN r)]
  unfold blockCoefficient
  ring

/-- Removing the vertical diagonal removes exactly equal label pairs; all other terms remain. -/
theorem horizontalGram_offDiagonal_labels {N : ℕ} (H : ℕ) (p : Base N → Frequency)
    (x x' : Fin N) (hx : x ≠ x') (y : Fin (N ^ 2))
    (hy : SafeVertical (N : ℤ) H ((y.val : ℤ) + 1)) (hh : |horizontalGap x x'| ≤ H)
    (hHN : H ≤ N) (b : Fin (N ^ 2) → ℂ) :
    (∑ t : Fin (N ^ 2), if t ≠ y then
      (gramKernel (horizontalKernel N p x x') y t * b t * conj (b y)).re else 0) =
    ∑ r : blockFinLabels N (horizontalGap x x'),
    ∑ s : blockFinLabels N (horizontalGap x x'), if s ≠ r then
      (horizontalKernel N p x x' y (blockTarget H y hy (horizontalGap x x') hh hHN r.val) *
        conj (horizontalKernel N p x x'
          (lagSource H y hy (horizontalGap x x') hh r.val s.val)
          (blockTarget H y hy (horizontalGap x x') hh hHN r.val)) *
        b (lagSource H y hy (horizontalGap x x') hh r.val s.val) * conj (b y)).re else 0 := by
  classical
  have he := horizontalGram_action_labels H p x x' hx y hy hh hHN (fun t => if t ≠ y then b t else 0)
  have he' := congrArg (fun z : ℂ => (z * conj (b y)).re) he
  simpa only [kernelAction, mul_ite, ite_mul, mul_zero, zero_mul,
    Finset.sum_mul, Complex.re_sum, apply_ite, Complex.zero_re, ne_eq,
    lagSource_eq_self_iff H y hy (horizontalGap x x') hh (horizontalGap_ne_zero x x' hx),
    Subtype.val_inj] using he'

/-- The complete signed off-diagonal row has precisely the original double phase and weights. -/
theorem horizontalGram_offDiagonal_original_phase {N : ℕ} (H : ℕ) (p : Base N → Frequency)
    (σ : Base N → ℝ) (lam : Base N → ℂ)
    (x x' : Fin N) (hx : x ≠ x') (y : Fin (N ^ 2))
    (hy : SafeVertical (N : ℤ) H ((y.val : ℤ) + 1)) (hh : |horizontalGap x x'| ≤ H)
    (hHN : H ≤ N) :
    (∑ t : Fin (N ^ 2), if t ≠ y then
      (gramKernel (horizontalKernel N p x x') y t * alignedWeightVector σ lam (x, t) *
        conj (alignedWeightVector σ lam (x, y))).re else 0) =
    ∑ r : blockFinLabels N (horizontalGap x x'),
    ∑ s : blockFinLabels N (horizontalGap x x'), if s ≠ r then
      (σ (x, y) * σ (x, lagSource H y hy (horizontalGap x x') hh r.val s.val) *
        (lam (x, y) * conj (lam (x, lagSource H y hy (horizontalGap x x') hh r.val s.val)) *
          circleCharacter (doublePhaseCoefficient (p (x, y))
            (p (x, lagSource H y hy (horizontalGap x x') hh r.val s.val))
            (p (x', blockTarget H y hy (horizontalGap x x') hh hHN r.val))
            (horizontalGap x x') ((label r.val : ℤ) - (label s.val : ℤ)) (label s.val))).re) /
        (N : ℝ) ^ 4 else 0 := by
  rw [horizontalGram_offDiagonal_labels H p x x' hx y hy hh hHN]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  split_ifs
  · exact double_kernel_original_weighted_phase p σ lam x x' hx y _ _ r.val
      (shiftedBlockLabel (horizontalGap x x') r) s.val (shiftedBlockLabel (horizontalGap x x') s)
      (blockTarget_collision H x x' y hy hh hHN r) (lagSource_collision H x x' y hy hh hHN r.val s)
  · rfl

end GMZP0
