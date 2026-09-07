import GMZP0.SingleBlockFormula

/-! An explicit bijection from original Fin labels to the integer interval I_h. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

theorem oneBasedIndex_of_label {n : ℕ} (r : Fin n)
    (hr0 : 1 ≤ (label r : ℤ)) (hrn : (label r : ℤ) ≤ n) :
    oneBasedIndex n (label r) hr0 hrn = r := by
  apply Fin.ext
  change ((label r : ℤ) - 1).toNat = r.val
  simp [label]

def blockLabelEquiv (N : ℕ) (h : ℤ) : blockFinLabels N h ≃ blockLabels N h where
  toFun r := ⟨(label r.val : ℤ), (blockFinLabels_membership N h r.val).1 r.property⟩
  invFun q := ⟨oneBasedIndex N q.val ((mem_blockLabels_iff N h q.val).1 q.property).1.1
      ((mem_blockLabels_iff N h q.val).1 q.property).1.2, by
    apply (blockFinLabels_membership N h _).2
    rw [oneBasedIndex_label]
    exact q.property⟩
  left_inv r := by
    apply Subtype.ext
    exact oneBasedIndex_of_label r.val
      (integer_label_bounds r.val).1 (integer_label_bounds r.val).2
  right_inv q := by
    apply Subtype.ext
    exact oneBasedIndex_label N q.val
      ((mem_blockLabels_iff N h q.val).1 q.property).1.1
      ((mem_blockLabels_iff N h q.val).1 q.property).1.2

theorem blockLabelEquiv_symm_value (N : ℕ) (h : ℤ) (q : blockLabels N h) :
    (label ((blockLabelEquiv N h).symm q).val : ℤ) = q.val := by
  exact oneBasedIndex_label N q.val
    ((mem_blockLabels_iff N h q.val).1 q.property).1.1
    ((mem_blockLabels_iff N h q.val).1 q.property).1.2

/-- The complete original block is now indexed by precisely the paper's integer I_h. -/
theorem horizontalBlock_action_integer_labels {N : ℕ} (H : ℕ) (p : Base N → Frequency)
    (x x' : Fin N) (hx : x ≠ x') (y : Fin (N ^ 2))
    (hy : SafeVertical (N : ℤ) H ((y.val : ℤ) + 1)) (hh : |horizontalGap x x'| ≤ H)
    (hHN : H ≤ N) (g : Fin (N ^ 2) → ℂ) :
    kernelAction (horizontalKernel N p x x') g y =
      ∑ q : blockLabels N (horizontalGap x x'),
        (circleCharacter (q.val ^ 3 • p (x, y) - (q.val - horizontalGap x x') ^ 3 •
          p (x', blockTarget H y hy (horizontalGap x x') hh hHN
            ((blockLabelEquiv N (horizontalGap x x')).symm q).val)) / (N : ℂ) ^ 2) *
        g (blockTarget H y hy (horizontalGap x x') hh hHN
          ((blockLabelEquiv N (horizontalGap x x')).symm q).val) := by
  rw [horizontalBlock_action_labels H p x x' hx y hy hh hHN]
  let F : blockFinLabels N (horizontalGap x x') → ℂ := fun r =>
    blockCoefficient H p x x' y hy hh hHN r *
      g (blockTarget H y hy (horizontalGap x x') hh hHN r.val)
  have hs := Equiv.sum_comp (blockLabelEquiv N (horizontalGap x x')).symm F
  change (∑ r, F r) = _
  rw [← hs]
  apply Finset.sum_congr rfl
  intro q _
  dsimp only [F]
  rw [blockCoefficient_character, blockLabelEquiv_symm_value]

end GMZP0
