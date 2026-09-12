import GMZP0.WideVertical

/-! Exact finite enlargement and compression for every original non-diagonal horizontal block. -/
noncomputable section
open scoped BigOperators ComplexConjugate
namespace GMZP0

/-- Zero extension of the original vertical input into the widened interval. -/
def wideZeroExtension {N : ℕ} (g : Fin (N ^ 2) → ℂ) (u : WideVertical N) : ℂ :=
  ∑ v, if wideVerticalEmbed v = u then g v else 0

/-- Zero extension agrees with the same original input at every embedded point. -/
theorem wideZeroExtension_original {N : ℕ} (g : Fin (N ^ 2) → ℂ) (v : Fin (N ^ 2)) :
    wideZeroExtension g (wideVerticalEmbed v) = g v := by
  simp [wideZeroExtension, wideVerticalEmbed_injective.eq_iff]

/-- No nonoriginal input value is introduced by zero extension. -/
theorem wideZeroExtension_outside {N : ℕ} (g : Fin (N ^ 2) → ℂ) (u : WideVertical N)
    (hu : u ∉ Set.range wideVerticalEmbed) : wideZeroExtension g u = 0 := by
  have hn (v : Fin (N ^ 2)) : wideVerticalEmbed v ≠ u := fun hv => hu ⟨v, hv⟩
  simp [wideZeroExtension, hn]

/-- Zero extension preserves the complete original vertical input energy exactly. -/
theorem wideZeroExtension_energy {N : ℕ} (g : Fin (N ^ 2) → ℂ) :
    finiteEnergy (wideZeroExtension g) = finiteEnergy g := by
  symm
  apply Fintype.sum_of_injective wideVerticalEmbed wideVerticalEmbed_injective
  · intro u hu
    simp [wideZeroExtension_outside g u hu]
  · intro v
    simp [wideZeroExtension_original]

/-- Any widened matrix on the zero extension acts through precisely its original columns. -/
theorem kernelAction_wideZeroExtension {N : ℕ} {Z : Type*}
    (K : Z → WideVertical N → ℂ) (g : Fin (N ^ 2) → ℂ) (z : Z) :
    kernelAction K (wideZeroExtension g) z = ∑ v, K z (wideVerticalEmbed v) * g v := by
  simp only [kernelAction, wideZeroExtension, Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  simp

/-- Agreement is required only on original points; no polynomial property of an arbitrary extension is asserted. -/
def WideProfileAgreement (N : ℕ) (P : Fin N → ℤ → Frequency) (p : Base N → Frequency) : Prop :=
  ∀ x y, P x (label y) = p (x, y)

def wideBlockCoefficient {N : ℕ} (P : Fin N → ℤ → Frequency) (x x' : Fin N)
    (y : Fin (N ^ 2)) (r : blockFinLabels N (horizontalGap x x')) : ℂ :=
  cubicPhase (P x (label y)) r.val *
    conj (cubicPhase (P x' (wideVerticalCoordinate (wideBlockTarget y (horizontalGap x x') r)))
      (shiftedBlockLabel (horizontalGap x x') r)) / (N : ℂ) ^ 2

/-- Every valid original block label contributes at its actual enlarged target. -/
def wideHorizontalKernel {N : ℕ} (P : Fin N → ℤ → Frequency) (x x' : Fin N)
    (y : Fin (N ^ 2)) (u : WideVertical N) : ℂ :=
  ∑ r : blockFinLabels N (horizontalGap x x'),
    if wideBlockTarget y (horizontalGap x x') r = u then wideBlockCoefficient P x x' y r else 0

/-- At a valid target the nonparallel widened kernel consists of exactly its one label contribution. -/
theorem wideHorizontalKernel_at_target {N : ℕ} (P : Fin N → ℤ → Frequency)
    (x x' : Fin N) (hx : x ≠ x') (y : Fin (N ^ 2)) (r : blockFinLabels N (horizontalGap x x')) :
    wideHorizontalKernel P x x' y (wideBlockTarget y (horizontalGap x x') r) =
      wideBlockCoefficient P x x' y r := by
  simp [wideHorizontalKernel, (wideBlockTarget_injective y (horizontalGap x x')
    (horizontalGap_ne_zero x x' hx)).eq_iff]

/-- Without a label reaching a target, the widened kernel is exactly zero. -/
theorem wideHorizontalKernel_no_target {N : ℕ} (P : Fin N → ℤ → Frequency)
    (x x' : Fin N) (y : Fin (N ^ 2)) (u : WideVertical N)
    (hu : ∀ r : blockFinLabels N (horizontalGap x x'), wideBlockTarget y (horizontalGap x x') r ≠ u) :
    wideHorizontalKernel P x x' y u = 0 := by
  simp [wideHorizontalKernel, hu]

/-- Every original collision appears as an actual complete label of the widened block. -/
theorem original_collision_wide_label {N : ℕ} (x x' : Fin N) (y v : Fin (N ^ 2))
    (r s : Fin N) (he : endpointIndex (x, y) r = endpointIndex (x', v) s) :
    ∃ t : blockFinLabels N (horizontalGap x x'), t.val = r ∧
      shiftedBlockLabel (horizontalGap x x') t = s ∧
      wideBlockTarget y (horizontalGap x x') t = wideVerticalEmbed v := by
  have hg := (endpointIndex_collision_iff (x, y) (x', v) r s).mp he
  have hs : (label s : ℤ) = (label r : ℤ) - horizontalGap x x' := by
    simpa only [basePoint, add_sub_add_right_eq_sub, horizontalGap] using hg.1
  have hr : r ∈ blockFinLabels N (horizontalGap x x') := by
    simp only [blockFinLabels, Finset.mem_filter, Finset.mem_univ, true_and, ← hs]
    exact integer_label_bounds s
  let t : blockFinLabels N (horizontalGap x x') := ⟨r, hr⟩
  have ht : shiftedBlockLabel (horizontalGap x x') t = s := by
    have h : (label (shiftedBlockLabel (horizontalGap x x') t) : ℤ) = (label s : ℤ) :=
      (shiftedBlockLabel_value (horizontalGap x x') t).trans hs.symm
    apply Fin.ext
    simp only [label, Nat.cast_add, Nat.cast_one] at h
    omega
  exact ⟨t, rfl, ht, (wideBlockTarget_original_collision x x' y v t).2 (by simpa only [ht] using he)⟩

/-- Restriction of the widened kernel to original columns is exactly the original Gram block. -/
theorem wideHorizontalKernel_original {N : ℕ} (P : Fin N → ℤ → Frequency)
    (p : Base N → Frequency) (hP : WideProfileAgreement N P p)
    (x x' : Fin N) (hx : x ≠ x') (y v : Fin (N ^ 2)) :
    wideHorizontalKernel P x x' y (wideVerticalEmbed v) = horizontalKernel N p x x' y v := by
  classical
  by_cases he : ∃ r : blockFinLabels N (horizontalGap x x'),
      wideBlockTarget y (horizontalGap x x') r = wideVerticalEmbed v
  · obtain ⟨r, hr⟩ := he
    have hc := (wideBlockTarget_original_collision x x' y v r).1 hr
    rw [← hr, wideHorizontalKernel_at_target P x x' hx y r]
    rw [horizontalKernel_of_collision p x x' hx y v r.val (shiftedBlockLabel (horizontalGap x x') r) hc]
    simp only [wideBlockCoefficient, hr, wideVerticalEmbed_coordinate]
    rw [hP x y, hP x' v]
  · rw [wideHorizontalKernel_no_target P x x' y (wideVerticalEmbed v)
      (fun r hr => he ⟨r, hr⟩)]
    symm
    apply horizontalKernel_no_collision
    intro r s hrs
    obtain ⟨t, _, _, ht⟩ := original_collision_wide_label x x' y v r s hrs
    exact he ⟨t, ht⟩

/-- The exact original block action is recovered at every source, including the boundary. -/
theorem wideHorizontalKernel_original_action {N : ℕ} (P : Fin N → ℤ → Frequency)
    (p : Base N → Frequency) (hP : WideProfileAgreement N P p)
    (x x' : Fin N) (hx : x ≠ x') (g : Fin (N ^ 2) → ℂ) :
    kernelAction (wideHorizontalKernel P x x') (wideZeroExtension g) =
      kernelAction (horizontalKernel N p x x') g := by
  funext y
  rw [kernelAction_wideZeroExtension]
  simp only [wideHorizontalKernel_original P p hP x x' hx, kernelAction]

/-- A widened-block estimate bounds the original block without comparing truncated phase sums. -/
theorem original_block_bound_of_wide {N : ℕ} (P : Fin N → ℤ → Frequency)
    (p : Base N → Frequency) (hP : WideProfileAgreement N P p)
    (x x' : Fin N) (hx : x ≠ x') (s : ℝ)
    (hwide : KernelEnergyBound (wideHorizontalKernel P x x') s) :
    KernelEnergyBound (horizontalKernel N p x x') s := by
  intro g
  simpa only [wideHorizontalKernel_original_action P p hP x x' hx, wideZeroExtension_energy] using
    hwide (wideZeroExtension g)

/-- Arbitrary pointwise compression of the original block is also controlled by the widened bound. -/
theorem masked_original_block_bound_of_wide {N : ℕ} (P : Fin N → ℤ → Frequency)
    (p : Base N → Frequency) (hP : WideProfileAgreement N P p)
    (m : Base N → ℂ) (hm : ∀ z, ‖m z‖ ≤ 1)
    (x x' : Fin N) (hx : x ≠ x') (s : ℝ)
    (hwide : KernelEnergyBound (wideHorizontalKernel P x x') s) :
    KernelEnergyBound (blockGramKernel (outputMaskedKernel (responseKernel N p) m) x x') s :=
  blockGramKernel_mask_bound (responseKernel N p) m hm x x' s
    (original_block_bound_of_wide P p hP x x' hx s hwide)

end GMZP0
