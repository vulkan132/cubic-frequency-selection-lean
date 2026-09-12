import GMZP0.FiniteSchur

/-! Block estimates apply to the actual Gram kernel, including any output masks. -/
noncomputable section
open scoped BigOperators ComplexConjugate
namespace GMZP0

def blockGramKernel {X Y U : Type*} [Fintype U]
    (K : (X × Y) → U → ℂ) (x x' : X) : Y → Y → ℂ :=
  fun y v => gramKernel K (x, y) (x', v)

def KernelEnergyBound {Z U : Type*} [Fintype Z] [Fintype U]
    (K : Z → U → ℂ) (s : ℝ) : Prop :=
  ∀ g : U → ℂ, finiteEnergy (kernelAction K g) ≤ s ^ 2 * finiteEnergy g

/-- Regroup exact Gram energy into whole horizontal blocks before taking norms. -/
theorem kernelAdjoint_energy_blocks {X Y U : Type*} [Fintype X] [Fintype Y] [Fintype U]
    (K : (X × Y) → U → ℂ) (b : X × Y → ℂ) :
    finiteEnergy (kernelAdjoint K b) =
      ∑ x, ∑ x', (finitePairing (kernelAction (blockGramKernel K x x')
        (fun v => b (x', v))) (fun y => b (x, y))).re := by
  have he := congrArg Complex.re (kernelAdjoint_energy_gram K b)
  simp only [Complex.ofReal_re, Complex.re_sum] at he
  rw [he]
  simp only [Fintype.sum_prod_type, blockGramKernel, finitePairing,
    kernelAction, Finset.sum_mul, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]

/-- A symmetric matrix of block bounds controls the complete adjoint energy. -/
theorem kernel_adjoint_energy_of_block_rows {X Y U : Type*}
    [Fintype X] [Fintype Y] [Fintype U]
    (K : (X × Y) → U → ℂ) (a : X → X → ℝ)
    (ha : ∀ x x', 0 ≤ a x x') (hsym : ∀ x x', a x x' = a x' x)
    (hblock : ∀ x x', KernelEnergyBound (blockGramKernel K x x') (a x x'))
    (R : ℝ) (hrow : ∀ x, ∑ x', a x x' ≤ R) (b : X × Y → ℂ) :
    finiteEnergy (kernelAdjoint K b) ≤ R * finiteEnergy b := by
  rw [kernelAdjoint_energy_blocks]
  have hp (x x' : X) :
      (finitePairing (kernelAction (blockGramKernel K x x') (fun v => b (x', v)))
        (fun y => b (x, y))).re ≤
      a x x' * Real.sqrt (finiteEnergy (fun y => b (x, y))) *
        Real.sqrt (finiteEnergy (fun v => b (x', v))) :=
    (Complex.re_le_norm _).trans (kernel_pairing_bound_of_energy _ _ (ha x x')
      (hblock x x') _ _)
  have h := (Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun x' _ => hp x x'))).trans
    (symmetric_nonnegative_form_bound a ha hsym R hrow
      (fun x => Real.sqrt (finiteEnergy (fun y => b (x, y)))))
  have hsq (x : X) := Real.sq_sqrt (finiteEnergy_nonneg (fun y => b (x, y)))
  simp_rw [hsq] at h
  simpa only [finiteEnergy, Fintype.sum_prod_type] using h

/-- The block Schur estimate for the original finite operator. -/
theorem kernel_action_energy_of_block_rows {X Y U : Type*}
    [Fintype X] [Fintype Y] [Fintype U]
    (K : (X × Y) → U → ℂ) (a : X → X → ℝ)
    (ha : ∀ x x', 0 ≤ a x x') (hsym : ∀ x x', a x x' = a x' x)
    (hblock : ∀ x x', KernelEnergyBound (blockGramKernel K x x') (a x x'))
    (R : ℝ) (hR : 0 ≤ R) (hrow : ∀ x, ∑ x', a x x' ≤ R) (g : U → ℂ) :
    finiteEnergy (kernelAction K g) ≤ R * finiteEnergy g :=
  kernel_action_energy_of_adjoint K R hR
    (kernel_adjoint_energy_of_block_rows K a ha hsym hblock R hrow) g

/-- The adjoint of a Gram block is the block with its two horizontal indices exchanged. -/
theorem blockGramKernel_adjoint {X Y U : Type*} [Fintype Y] [Fintype U]
    (K : (X × Y) → U → ℂ) (x x' : X) (g : Y → ℂ) :
    kernelAdjoint (blockGramKernel K x x') g = kernelAction (blockGramKernel K x' x) g := by
  funext y
  simp only [kernelAdjoint, kernelAction, blockGramKernel, gramKernel_conjugate]

/-- The actual block energy-bound predicate is symmetric in horizontal indices. -/
theorem blockGramKernel_energy_bound_symm {X Y U : Type*} [Fintype Y] [Fintype U]
    (K : (X × Y) → U → ℂ) (s : ℝ) (x x' : X) :
    KernelEnergyBound (blockGramKernel K x x') s ↔
      KernelEnergyBound (blockGramKernel K x' x) s := by
  constructor <;> intro h g
  · simpa only [blockGramKernel_adjoint] using
      kernel_adjoint_energy_of_action _ (s ^ 2) (sq_nonneg s) h g
  · simpa only [blockGramKernel_adjoint] using
      kernel_adjoint_energy_of_action _ (s ^ 2) (sq_nonneg s) h g

/-- The masked Gram kernel retains both pointwise multipliers exactly. -/
theorem outputMaskedKernel_gram {Z U : Type*} [Fintype U]
    (K : Z → U → ℂ) (m : Z → ℂ) (z w : Z) :
    gramKernel (outputMaskedKernel K m) z w =
      m z * gramKernel K z w * conj (m w) := by
  simp only [gramKernel, outputMaskedKernel, map_mul, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro u _
  ring

/-- A masked block acts through one input and one output pointwise multiplier. -/
theorem blockGramKernel_masked_action {X Y U : Type*} [Fintype Y] [Fintype U]
    (K : (X × Y) → U → ℂ) (m : X × Y → ℂ) (x x' : X) (g : Y → ℂ) (y : Y) :
    kernelAction (blockGramKernel (outputMaskedKernel K m) x x') g y =
      m (x, y) * kernelAction (blockGramKernel K x x') (fun v => conj (m (x', v)) * g v) y := by
  simp only [kernelAction, blockGramKernel, outputMaskedKernel_gram, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  ring

/-- Arbitrary contractive output masks preserve each whole Gram block bound. -/
theorem blockGramKernel_mask_bound {X Y U : Type*} [Fintype Y] [Fintype U]
    (K : (X × Y) → U → ℂ) (m : X × Y → ℂ) (hm : ∀ z, ‖m z‖ ≤ 1)
    (x x' : X) (s : ℝ) (h : KernelEnergyBound (blockGramKernel K x x') s) :
    KernelEnergyBound (blockGramKernel (outputMaskedKernel K m) x x') s := by
  intro g
  have he : kernelAction (blockGramKernel (outputMaskedKernel K m) x x') g =
      fun y => m (x, y) * kernelAction (blockGramKernel K x x')
        (fun v => conj (m (x', v)) * g v) y := funext (blockGramKernel_masked_action K m x x' g)
  rw [he]
  exact (finiteEnergy_mask_le _ _ (fun y => hm (x, y))).trans
    ((h _).trans (mul_le_mul_of_nonneg_left
      (finiteEnergy_mask_le _ g (fun v => by simpa using hm (x', v))) (sq_nonneg s)))

end GMZP0
