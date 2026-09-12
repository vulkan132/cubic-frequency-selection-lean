import GMZP0.GramEnergy
import GMZP0.FiniteEnergyPermutation

/-! Finite Schur estimates, exact adjoint transfer, and arbitrary contractive output masks.
All estimates are proved from finite sums; no external analytic input is used. -/

noncomputable section
open scoped BigOperators ComplexConjugate
namespace GMZP0

/-- A nonnegative symmetric matrix is bounded by its largest row sum. -/
theorem symmetric_nonnegative_form_bound {I : Type*} [Fintype I]
    (a : I → I → ℝ) (ha : ∀ i j, 0 ≤ a i j) (hsym : ∀ i j, a i j = a j i)
    (R : ℝ) (hrow : ∀ i, ∑ j, a i j ≤ R) (u : I → ℝ) :
    (∑ i, ∑ j, a i j * u i * u j) ≤ R * ∑ i, u i ^ 2 := by
  have hpoint (i j : I) : 2 * (a i j * u i * u j) ≤ a i j * (u i ^ 2 + u j ^ 2) := by
    nlinarith [mul_nonneg (ha i j) (sq_nonneg (u i - u j))]
  have hsum : 2 * (∑ i, ∑ j, a i j * u i * u j) ≤ ∑ i, ∑ j, a i j * (u i ^ 2 + u j ^ 2) := by
    simp only [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hpoint i j))
  have hfirst : (∑ i, ∑ j, a i j * u i ^ 2) ≤ R * ∑ i, u i ^ 2 := by
    calc
      _ = ∑ i, (∑ j, a i j) * u i ^ 2 := by simp only [Finset.sum_mul]
      _ ≤ ∑ i, R * u i ^ 2 := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hrow i) (sq_nonneg _))
      _ = _ := (Finset.mul_sum ..).symm
  have hsecond : (∑ i, ∑ j, a i j * u j ^ 2) = ∑ i, ∑ j, a i j * u i ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hsym j i]
  simp only [mul_add, Finset.sum_add_distrib] at hsum
  rw [hsecond] at hsum
  linarith

/-- An adjoint energy bound transfers to the original finite operator. -/
theorem kernel_action_energy_of_adjoint {Z U : Type*} [Fintype Z] [Fintype U]
    (K : Z → U → ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hadjoint : ∀ b : Z → ℂ, finiteEnergy (kernelAdjoint K b) ≤ R * finiteEnergy b)
    (g : U → ℂ) : finiteEnergy (kernelAction K g) ≤ R * finiteEnergy g := by
  have hcs := finitePairing_norm_sq_le g (kernelAdjoint K (kernelAction K g))
  rw [← kernel_adjoint_identity, finitePairing_self, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (finiteEnergy_nonneg _)] at hcs
  have he := mul_le_mul_of_nonneg_left (hadjoint (kernelAction K g)) (finiteEnergy_nonneg g)
  have hnonneg := mul_nonneg hR (finiteEnergy_nonneg g)
  nlinarith [finiteEnergy_nonneg (kernelAction K g)]

/-- Absolute Gram row sums control adjoint energy. -/
theorem kernel_adjoint_energy_of_gram_rows {Z U : Type*} [Fintype Z] [Fintype U]
    (K : Z → U → ℂ) (R : ℝ)
    (hrow : ∀ z, ∑ w, ‖gramKernel K z w‖ ≤ R) (b : Z → ℂ) :
    finiteEnergy (kernelAdjoint K b) ≤ R * finiteEnergy b := by
  have he := congrArg Complex.re (kernelAdjoint_energy_gram K b)
  simp only [Complex.ofReal_re, Complex.re_sum] at he
  have hp (z w : Z) : (gramKernel K z w * b w * conj (b z)).re ≤
      ‖gramKernel K z w‖ * ‖b z‖ * ‖b w‖ := by
    have ht := Complex.re_le_norm (gramKernel K z w * b w * conj (b z))
    simpa only [norm_mul, Complex.norm_conj, mul_comm, mul_left_comm, mul_assoc] using ht
  have hs : ∀ z w, ‖gramKernel K z w‖ = ‖gramKernel K w z‖ := by
    intro z w
    rw [← gramKernel_conjugate K z w, Complex.norm_conj]
  rw [he]
  exact (Finset.sum_le_sum (fun z _ => Finset.sum_le_sum (fun w _ => hp z w))).trans
    (symmetric_nonnegative_form_bound (fun z w => ‖gramKernel K z w‖)
      (fun _ _ => norm_nonneg _) hs R hrow (fun z => ‖b z‖))

/-- Absolute Gram row sums control the original squared energy. -/
theorem kernel_action_energy_of_gram_rows {Z U : Type*} [Fintype Z] [Fintype U]
    (K : Z → U → ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hrow : ∀ z, ∑ w, ‖gramKernel K z w‖ ≤ R) (g : U → ℂ) :
    finiteEnergy (kernelAction K g) ≤ R * finiteEnergy g :=
  kernel_action_energy_of_adjoint K R hR (kernel_adjoint_energy_of_gram_rows K R hrow) g

/-- Converting a squared-energy bound to a norm bound retains the square root. -/
theorem kernel_action_sqrt_bound {Z U : Type*} [Fintype Z] [Fintype U]
    (K : Z → U → ℂ) (R : ℝ) (hR : 0 ≤ R)
    (henergy : ∀ g : U → ℂ, finiteEnergy (kernelAction K g) ≤ R * finiteEnergy g) (g : U → ℂ) :
    Real.sqrt (finiteEnergy (kernelAction K g)) ≤ Real.sqrt R * Real.sqrt (finiteEnergy g) := by
  simpa only [Real.sqrt_mul hR] using Real.sqrt_le_sqrt (henergy g)

/-- Finite kernel row and column bounds imply the product bound for Gram rows. -/
theorem kernel_gram_row_bound {Z U : Type*} [Fintype Z] [Fintype U]
    (K : Z → U → ℂ) (C D : ℝ) (hD : 0 ≤ D)
    (hrow : ∀ z, ∑ u, ‖K z u‖ ≤ C) (hcol : ∀ u, ∑ z, ‖K z u‖ ≤ D) (z : Z) :
    ∑ w, ‖gramKernel K z w‖ ≤ C * D := by
  calc
    _ ≤ ∑ w, ∑ u, ‖K z u‖ * ‖K w u‖ := by
      apply Finset.sum_le_sum
      intro w _
      simpa only [gramKernel, norm_mul, Complex.norm_conj] using
        norm_sum_le Finset.univ (fun u => K z u * conj (K w u))
    _ = ∑ u, ‖K z u‖ * ∑ w, ‖K w u‖ := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ ∑ u, ‖K z u‖ * D :=
      Finset.sum_le_sum (fun u _ => mul_le_mul_of_nonneg_left (hcol u) (norm_nonneg _))
    _ = (∑ u, ‖K z u‖) * D := (Finset.sum_mul ..).symm
    _ ≤ C * D := mul_le_mul_of_nonneg_right (hrow z) hD

/-- The finite rectangular Schur estimate with explicit row and column constants. -/
theorem kernel_action_energy_of_rows_columns {Z U : Type*} [Fintype Z] [Fintype U]
    (K : Z → U → ℂ) (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hrow : ∀ z, ∑ u, ‖K z u‖ ≤ C) (hcol : ∀ u, ∑ z, ‖K z u‖ ≤ D) (g : U → ℂ) :
    finiteEnergy (kernelAction K g) ≤ C * D * finiteEnergy g :=
  kernel_action_energy_of_gram_rows K (C * D) (mul_nonneg hC hD)
    (kernel_gram_row_bound K C D hD hrow hcol) g

/-- An original-operator energy bound transfers to its adjoint. -/
theorem kernel_adjoint_energy_of_action {Z U : Type*} [Fintype Z] [Fintype U]
    (K : Z → U → ℂ) (R : ℝ) (hR : 0 ≤ R)
    (haction : ∀ g : U → ℂ, finiteEnergy (kernelAction K g) ≤ R * finiteEnergy g)
    (b : Z → ℂ) : finiteEnergy (kernelAdjoint K b) ≤ R * finiteEnergy b := by
  have hcs := finitePairing_norm_sq_le (kernelAction K (kernelAdjoint K b)) b
  rw [kernel_adjoint_identity, finitePairing_self, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (finiteEnergy_nonneg _)] at hcs
  have he := mul_le_mul_of_nonneg_right (haction (kernelAdjoint K b)) (finiteEnergy_nonneg b)
  have hnonneg := mul_nonneg hR (finiteEnergy_nonneg b)
  nlinarith [finiteEnergy_nonneg (kernelAdjoint K b)]

/-- A block energy bound controls its complete linear-first pairing. -/
theorem kernel_pairing_bound_of_energy {Z U : Type*} [Fintype Z] [Fintype U]
    (K : Z → U → ℂ) (a : ℝ) (ha : 0 ≤ a)
    (henergy : ∀ g, finiteEnergy (kernelAction K g) ≤ a ^ 2 * finiteEnergy g)
    (g : U → ℂ) (b : Z → ℂ) :
    ‖finitePairing (kernelAction K g) b‖ ≤
      a * Real.sqrt (finiteEnergy b) * Real.sqrt (finiteEnergy g) := by
  have h := (finitePairing_norm_sq_le (kernelAction K g) b).trans
    (mul_le_mul_of_nonneg_right (henergy g) (finiteEnergy_nonneg b))
  have hp : (a * Real.sqrt (finiteEnergy b) * Real.sqrt (finiteEnergy g)) ^ 2 =
      a ^ 2 * finiteEnergy g * finiteEnergy b := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (finiteEnergy_nonneg b),
      Real.sq_sqrt (finiteEnergy_nonneg g)]
    ring
  have hn := mul_nonneg (mul_nonneg ha (Real.sqrt_nonneg (finiteEnergy b)))
    (Real.sqrt_nonneg (finiteEnergy g))
  nlinarith [norm_nonneg (finitePairing (kernelAction K g) b)]

def outputMaskedKernel {Z U : Type*} (K : Z → U → ℂ) (m : Z → ℂ) : Z → U → ℂ :=
  fun z u => m z * K z u

/-- An output mask multiplies the original finite action pointwise. -/
theorem outputMaskedKernel_action {Z U : Type*} [Fintype U]
    (K : Z → U → ℂ) (m : Z → ℂ) (g : U → ℂ) (z : Z) :
    kernelAction (outputMaskedKernel K m) g z = m z * kernelAction K g z := by
  simp only [kernelAction, outputMaskedKernel, Finset.mul_sum, mul_assoc]

/-- The conjugate output mask moves to the input of the exact adjoint. -/
theorem outputMaskedKernel_adjoint {Z U : Type*} [Fintype Z]
    (K : Z → U → ℂ) (m b : Z → ℂ) :
    kernelAdjoint (outputMaskedKernel K m) b = kernelAdjoint K (fun z => conj (m z) * b z) := by
  funext u
  simp only [kernelAdjoint, outputMaskedKernel, map_mul]
  apply Finset.sum_congr rfl
  intro z _
  ring

/-- Every pointwise complex contraction decreases finite energy. -/
theorem finiteEnergy_mask_le {Z : Type*} [Fintype Z]
    (m b : Z → ℂ) (hm : ∀ z, ‖m z‖ ≤ 1) :
    finiteEnergy (fun z => m z * b z) ≤ finiteEnergy b := by
  apply Finset.sum_le_sum
  intro z _
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  rw [norm_mul]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (hm z) (norm_nonneg (b z))

/-- Only the adjoint bound on the mask's actual support is needed. -/
theorem masked_action_energy_of_supported_adjoint {Z U : Type*} [Fintype Z] [Fintype U]
    (K : Z → U → ℂ) (P : Z → Prop) (m : Z → ℂ) (hm : ∀ z, ‖m z‖ ≤ 1)
    (hsupport : ∀ z, ¬ P z → m z = 0) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ b : Z → ℂ, (∀ z, ¬ P z → b z = 0) →
      finiteEnergy (kernelAdjoint K b) ≤ R * finiteEnergy b)
    (g : U → ℂ) :
    finiteEnergy (kernelAction (outputMaskedKernel K m) g) ≤ R * finiteEnergy g := by
  apply kernel_action_energy_of_adjoint _ R hR _ g
  intro b
  rw [outputMaskedKernel_adjoint]
  have hs : ∀ z, ¬ P z → conj (m z) * b z = 0 := by
    intro z hz
    simp only [hsupport z hz, map_zero, zero_mul]
  exact (hbound _ hs).trans (mul_le_mul_of_nonneg_left
    (finiteEnergy_mask_le (fun z => conj (m z)) b (fun z => by simpa using hm z)) hR)

/-- An exact one-dimensional obstruction to omitting the square-root loss. -/
theorem gram_row_bound_needs_square_root :
    ∃ K : Unit → Unit → ℂ, ∃ R : ℝ, 0 < R ∧
      (∀ z, ∑ w, ‖gramKernel K z w‖ ≤ R) ∧
      ∃ g : Unit → ℂ, R ^ 2 * finiteEnergy g < finiteEnergy (kernelAction K g) := by
  refine ⟨fun _ _ => (1 / 2 : ℂ), 1 / 4, by norm_num, ?_, fun _ => 1, ?_⟩
  · intro z
    norm_num [gramKernel, Complex.norm_div]
  · norm_num [finiteEnergy, kernelAction, Complex.norm_div]

end GMZP0
