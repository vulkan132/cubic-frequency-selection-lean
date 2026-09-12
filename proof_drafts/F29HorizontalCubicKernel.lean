import GMZP0.ConstantFourier

/-! The actual horizontal cubic-plus-quadratic Fourier operator and its complete Gram labels. -/
noncomputable section
open scoped BigOperators ComplexConjugate
namespace GMZP0

theorem horizontalEndpointIndex_injective {N : ℕ} (x : Fin N) :
    Function.Injective (horizontalEndpointIndex x) := by
  intro r s h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [horizontalEndpointIndex] at hv
  omega

/-- The actual shared horizontal input forces exactly the original shifted label. -/
theorem horizontalEndpointIndex_collision_iff {N : ℕ} (x x' r s : Fin N) :
    horizontalEndpointIndex x r = horizontalEndpointIndex x' s ↔
      (label s : ℤ) = (label r : ℤ) - horizontalGap x x' := by
  rw [Fin.ext_iff]
  simp only [horizontalEndpointIndex, horizontalGap, label, Nat.cast_add, Nat.cast_one]
  omega

theorem horizontalEndpointIndex_shifted {N : ℕ} (x x' : Fin N)
    (r : blockFinLabels N (horizontalGap x x')) :
    horizontalEndpointIndex x r.val =
      horizontalEndpointIndex x' (shiftedBlockLabel (horizontalGap x x') r) := by
  exact (horizontalEndpointIndex_collision_iff ..).2 (shiftedBlockLabel_value _ r)

theorem horizontalEndpointIndex_collision_mem {N : ℕ} (x x' r s : Fin N)
    (h : horizontalEndpointIndex x r = horizontalEndpointIndex x' s) :
    r ∈ blockFinLabels N (horizontalGap x x') := by
  have hs := integer_label_bounds s
  rw [(horizontalEndpointIndex_collision_iff ..).1 h] at hs
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩

/-- Each collision occurs once in the full I_h label family, without boundary truncation. -/
theorem horizontal_collision_sum {N : ℕ} (x x' : Fin N) (F : Fin N → Fin N → ℂ) :
    (∑ r, ∑ s, if horizontalEndpointIndex x r = horizontalEndpointIndex x' s then F r s else 0) =
      ∑ r : blockFinLabels N (horizontalGap x x'),
        F r.val (shiftedBlockLabel (horizontalGap x x') r) := by
  classical
  let i : blockFinLabels N (horizontalGap x x') → Fin N × Fin N :=
    fun r => (r.val, shiftedBlockLabel (horizontalGap x x') r)
  have hi : Function.Injective i := by
    intro r s h
    exact Subtype.ext (congrArg Prod.fst h)
  have he := Fintype.sum_of_injective i hi
    (f := fun r => F r.val (shiftedBlockLabel (horizontalGap x x') r))
    (g := fun z : Fin N × Fin N =>
      if horizontalEndpointIndex x z.1 = horizontalEndpointIndex x' z.2 then F z.1 z.2 else 0)
  have hout (z : Fin N × Fin N) (hz : z ∉ Set.range i) :
      (if horizontalEndpointIndex x z.1 = horizontalEndpointIndex x' z.2 then F z.1 z.2 else 0) = 0 := by
    apply if_neg
    intro h
    have hr := horizontalEndpointIndex_collision_mem x x' z.1 z.2 h
    apply hz
    refine ⟨⟨z.1, hr⟩, ?_⟩
    apply Prod.ext
    · rfl
    · exact horizontalEndpointIndex_injective x'
        ((horizontalEndpointIndex_shifted x x' ⟨z.1, hr⟩).symm.trans h)
  have hin (r : blockFinLabels N (horizontalGap x x')) :
      (if horizontalEndpointIndex x (i r).1 = horizontalEndpointIndex x' (i r).2
        then F (i r).1 (i r).2 else 0) = F r.val (shiftedBlockLabel (horizontalGap x x') r) := by
    exact if_pos (horizontalEndpointIndex_shifted x x' r)
  simpa only [Fintype.sum_prod_type] using (he hout (fun r => (hin r).symm)).symm

def horizontalFourierPhase (a ξ : Frequency) (r : ℤ) : ℂ :=
  circleCharacter (r ^ 3 • a + r ^ 2 • ξ)

theorem norm_horizontalFourierPhase (a ξ : Frequency) (r : ℤ) :
    ‖horizontalFourierPhase a ξ r‖ = 1 := Circle.norm_coe _

theorem horizontalFourierPhase_label {N : ℕ} (a ξ : Frequency) (r : Fin N) :
    horizontalFourierPhase a ξ (label r) =
      circleCharacter (label r ^ 3 • a + label r ^ 2 • ξ) := by
  simp only [horizontalFourierPhase, ← Nat.cast_pow, natCast_zsmul]

def horizontalCubicKernel (N : ℕ) (φ : Fin N → Frequency) (ξ : Frequency)
    (x : Fin N) (u : Fin (2 * N)) : ℂ :=
  (∑ r : Fin N, if horizontalEndpointIndex x r = u then
    horizontalFourierPhase (φ x) ξ (label r) else 0) / (N : ℂ)

/-- The finite kernel acts on the exact original horizontal Fourier input. -/
theorem horizontalCubicKernel_action (N : ℕ) (φ : Fin N → Frequency) (ξ : Frequency)
    (u : Fin (2 * N) → ℂ) (x : Fin N) :
    kernelAction (horizontalCubicKernel N φ ξ) u x = horizontalCubicResponse N φ ξ u x := by
  classical
  simp only [kernelAction, horizontalCubicKernel, div_eq_mul_inv, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [ite_mul, zero_mul, Fintype.sum_ite_eq]
  simp only [horizontalCubicResponse, horizontalFourierPhase_label, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r _
  ring

/-- Complete double-label Gram formula with its original N^(-2) normalization. -/
theorem horizontalCubicKernel_gram (N : ℕ) (φ : Fin N → Frequency) (ξ : Frequency)
    (x x' : Fin N) :
    gramKernel (horizontalCubicKernel N φ ξ) x x' =
      (∑ r : Fin N, ∑ s : Fin N, if horizontalEndpointIndex x r = horizontalEndpointIndex x' s then
        horizontalFourierPhase (φ x) ξ (label r) *
          conj (horizontalFourierPhase (φ x') ξ (label s)) else 0) / (N : ℂ) ^ 2 := by
  classical
  conv_rhs => rw [Finset.sum_comm]
  simp only [gramKernel, horizontalCubicKernel, div_eq_mul_inv, map_mul, map_sum,
    apply_ite, map_zero, map_inv₀, map_natCast, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  simp only [ite_mul, mul_ite, zero_mul, mul_zero, Fintype.sum_ite_eq]
  by_cases he : horizontalEndpointIndex x r = horizontalEndpointIndex x' s
  · simp only [he, if_true]
    ring
  · simp only [he, if_false]

/-- The diagonal is exactly 1/N, independently of every phase parameter. -/
theorem horizontalCubicKernel_diagonal {N : ℕ} (hN : 0 < N)
    (φ : Fin N → Frequency) (ξ : Frequency) (x : Fin N) :
    gramKernel (horizontalCubicKernel N φ ξ) x x = (N : ℂ)⁻¹ := by
  rw [horizontalCubicKernel_gram]
  simp only [(horizontalEndpointIndex_injective x).eq_iff, Fintype.sum_ite_eq,
    Complex.mul_conj', norm_horizontalFourierPhase, one_pow, Complex.ofReal_one,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

/-- A single complete I_h sum, retaining the quadratic Fourier term in each original label. -/
theorem horizontalCubicKernel_gram_labels (N : ℕ) (φ : Fin N → Frequency) (ξ : Frequency)
    (x x' : Fin N) :
    gramKernel (horizontalCubicKernel N φ ξ) x x' =
      (∑ r : blockFinLabels N (horizontalGap x x'),
        horizontalFourierPhase (φ x) ξ (label r.val) *
          conj (horizontalFourierPhase (φ x') ξ ((label r.val : ℤ) - horizontalGap x x'))) /
        (N : ℂ) ^ 2 := by
  rw [horizontalCubicKernel_gram, horizontal_collision_sum]
  simp only [shiftedBlockLabel_value]

end GMZP0
