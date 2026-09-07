import GMZP0.ParabolaGeometry

/-! Finite adjoints, using the manuscript's inner product linear in its first argument. -/

noncomputable section
open scoped BigOperators ComplexConjugate
namespace GMZP0

def finitePairing {Z : Type*} [Fintype Z] (a b : Z → ℂ) : ℂ :=
  ∑ z, a z * conj (b z)

def kernelAction {Z U : Type*} [Fintype U] (K : Z → U → ℂ) (g : U → ℂ) (z : Z) : ℂ :=
  ∑ u, K z u * g u

def kernelAdjoint {Z U : Type*} [Fintype Z] (K : Z → U → ℂ) (b : Z → ℂ) (u : U) : ℂ :=
  ∑ z, conj (K z u) * b z

/-- The adjoint convention is checked rather than inferred from a sign convention. -/
theorem kernel_adjoint_identity {Z U : Type*} [Fintype Z] [Fintype U]
    (K : Z → U → ℂ) (g : U → ℂ) (b : Z → ℂ) :
    finitePairing (kernelAction K g) b = finitePairing g (kernelAdjoint K b) := by
  simp only [finitePairing, kernelAction, kernelAdjoint, map_sum, map_mul,
    starRingEnd_self_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro z _
  ring

def gramKernel {Z U : Type*} [Fintype U] (K : Z → U → ℂ) (z w : Z) : ℂ :=
  ∑ u, K z u * conj (K w u)

theorem kernel_comp_adjoint {Z U : Type*} [Fintype Z] [Fintype U]
    (K : Z → U → ℂ) (b : Z → ℂ) (z : Z) :
    kernelAction K (kernelAdjoint K b) z = kernelAction (gramKernel K) b z := by
  simp only [kernelAction, kernelAdjoint, gramKernel, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  apply Finset.sum_congr rfl
  intro u _
  ring

theorem gramKernel_conjugate {Z U : Type*} [Fintype U]
    (K : Z → U → ℂ) (z w : Z) : conj (gramKernel K z w) = gramKernel K w z := by
  simp only [gramKernel, map_sum, map_mul, starRingEnd_self_apply]
  apply Finset.sum_congr rfl
  intro u _
  ring

/-- The kernel uses every original label and the exact original endpoint index. -/
def responseKernel (N : ℕ) (p : Base N → Frequency) (z : Base N) (u : InputBox N) : ℂ :=
  (∑ r : Fin N, if endpointIndex z r = u then cubicPhase (p z) r else 0) / (N : ℂ)

theorem responseKernel_action (N : ℕ) (p : Base N → Frequency)
    (g : InputBox N → ℂ) (z : Base N) :
    kernelAction (responseKernel N p) g z = finiteResponse N p g z := by
  classical
  simp only [kernelAction, responseKernel, div_eq_mul_inv, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [ite_mul, zero_mul, Fintype.sum_ite_eq]
  simp only [finiteResponse, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r _
  ring

def finiteAdjoint (N : ℕ) (p : Base N → Frequency) (b : Base N → ℂ) : InputBox N → ℂ :=
  kernelAdjoint (responseKernel N p) b

theorem finiteResponse_adjoint_identity (N : ℕ) (p : Base N → Frequency)
    (g : InputBox N → ℂ) (b : Base N → ℂ) :
    finitePairing (finiteResponse N p g) b = finitePairing g (finiteAdjoint N p b) := by
  have heq : kernelAction (responseKernel N p) g = finiteResponse N p g :=
    funext (responseKernel_action N p g)
  rw [← heq]
  exact kernel_adjoint_identity _ _ _

/-- AA* is exactly the sum over pairs of original labels sharing an original endpoint. -/
theorem responseKernel_gram (N : ℕ) (p : Base N → Frequency) (z w : Base N) :
    gramKernel (responseKernel N p) z w =
      (∑ r : Fin N, ∑ s : Fin N, if endpointIndex z r = endpointIndex w s then
        cubicPhase (p z) r * conj (cubicPhase (p w) s) else 0) / (N : ℂ) ^ 2 := by
  classical
  conv_rhs => rw [Finset.sum_comm]
  simp only [gramKernel, responseKernel, div_eq_mul_inv, map_mul, map_sum,
    apply_ite, map_zero, map_inv₀, map_natCast, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  simp only [ite_mul, mul_ite, zero_mul, mul_zero,
    Fintype.sum_ite_eq]
  by_cases he : endpointIndex z r = endpointIndex w s
  · simp only [he, if_true]
    ring
  · simp only [he, if_false]

/-- Within one horizontal fiber the Gram kernel is precisely the I/N diagonal. -/
theorem responseKernel_gram_same_horizontal {N : ℕ} (hN : 0 < N)
    (p : Base N → Frequency) (z w : Base N) (hx : z.1 = w.1) :
    gramKernel (responseKernel N p) z w = if z = w then (N : ℂ)⁻¹ else 0 := by
  classical
  rw [responseKernel_gram]
  by_cases hzw : z = w
  · subst w
    simp only [(endpointIndex_label_injective z).eq_iff, Fintype.sum_ite_eq,
      if_true, Complex.mul_conj', norm_cubicPhase,
      Complex.ofReal_one, one_pow, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
    have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    field_simp
  · have hne : ∀ r s : Fin N, endpointIndex z r ≠ endpointIndex w s := by
      intro r s he
      exact hzw (endpointIndex_same_horizontal z w r s hx he).1
    simp only [hne, if_false, Finset.sum_const_zero, zero_div, hzw]

/-- Summing AA* on the same horizontal fiber gives the original vector divided by N. -/
theorem responseKernel_horizontal_block {N : ℕ} (hN : 0 < N)
    (p : Base N → Frequency) (b : Base N → ℂ) (z : Base N) :
    (∑ w : Base N, if w.1 = z.1 then gramKernel (responseKernel N p) z w * b w else 0) =
      b z / (N : ℂ) := by
  classical
  have hterm : ∀ w : Base N,
      (if w.1 = z.1 then gramKernel (responseKernel N p) z w * b w else 0) =
        if w = z then (N : ℂ)⁻¹ * b z else 0 := by
    intro w
    by_cases hx : w.1 = z.1
    · rw [if_pos hx, responseKernel_gram_same_horizontal hN p z w hx.symm]
      by_cases hw : w = z
      · subst w
        simp
      · simp [hw, Ne.symm hw]
    · have hw : w ≠ z := fun h => hx (congrArg Prod.fst h)
      simp [hx, hw]
  simp_rw [hterm]
  simp [div_eq_mul_inv, mul_comm]

end GMZP0
