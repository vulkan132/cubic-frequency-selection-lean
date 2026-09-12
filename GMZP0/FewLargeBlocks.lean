import GMZP0.BlockSchur

/-! Count actual large Gram blocks and deduce the finite Schur energy estimate.
The large-block count is an explicit premise, not a structural existence theorem. -/

noncomputable section
open scoped BigOperators ComplexConjugate
namespace GMZP0

/-- Large means failure of the actual complete vertical block energy bound. -/
def largeBlockNeighbors {N : ℕ} {Y U : Type*} [Fintype Y] [Fintype U]
    (K : (Fin N × Y) → U → ℂ) (H : Finset (Fin N)) (v : ℝ) (x : Fin N) : Finset (Fin N) := by
  classical
  exact H.filter (fun x' => x' ≠ x ∧ ¬ KernelEnergyBound (blockGramKernel K x x') (v / N))

def largeBlockCoefficient {N : ℕ} {Y U : Type*} [Fintype Y] [Fintype U]
    (K : (Fin N × Y) → U → ℂ) (H : Finset (Fin N)) (v : ℝ) (x x' : Fin N) : ℝ := by
  classical
  exact if x ∈ H ∧ x' ∈ H then
    if x' = x then (N : ℝ)⁻¹ else
      if KernelEnergyBound (blockGramKernel K x x') (v / N) then v / N else (N : ℝ)⁻¹
    else 0

/-- All selected block coefficients are nonnegative for a nonnegative threshold. -/
theorem largeBlockCoefficient_nonneg {N : ℕ} {Y U : Type*} [Fintype Y] [Fintype U]
    (K : (Fin N × Y) → U → ℂ) (H : Finset (Fin N)) (v : ℝ) (hv : 0 ≤ v)
    (x x' : Fin N) : 0 ≤ largeBlockCoefficient K H v x x' := by
  unfold largeBlockCoefficient
  split_ifs <;> positivity

/-- The selected coefficient matrix inherits exact block-adjoint symmetry. -/
theorem largeBlockCoefficient_symm {N : ℕ} {Y U : Type*} [Fintype Y] [Fintype U]
    (K : (Fin N × Y) → U → ℂ) (H : Finset (Fin N)) (v : ℝ) (x x' : Fin N) :
    largeBlockCoefficient K H v x x' = largeBlockCoefficient K H v x' x := by
  classical
  by_cases he : x' = x
  · subst x'
    rfl
  · have he' : x ≠ x' := Ne.symm he
    have hs := blockGramKernel_energy_bound_symm K (v / N) x x'
    by_cases hx : x ∈ H <;> by_cases hx' : x' ∈ H <;>
      simp [largeBlockCoefficient, hx, hx', he, he', hs]

/-- Count large blocks while retaining both the small-block and diagonal contributions. -/
theorem largeBlockCoefficient_row {N : ℕ} (hN : 0 < N) {Y U : Type*}
    [Fintype Y] [Fintype U] (K : (Fin N × Y) → U → ℂ) (H : Finset (Fin N))
    (v ρ : ℝ) (hv : 0 ≤ v) (hρ : 0 ≤ ρ)
    (hcount : ∀ x ∈ H, ((largeBlockNeighbors K H v x).card : ℝ) ≤ ρ * N) (x : Fin N) :
    ∑ x', largeBlockCoefficient K H v x x' ≤ ρ + v + (N : ℝ)⁻¹ := by
  classical
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  by_cases hx : x ∈ H
  · have hp (x' : Fin N) : largeBlockCoefficient K H v x x' ≤
        (if x' = x then (N : ℝ)⁻¹ else 0) +
        (if x' ∈ largeBlockNeighbors K H v x then (N : ℝ)⁻¹ else 0) + v / N := by
      by_cases hx' : x' ∈ H <;> by_cases he : x' = x <;>
        by_cases hs : KernelEnergyBound (blockGramKernel K x x') (v / N) <;>
        simp [largeBlockCoefficient, largeBlockNeighbors, hx, hx', he, hs] <;> positivity
    have hc : (∑ x' : Fin N, if x' ∈ largeBlockNeighbors K H v x then (N : ℝ)⁻¹ else 0) =
        ((largeBlockNeighbors K H v x).card : ℝ) / N := by
      rw [← Finset.sum_filter]
      simp [div_eq_mul_inv]
    have hcard : ((largeBlockNeighbors K H v x).card : ℝ) / N ≤ ρ :=
      (div_le_iff₀ hNr).2 (hcount x hx)
    have hs := Finset.sum_le_sum (fun x' (_ : x' ∈ (Finset.univ : Finset (Fin N))) => hp x')
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, hc, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
    have he : (N : ℝ) * (v / N) = v := by field_simp
    rw [he] at hs
    linarith
  · simp only [largeBlockCoefficient, hx, false_and, ↓reduceIte, Finset.sum_const_zero]
    positivity

/-- Horizontal support makes every block outside the retained pair of fibers zero. -/
theorem blockGramKernel_zero_outside {N : ℕ} {Y U : Type*} [Fintype U]
    (K : (Fin N × Y) → U → ℂ) (H : Finset (Fin N))
    (hsupport : ∀ x, x ∉ H → ∀ y u, K (x, y) u = 0)
    (x x' : Fin N) (hout : ¬ (x ∈ H ∧ x' ∈ H)) (y v : Y) :
    blockGramKernel K x x' y v = 0 := by
  classical
  by_cases hx : x ∈ H
  · have hx' : x' ∉ H := fun hx' => hout ⟨hx, hx'⟩
    simp [blockGramKernel, gramKernel, hsupport x' hx']
  · simp [blockGramKernel, gramKernel, hsupport x hx]

/-- The selected coefficient bounds every actual block, including outside the support. -/
theorem largeBlockCoefficient_bounds_blocks {N : ℕ} {Y U : Type*} [Fintype Y] [Fintype U]
    (K : (Fin N × Y) → U → ℂ) (H : Finset (Fin N)) (v : ℝ)
    (hsupport : ∀ x, x ∉ H → ∀ y u, K (x, y) u = 0)
    (htrivial : ∀ x x', KernelEnergyBound (blockGramKernel K x x') (N : ℝ)⁻¹)
    (x x' : Fin N) : KernelEnergyBound (blockGramKernel K x x')
      (largeBlockCoefficient K H v x x') := by
  classical
  unfold largeBlockCoefficient
  split_ifs with hmem he hs
  · exact htrivial x x'
  · exact hs
  · exact htrivial x x'
  · intro g
    simp [kernelAction, blockGramKernel_zero_outside K H hsupport x x' hmem,
      finiteEnergy]

/-- The diagonal costs 1/N; the original operator costs the square root of this row sum. -/
theorem kernel_energy_of_few_large_blocks {N : ℕ} (hN : 0 < N) {Y U : Type*}
    [Fintype Y] [Fintype U] (K : (Fin N × Y) → U → ℂ) (H : Finset (Fin N))
    (v ρ : ℝ) (hv : 0 ≤ v) (hρ : 0 ≤ ρ)
    (hsupport : ∀ x, x ∉ H → ∀ y u, K (x, y) u = 0)
    (htrivial : ∀ x x', KernelEnergyBound (blockGramKernel K x x') (N : ℝ)⁻¹)
    (hcount : ∀ x ∈ H, ((largeBlockNeighbors K H v x).card : ℝ) ≤ ρ * N)
    (g : U → ℂ) :
    finiteEnergy (kernelAction K g) ≤ (ρ + v + (N : ℝ)⁻¹) * finiteEnergy g := by
  exact kernel_action_energy_of_block_rows K (largeBlockCoefficient K H v)
    (largeBlockCoefficient_nonneg K H v hv) (largeBlockCoefficient_symm K H v)
    (largeBlockCoefficient_bounds_blocks K H v hsupport htrivial)
    (ρ + v + (N : ℝ)⁻¹) (by positivity) (largeBlockCoefficient_row hN K H v ρ hv hρ hcount) g

end GMZP0
