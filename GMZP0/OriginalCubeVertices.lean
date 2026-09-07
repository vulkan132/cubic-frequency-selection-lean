import GMZP0.CyclicCubePhase

/-! A cube of nonzero original weight reads actual retained original base points at every vertex. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

theorem cyclicCubeWeight_ne_zero_vertices (N q ℓ : ℕ) (σ : Base N → ℝ)
    (x : Fin N) (Y : ZMod q) (h : ℤ) (u : CubeShiftPairs ℓ)
    (hW : cyclicCubeWeight N q ℓ σ x Y h u ≠ 0) :
    ∀ ω : Fin 4 → Bool, cyclicField N q σ 0 x (cyclicCubeVertex q ℓ h Y u ω) ≠ 0 := by
  intro ω
  exact Finset.prod_ne_zero_iff.mp hW ω (Finset.mem_univ ω)

theorem cyclicCube_original_vertices {N q : ℕ} [NeZero q] (hq : N ^ 2 < q) (ℓ : ℕ)
    (f : ℤ × ℤ → ℂ) (θ : Base N → Frequency) (lam : Base N → ℂ)
    (μ : Base N → ℝ) (D : Finset (Base N)) (η : ℝ)
    (hresponse : ∀ z, μ z ≠ 0 → η ≤ (lam z * response N f z (θ z)).re)
    (x : Fin N) (Y : ZMod q) (h : ℤ) (u : CubeShiftPairs ℓ)
    (hW : cyclicCubeWeight N q ℓ (originalScaledWeight N μ D) x Y h u ≠ 0) :
    ∀ ω : Fin 4 → Bool, ∃ y : Fin (N ^ 2),
      cyclicCubeVertex q ℓ h Y u ω = cyclicRow N q y ∧
      (x, y) ∈ D ∧ μ (x, y) ≠ 0 ∧
      cyclicField N q θ 0 x (cyclicCubeVertex q ℓ h Y u ω) = θ (x, y) ∧
      cyclicField N q lam 1 x (cyclicCubeVertex q ℓ h Y u ω) = lam (x, y) ∧
      cyclicField N q (originalScaledWeight N μ D) 0 x (cyclicCubeVertex q ℓ h Y u ω) =
        (N : ℝ) ^ 3 * μ (x, y) ∧
      η ≤ (lam (x, y) * response N f (x, y) (θ (x, y))).re := by
  intro ω
  have hs := cyclicCubeWeight_ne_zero_vertices N q ℓ (originalScaledWeight N μ D) x Y h u hW ω
  have hr : cyclicCubeVertex q ℓ h Y u ω ∈ Set.range (cyclicRow N q) := by
    by_contra hn
    exact hs (cyclicField_outside_range hq (originalScaledWeight N μ D) 0 x _ hn)
  obtain ⟨y, hy⟩ := hr
  have ho : originalScaledWeight N μ D (x, y) ≠ 0 := by
    rwa [← hy, cyclicField_original hq] at hs
  have hd := originalScaledWeight_support μ D (x, y) ho
  refine ⟨y, hy.symm, hd.1, hd.2, ?_, ?_, ?_, hresponse (x, y) hd.2⟩
  · rw [← hy, cyclicField_original hq]
  · rw [← hy, cyclicField_original hq]
  · rw [← hy, cyclicField_original hq, originalScaledWeight, if_pos hd.1]

end GMZP0
