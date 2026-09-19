import GMZP0.BoundaryCutoffGluing

/-! An exact obstruction to treating the base cutoff's Lipschitz bound
as a bound for its product with an unrelated discontinuous observation. -/
noncomputable section
open scoped NNReal
namespace GMZP0

/-- Even a constant cutoff cannot regularize a unit jump away from its
declared boundary. This is a missing-hypothesis obstruction, not a P0 counterexample. -/
theorem boundary_cutoff_unrelated_jump_obstruction :
    ¬ ∃ K : ℝ≥0, LipschitzWith K (fun x : ℝ =>
      (boundaryCutoff ∅ 1 x : ℂ) * (if x ≤ 0 then (1 : ℂ) else -1)) := by
  rintro ⟨K, hK⟩
  let x : ℝ := ((K : ℝ) + 1)⁻¹
  have hden : 0 < (K : ℝ) + 1 := by positivity
  have hx : 0 < x := inv_pos.mpr hden
  have hprod : ((K : ℝ) + 1) * x = 1 := mul_inv_cancel₀ hden.ne'
  have h := hK.dist_le_mul 0 x
  rw [(boundary_cutoff_empty 1 0).2, (boundary_cutoff_empty 1 x).2] at h
  norm_num [not_le.mpr hx, Real.dist_eq, abs_of_pos hx, dist_eq_norm] at h
  nlinarith

end GMZP0
