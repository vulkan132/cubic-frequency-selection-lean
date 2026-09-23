import GMZP0.OriginalChartDifferential

/-! The actual manifold Lie bracket in the original singleton chart,
with its derivative transports explicitly identified. -/
noncomputable section
open scoped Manifold
namespace GMZP0
variable {G E : Type*} [TopologicalSpace G] [Nonempty G]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option backward.isDefEq.respectTransparency false in
/-- The original global coordinate map acts as the identity on its own
manifold tangent coefficients at every point. -/
theorem original_chart_mfderiv (coord : G ≃ₜ E) (x : G) :
    letI := coord.isOpenEmbedding.singletonChartedSpace
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) coord x = ContinuousLinearMap.id ℝ E := by
  let := coord.isOpenEmbedding.singletonChartedSpace
  let : IsManifold 𝓘(ℝ, E) 1 G := coord.isOpenEmbedding.isManifold_singleton
  simpa only [original_ext_chart] using!
    (mfderiv_extChartAt_self (I := 𝓘(ℝ, E)) (x := x))

set_option backward.isDefEq.respectTransparency false in
/-- The inverse original chart has the identity differential at every
coordinate point, with the original manifold tangent space as target. -/
theorem original_chart_symm_mfderiv (coord : G ≃ₜ E) (y : E) :
    letI := coord.isOpenEmbedding.singletonChartedSpace
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) coord.symm y = ContinuousLinearMap.id ℝ E := by
  let := coord.isOpenEmbedding.singletonChartedSpace
  let : IsManifold 𝓘(ℝ, E) 1 G := coord.isOpenEmbedding.isManifold_singleton
  have h := mfderivWithin_range_extChartAt_symm (I := 𝓘(ℝ, E)) (x := coord.symm y)
  have hs := original_ext_chart_symm coord (coord.symm y)
  have hx := congrFun (original_ext_chart coord (coord.symm y)) (coord.symm y)
  simp only [coord.apply_symm_apply] at hx
  simp only [modelWithCornersSelf_coe, Set.range_id, mfderivWithin_univ] at h
  rw [hx, hs] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- The actual manifold Lie bracket is the analytic coordinate bracket
in the same original chart. No bracket identification is assumed. -/
theorem original_chart_lie_bracket (coord : G ≃ₜ E) (V W : G → E) (x : G) :
    letI := coord.isOpenEmbedding.singletonChartedSpace
    VectorField.mlieBracket 𝓘(ℝ, E) V W x =
      VectorField.lieBracket ℝ (V ∘ coord.symm) (W ∘ coord.symm) (coord x) := by
  let := coord.isOpenEmbedding.singletonChartedSpace
  let : IsManifold 𝓘(ℝ, E) 1 G := coord.isOpenEmbedding.isManifold_singleton
  have hpb (U : G → E) :
      VectorField.mpullbackWithin 𝓘(ℝ, E) 𝓘(ℝ, E) coord.symm U Set.univ = U ∘ coord.symm := by
    funext y
    change (mfderivWithin 𝓘(ℝ, E) 𝓘(ℝ, E) coord.symm Set.univ y).inverse (U (coord.symm y)) = _
    rw [mfderivWithin_univ, original_chart_symm_mfderiv]
    change (ContinuousLinearMap.id ℝ E).inverse (U (coord.symm y)) = _
    rw [ContinuousLinearMap.inverse_id]
    rfl
  rw [VectorField.mlieBracket, VectorField.mlieBracketWithin_apply,
    mfderiv_extChartAt_self, ContinuousLinearMap.inverse_id]
  simp only [original_ext_chart, original_ext_chart_symm,
    Set.preimage_univ, modelWithCornersSelf_coe, Set.range_id, Set.inter_univ,
    VectorField.lieBracketWithin_univ, hpb]
  rfl

end GMZP0
