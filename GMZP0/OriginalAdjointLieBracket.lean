import GMZP0.OriginalConjugationTangent
import GMZP0.OriginalRationalLowerCentral

/-! Bracket compatibility of the differential of actual conjugation.
All vector fields and differentials are Mathlib's native manifold ones. -/
noncomputable section
open scoped Manifold ContDiff
namespace GMZP0
variable {G sigma : Type*} [Group G] [TopologicalSpace G] [Fintype sigma]
attribute [local instance] original_real_lie_native_smoothness

/-- Conjugation and its inverse are smooth on the original manifold. -/
theorem original_conjugation_contMDiff (coord : G ≃ₜ (sigma → ℝ))
    (hLie : letI := coord.isOpenEmbedding.singletonChartedSpace;
      LieGroup 𝓘(ℝ, sigma → ℝ) ∞ G) (g : G) :
    letI := coord.isOpenEmbedding.singletonChartedSpace
    ContMDiff 𝓘(ℝ, sigma → ℝ) 𝓘(ℝ, sigma → ℝ) ∞ (fun h : G => g * h * g⁻¹) := by
  let := coord.isOpenEmbedding.singletonChartedSpace
  let := hLie
  exact (contMDiff_const.mul contMDiff_id).mul contMDiff_const

section TangentModelCalculations

set_option backward.isDefEq.respectTransparency false in
/-- The inverse of the actual conjugation differential is the derivative
of inverse conjugation at the actual image point. -/
theorem original_conjugation_inverse_mfderiv (coord : G ≃ₜ (sigma → ℝ))
    (hLie : letI := coord.isOpenEmbedding.singletonChartedSpace;
      LieGroup 𝓘(ℝ, sigma → ℝ) ∞ G) (g h : G) :
    letI := coord.isOpenEmbedding.singletonChartedSpace
    @Eq ((sigma → ℝ) →L[ℝ] (sigma → ℝ))
      (mfderiv 𝓘(ℝ, sigma → ℝ) 𝓘(ℝ, sigma → ℝ) (fun x : G => g * x * g⁻¹) h).inverse
      (mfderiv 𝓘(ℝ, sigma → ℝ) 𝓘(ℝ, sigma → ℝ)
        (fun x : G => g⁻¹ * x * (g⁻¹)⁻¹) (g * h * g⁻¹)) := by
  let := coord.isOpenEmbedding.singletonChartedSpace
  let := hLie
  have hd (a x : G) : MDifferentiableAt 𝓘(ℝ, sigma → ℝ) 𝓘(ℝ, sigma → ℝ)
      (fun y : G => a * y * a⁻¹) x :=
    ((original_conjugation_contMDiff coord hLie a).contMDiffAt).mdifferentiableAt (by simp)
  have he (a : G) : (fun x : G => a⁻¹ * x * (a⁻¹)⁻¹) ∘
      (fun x : G => a * x * a⁻¹) = id := by
    funext x
    simp [mul_assoc]
  have A := mfderiv_congr (I := 𝓘(ℝ, sigma → ℝ)) (I' := 𝓘(ℝ, sigma → ℝ))
    (x := h) (he g)
  rw [mfderiv_comp (I' := 𝓘(ℝ, sigma → ℝ)) _ (hd _ _) (hd _ _), mfderiv_id] at A
  have B := mfderiv_congr (I := 𝓘(ℝ, sigma → ℝ)) (I' := 𝓘(ℝ, sigma → ℝ))
    (x := g * h * g⁻¹) (he g⁻¹)
  rw [mfderiv_comp (I' := 𝓘(ℝ, sigma → ℝ)) _ (hd _ _) (hd _ _), mfderiv_id] at B
  have hback : g⁻¹ * (g * h * g⁻¹) * (g⁻¹)⁻¹ = h := by simp [mul_assoc]
  have hfun : (fun x : G => (g⁻¹)⁻¹ * x * ((g⁻¹)⁻¹)⁻¹) =
      (fun x : G => g * x * g⁻¹) := by simp only [inv_inv]
  rw [mfderiv_congr (I := 𝓘(ℝ, sigma → ℝ)) (I' := 𝓘(ℝ, sigma → ℝ)) hfun,
    mfderiv_congr_point (I := 𝓘(ℝ, sigma → ℝ)) (I' := 𝓘(ℝ, sigma → ℝ))
      (f := fun x : G => g * x * g⁻¹) hback] at B
  exact ContinuousLinearMap.inverse_eq B A

set_option backward.isDefEq.respectTransparency false in
/-- Pulling back an actual left-invariant field by conjugation gives the
left-invariant field of the inverse conjugation tangent action. -/
theorem original_conjugation_pullback_invariant (coord : G ≃ₜ (sigma → ℝ))
    (hLie : letI := coord.isOpenEmbedding.singletonChartedSpace;
      LieGroup 𝓘(ℝ, sigma → ℝ) ∞ G) (g : G) :
    letI := coord.isOpenEmbedding.singletonChartedSpace
    ∀ v : GroupLieAlgebra 𝓘(ℝ, sigma → ℝ) G,
      VectorField.mpullback 𝓘(ℝ, sigma → ℝ) 𝓘(ℝ, sigma → ℝ)
        (fun x : G => g * x * g⁻¹) (mulInvariantVectorField (I := 𝓘(ℝ, sigma → ℝ)) (G := G) v) =
        mulInvariantVectorField (I := 𝓘(ℝ, sigma → ℝ)) (G := G) (originalAdjoint coord g⁻¹ v) := by
  let := coord.isOpenEmbedding.singletonChartedSpace
  let := hLie
  intro v
  funext h
  rw [VectorField.mpullback, original_conjugation_inverse_mfderiv coord hLie]
  simp only [mulInvariantVectorField]
  rw [← original_adjoint_native coord hLie g⁻¹]
  have he : (fun x : G => g⁻¹ * x * (g⁻¹)⁻¹) ∘ (fun x : G => (g * h * g⁻¹) * x) =
      (fun x : G => h * x) ∘ (fun x : G => g⁻¹ * x * (g⁻¹)⁻¹) := by
    funext x
    simp [mul_assoc]
  have hd (a x : G) : MDifferentiableAt 𝓘(ℝ, sigma → ℝ) 𝓘(ℝ, sigma → ℝ)
      (fun y : G => a * y * a⁻¹) x :=
    ((original_conjugation_contMDiff coord hLie a).contMDiffAt).mdifferentiableAt (by simp)
  have hl (a x : G) : MDifferentiableAt 𝓘(ℝ, sigma → ℝ) 𝓘(ℝ, sigma → ℝ)
      (fun y : G => a * y) x :=
    contMDiff_mul_left.contMDiffAt.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)
  have heD := mfderiv_congr (I := 𝓘(ℝ, sigma → ℝ)) (I' := 𝓘(ℝ, sigma → ℝ))
    (x := (1 : G)) he
  rw [mfderiv_comp (I' := 𝓘(ℝ, sigma → ℝ)) _ (hd _ _) (hl _ _),
    mfderiv_comp (I' := 𝓘(ℝ, sigma → ℝ)) _ (hl _ _) (hd _ _)] at heD
  rw [mfderiv_congr_point (I := 𝓘(ℝ, sigma → ℝ)) (I' := 𝓘(ℝ, sigma → ℝ))
      (f := fun x : G => g⁻¹ * x * (g⁻¹)⁻¹) (mul_one (g * h * g⁻¹)),
    mfderiv_congr_point (I := 𝓘(ℝ, sigma → ℝ)) (I' := 𝓘(ℝ, sigma → ℝ))
      (f := fun x : G => h * x) (by simp : g⁻¹ * (1 : G) * (g⁻¹)⁻¹ = 1)] at heD
  exact congrArg (fun D : (sigma → ℝ) →L[ℝ] (sigma → ℝ) => D v) heD

set_option backward.isDefEq.respectTransparency false in
/-- The conjugation differential commutes with the native vector-field
bracket at the identity. No coordinate pointwise bracket is involved. -/
theorem original_adjoint_vectorfield_bracket (coord : G ≃ₜ (sigma → ℝ))
    (hLie : letI := coord.isOpenEmbedding.singletonChartedSpace;
      LieGroup 𝓘(ℝ, sigma → ℝ) ∞ G) (g : G) :
    letI := coord.isOpenEmbedding.singletonChartedSpace
    letI := hLie
    ∀ v w : GroupLieAlgebra 𝓘(ℝ, sigma → ℝ) G,
      originalAdjoint coord g (VectorField.mlieBracket 𝓘(ℝ, sigma → ℝ)
        (mulInvariantVectorField (I := 𝓘(ℝ, sigma → ℝ)) (G := G) v)
        (mulInvariantVectorField (I := 𝓘(ℝ, sigma → ℝ)) (G := G) w) 1) =
      VectorField.mlieBracket 𝓘(ℝ, sigma → ℝ)
        (mulInvariantVectorField (I := 𝓘(ℝ, sigma → ℝ)) (G := G) (originalAdjoint coord g v))
        (mulInvariantVectorField (I := 𝓘(ℝ, sigma → ℝ)) (G := G) (originalAdjoint coord g w)) 1 := by
  let := coord.isOpenEmbedding.singletonChartedSpace
  let := hLie
  intro v w
  have hn : minSmoothness ℝ 2 ≤ (∞ : ℕ∞ω) := by
    simp only [minSmoothness_of_isRCLikeNormedField]
    norm_cast
  have h := VectorField.mpullback_mlieBracket
    (I := 𝓘(ℝ, sigma → ℝ)) (I' := 𝓘(ℝ, sigma → ℝ))
    (f := fun x : G => g⁻¹ * x * (g⁻¹)⁻¹) (x₀ := (1 : G))
    (mdifferentiableAt_mulInvariantVectorField (I := 𝓘(ℝ, sigma → ℝ)) (G := G) v)
    (mdifferentiableAt_mulInvariantVectorField (I := 𝓘(ℝ, sigma → ℝ)) (G := G) w)
    (original_conjugation_contMDiff coord hLie g⁻¹).contMDiffAt hn
  rw [original_conjugation_pullback_invariant coord hLie,
    original_conjugation_pullback_invariant coord hLie] at h
  dsimp only [VectorField.mpullback] at h
  rw [original_conjugation_inverse_mfderiv coord hLie] at h
  have hpoint : g⁻¹ * (1 : G) * (g⁻¹)⁻¹ = 1 := by simp
  have hfun : (fun x : G => (g⁻¹)⁻¹ * x * ((g⁻¹)⁻¹)⁻¹) =
      (fun x : G => g * x * g⁻¹) := by simp only [inv_inv]
  rw [mfderiv_congr (I := 𝓘(ℝ, sigma → ℝ)) (I' := 𝓘(ℝ, sigma → ℝ)) hfun,
    mfderiv_congr_point (I := 𝓘(ℝ, sigma → ℝ)) (I' := 𝓘(ℝ, sigma → ℝ))
      (f := fun x : G => g * x * g⁻¹) hpoint,
    original_adjoint_native coord hLie] at h
  have hb := congrArg (fun x : G => (VectorField.mlieBracket 𝓘(ℝ, sigma → ℝ)
    (mulInvariantVectorField (I := 𝓘(ℝ, sigma → ℝ)) (G := G) v)
    (mulInvariantVectorField (I := 𝓘(ℝ, sigma → ℝ)) (G := G) w) x : sigma → ℝ)) hpoint
  rw [hb, inv_inv] at h
  exact h

end TangentModelCalculations

/-- The actual conjugation differential preserves the actual native Lie
bracket. Both instances explicitly use the original Lie algebra; the
equality follows from its actual vector-field bracket definition. -/
theorem original_adjoint_preserves_native_bracket (coord : G ≃ₜ (sigma → ℝ))
    (hLie : letI := coord.isOpenEmbedding.singletonChartedSpace;
      LieGroup 𝓘(ℝ, sigma → ℝ) ∞ G) (g : G) :
    letI := coord.isOpenEmbedding.singletonChartedSpace
    letI := hLie
    ∀ v w : GroupLieAlgebra 𝓘(ℝ, sigma → ℝ) G,
      originalAdjoint coord g
        (@Bracket.bracket (GroupLieAlgebra 𝓘(ℝ, sigma → ℝ) G)
          (GroupLieAlgebra 𝓘(ℝ, sigma → ℝ) G) inferInstance v w) =
        @Bracket.bracket (GroupLieAlgebra 𝓘(ℝ, sigma → ℝ) G)
          (GroupLieAlgebra 𝓘(ℝ, sigma → ℝ) G) inferInstance
          (originalAdjoint coord g v) (originalAdjoint coord g w) := by
  let := coord.isOpenEmbedding.singletonChartedSpace
  let := hLie
  exact original_adjoint_vectorfield_bracket coord hLie g

/-- The native differential is now a proved Lie homomorphism on the
original tangent algebra, not a supplied bracket-compatibility premise. -/
def originalAdjointLieHom (coord : G ≃ₜ (sigma → ℝ))
    (hLie : letI := coord.isOpenEmbedding.singletonChartedSpace;
      LieGroup 𝓘(ℝ, sigma → ℝ) ∞ G) (g : G) :
    letI := coord.isOpenEmbedding.singletonChartedSpace
    letI := hLie
    GroupLieAlgebra 𝓘(ℝ, sigma → ℝ) G →ₗ⁅ℝ⁆ GroupLieAlgebra 𝓘(ℝ, sigma → ℝ) G := by
  let := coord.isOpenEmbedding.singletonChartedSpace
  let := hLie
  exact { (originalAdjoint coord g).toLinearMap with
    map_lie' := fun {v w} => original_adjoint_preserves_native_bracket coord hLie g v w }

end GMZP0
