import GMZP0.OriginalCurveLieTangent

/-! Subgroup uniqueness with the actual native manifold derivative.
The differentiability condition is retained: an equality involving a
totalized derivative alone would not prescribe an initial tangent. -/
noncomputable section
open scoped Manifold
namespace GMZP0
variable {G E : Type*} [Group G] [TopologicalSpace G]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A constructed subgroup with its original coordinate tangent and
uniqueness among all subgroups with that tangent. -/
def OriginalCoordinateSubgroup (coord : G ≃ₜ E) (gamma : ℝ → G) (v : E) : Prop :=
  gamma 0 = 1 ∧ (∀ s t, gamma (s + t) = gamma s * gamma t) ∧
    HasDerivAt (coord ∘ gamma) v 0 ∧
    ∀ eta : ℝ → G, (∀ s t, eta (s + t) = eta s * eta t) →
      HasDerivAt (coord ∘ eta) v 0 → eta = gamma

/-- The native initial tangent condition includes actual differentiability,
and applies the differential to the unit scalar tangent. -/
def OriginalNativeSubgroup (coord : G ≃ₜ E) (gamma : ℝ → G) (v : E) : Prop :=
  letI := coord.isOpenEmbedding.singletonChartedSpace
  gamma 0 = 1 ∧ (∀ s t, gamma (s + t) = gamma s * gamma t) ∧
    MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) gamma 0 ∧
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) gamma 0 (1 : ℝ) = v

set_option backward.isDefEq.respectTransparency false in
/-- A native derivative on the scalar unit determines the full original
coordinate derivative, provided actual differentiability is retained. -/
theorem original_coordinate_derivative_iff_native (coord : G ≃ₜ E)
    (gamma : ℝ → G) (v : E) :
    letI := coord.isOpenEmbedding.singletonChartedSpace
    HasDerivAt (coord ∘ gamma) v 0 ↔
      MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) gamma 0 ∧
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) gamma 0 (1 : ℝ) = v := by
  let := coord.isOpenEmbedding.singletonChartedSpace
  constructor
  · intro h
    exact ⟨((original_curve_has_mfderiv_iff coord gamma 0 _).mpr
      h.hasFDerivAt).mdifferentiableAt, original_curve_lie_tangent coord gamma 0 v h⟩
  · rintro ⟨hd, hv⟩
    have h := (original_curve_has_mfderiv_iff coord gamma 0 _).mp hd.hasMFDerivAt
    have hh := h.hasDerivAt
    convert! hh using 1
    exact hv.symm

/-- A proved original coordinate subgroup is the unique actual native
subgroup with that tangent. No separate existential choices are made. -/
theorem original_coordinate_subgroup_native_unique (coord : G ≃ₜ E)
    (gamma : ℝ → G) (v : E) (h : OriginalCoordinateSubgroup coord gamma v) :
    OriginalNativeSubgroup coord gamma v ∧
      ∀ eta, OriginalNativeSubgroup coord eta v → eta = gamma := by
  obtain ⟨h0, hm, hd, hu⟩ := h
  have hn := (original_coordinate_derivative_iff_native coord gamma v).mp hd
  refine ⟨⟨h0, hm, hn⟩, ?_⟩
  intro eta he
  exact hu eta he.2.1
    ((original_coordinate_derivative_iff_native coord eta v).mpr he.2.2)

/-- Real time rescaling scales the actual native tangent, including at
zero and negative scales; the original subgroup law is retained. -/
theorem original_native_subgroup_rescale (coord : G ≃ₜ E)
    (gamma : ℝ → G) (v : E) (h : OriginalNativeSubgroup coord gamma v) (r : ℝ) :
    OriginalNativeSubgroup coord (fun t => gamma (r * t)) (r • v) := by
  have hd := (original_coordinate_derivative_iff_native coord gamma v).mpr h.2.2
  have hr : HasDerivAt (fun t : ℝ => r * t) r 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul r
  have hcomp : HasDerivAt (coord ∘ fun t => gamma (r * t)) (r • v) 0 := by
    exact hd.scomp_of_eq 0 hr (mul_zero r).symm
  refine ⟨?_, ?_, (original_coordinate_derivative_iff_native coord _ _).mp hcomp⟩
  · simpa using h.1
  · intro s t
    change gamma (r * (s + t)) = gamma (r * s) * gamma (r * t)
    rw [mul_add, h.2.1]

/-- A time-one map characterized by unique native subgroups determines
their values at every real time, not just at the endpoint. -/
theorem original_native_time_one_all_times (coord : G ≃ₜ E) (exp : E → G)
    (hexp : ∀ v, ∃ gamma : ℝ → G, OriginalNativeSubgroup coord gamma v ∧
      (∀ eta, OriginalNativeSubgroup coord eta v → eta = gamma) ∧ gamma 1 = exp v)
    (v : E) (gamma : ℝ → G) (hgamma : OriginalNativeSubgroup coord gamma v) :
    ∀ t : ℝ, gamma t = exp (t • v) := by
  intro t
  obtain ⟨delta, hd, hu, h1⟩ := hexp (t • v)
  have heq := hu (fun s => gamma (t * s)) (original_native_subgroup_rescale coord gamma v hgamma t)
  have hh := congrFun heq 1
  simpa only [mul_one, h1] using hh

/-- The actual exponential line is itself the unique native subgroup
with the prescribed tangent, on the entire real time axis. -/
theorem original_native_time_one_canonical_subgroup (coord : G ≃ₜ E) (exp : E → G)
    (hexp : ∀ v, ∃ gamma : ℝ → G, OriginalNativeSubgroup coord gamma v ∧
      (∀ eta, OriginalNativeSubgroup coord eta v → eta = gamma) ∧ gamma 1 = exp v) :
    ∀ v, OriginalNativeSubgroup coord (fun t : ℝ => exp (t • v)) v ∧
      ∀ eta, OriginalNativeSubgroup coord eta v → eta = (fun t : ℝ => exp (t • v)) := by
  intro v
  obtain ⟨gamma, hg, hu, h1⟩ := hexp v
  have heq := funext (original_native_time_one_all_times coord exp hexp v gamma hg)
  exact ⟨heq ▸ hg, fun eta he => (hu eta he).trans heq⟩

end GMZP0
