import GMZP0.RationalPolynomialDerivative
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! The actual infinitesimal translation on the original observation
space, with rational coefficients in the original coordinate tangent.
The differential is proved along every differentiable curve through the
identity; a coordinate curve is not assumed to be a one-parameter subgroup. -/
noncomputable section
open Module MvPolynomial
open scoped Topology
namespace GMZP0
variable {G sigma iota : Type*} [Group G] [Fintype sigma] [Fintype iota]

/-- A rational coefficient array acts on the original real observation
space, linearly in the observation and in the real coordinate tangent. -/
def observationCoordinateDifferential (V : ObservationModule G)
    (b : Basis iota ℝ V.space) (A : iota → iota → sigma → ℚ)
    (v : sigma → ℝ) : Module.End ℝ V.space :=
  b.equivFun.symm.toLinearMap.comp
    ((Matrix.mulVecLin (fun i j => ∑ s, (A i j s : ℝ) * v s)).comp b.equivFun.toLinearMap)

/-- Exact coefficients of the original-space differential. -/
theorem observation_coordinate_differential_repr
    (V : ObservationModule G) (b : Basis iota ℝ V.space)
    (A : iota → iota → sigma → ℚ) (v : sigma → ℝ) (F : V.space) (i : iota) :
    b.equivFun (observationCoordinateDifferential V b A v F) i =
      ∑ j, (∑ s, (A i j s : ℝ) * v s) * b.equivFun F j := by
  change b.equivFun (b.equivFun.symm
    ((Matrix.mulVecLin (fun i j => ∑ s, (A i j s : ℝ) * v s)) (b.equivFun F))) i = _
  rw [b.equivFun.apply_symm_apply]
  rfl

/-- The differential depends additively on the coordinate tangent. -/
theorem observation_coordinate_differential_add
    (V : ObservationModule G) (b : Basis iota ℝ V.space)
    (A : iota → iota → sigma → ℚ) (v w : sigma → ℝ) :
    observationCoordinateDifferential V b A (v + w) =
      observationCoordinateDifferential V b A v + observationCoordinateDifferential V b A w := by
  apply LinearMap.ext
  intro F
  apply b.equivFun.injective
  ext i
  simp only [LinearMap.add_apply, map_add, Pi.add_apply,
    observation_coordinate_differential_repr, mul_add, add_mul, Finset.sum_add_distrib]

/-- The differential is homogeneous for every real tangent scalar. -/
theorem observation_coordinate_differential_smul
    (V : ObservationModule G) (b : Basis iota ℝ V.space)
    (A : iota → iota → sigma → ℚ) (a : ℝ) (v : sigma → ℝ) :
    observationCoordinateDifferential V b A (a • v) =
      a • observationCoordinateDifferential V b A v := by
  apply LinearMap.ext
  intro F
  apply b.equivFun.injective
  ext i
  simp only [LinearMap.smul_apply, map_smul, Pi.smul_apply, smul_eq_mul,
    observation_coordinate_differential_repr]
  simp only [mul_left_comm _ a, ← Finset.mul_sum, mul_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Derivative of every actual translation coefficient along an arbitrary
curve with a specified original coordinate tangent. -/
theorem original_translation_coefficient_hasDerivAt
    (V : ObservationModule G) (b : Basis iota ℝ V.space) (coord : G → sigma → ℝ)
    (T : iota → iota → MvPolynomial sigma ℚ)
    (hT : ∀ g j i, b.equivFun (observationTranslate V g (b j)) i = MvPolynomial.aeval (coord g) (T i j))
    (c : sigma → ℚ) (gamma : ℝ → G) (v : sigma → ℝ)
    (hc : coord (gamma 0) = fun s => (c s : ℝ))
    (hv : ∀ s, HasDerivAt (fun t => coord (gamma t) s) (v s) 0)
    (F : V.space) (i : iota) :
    HasDerivAt (fun t => b.equivFun (observationTranslate V (gamma t) F) i)
      (b.equivFun (observationCoordinateDifferential V b
        (fun i j s => MvPolynomial.eval c (MvPolynomial.pderiv s (T i j))) v F) i) 0 := by
  classical
  have hlin (t : ℝ) : b.equivFun (observationTranslate V (gamma t) F) i =
      ∑ j, b.equivFun F j * MvPolynomial.aeval (coord (gamma t)) (T i j) := by
    have he := congrArg (fun Q => b.equivFun (observationTranslate V (gamma t) Q) i)
      (b.sum_equivFun F)
    simpa only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hT] using he.symm
  have hh := HasDerivAt.fun_sum (u := Finset.univ) fun j _ =>
    (rational_polynomial_derivative_at_rational (T i j) (fun t => coord (gamma t)) c v 0 hc hv).const_mul
      (b.equivFun F j)
  convert! hh using 1
  · funext t
    exact hlin t
  · simp only [observation_coordinate_differential_repr, mul_comm]

set_option backward.isDefEq.respectTransparency false in
/-- The same operator differentiates the actual original function at
every original group point; no coefficient or evaluation response is
substituted for the original observation. -/
theorem original_translation_pointwise_hasDerivAt
    (V : ObservationModule G) (b : Basis iota ℝ V.space) (coord : G → sigma → ℝ)
    (T : iota → iota → MvPolynomial sigma ℚ)
    (hT : ∀ g j i, b.equivFun (observationTranslate V g (b j)) i = MvPolynomial.aeval (coord g) (T i j))
    (c : sigma → ℚ) (gamma : ℝ → G) (v : sigma → ℝ)
    (hc : coord (gamma 0) = fun s => (c s : ℝ))
    (hv : ∀ s, HasDerivAt (fun t => coord (gamma t) s) (v s) 0)
    (F : V.space) (u : G) :
    HasDerivAt (fun t => F (gamma t * u))
      (observationCoordinateDifferential V b
        (fun i j s => MvPolynomial.eval c (MvPolynomial.pderiv s (T i j))) v F u) 0 := by
  classical
  have hh := HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
    (original_translation_coefficient_hasDerivAt V b coord T hT c gamma v hc hv F i).mul_const (b i u)
  convert! hh using 1
  · funext t
    exact observation_evaluation_basis V b (observationTranslate V (gamma t) F) u
  · exact observation_evaluation_basis V b _ u

set_option backward.isDefEq.respectTransparency false in
/-- Differentiating actual translation differences preserves their
membership in a lower flag space. Closedness is derived from finite
dimension after mapping the original subspace into its basis coordinates. -/
theorem observation_coordinate_differential_lowers
    (V : ObservationModule G) (b : Basis iota ℝ V.space) (coord : G ≃ (sigma → ℝ))
    (T : iota → iota → MvPolynomial sigma ℚ)
    (hT : ∀ g j i, b.equivFun (observationTranslate V g (b j)) i = MvPolynomial.aeval (coord g) (T i j))
    (c : sigma → ℚ) (hc : coord 1 = fun s => (c s : ℝ))
    (U U' : Submodule ℝ V.space)
    (hdrop : ∀ g (F : V.space), F ∈ U → observationTranslate V g F - F ∈ U')
    (v : sigma → ℝ) (F : V.space) (hF : F ∈ U) :
    observationCoordinateDifferential V b
      (fun i j s => MvPolynomial.eval c (MvPolynomial.pderiv s (T i j))) v F ∈ U' := by
  let gamma : ℝ → G := fun t => coord.symm (fun s => (c s : ℝ) + t * v s)
  have hg0 : gamma 0 = 1 := by
    apply coord.injective
    simp [gamma, hc]
  have hcurve : ∀ s, HasDerivAt (fun t => coord (gamma t) s) (v s) 0 := by
    intro s
    simp only [gamma, Equiv.apply_symm_apply]
    convert! ((hasDerivAt_id 0).mul_const (v s)).const_add (c s : ℝ) using 1
    simp
  let A := fun i j s => MvPolynomial.eval c (MvPolynomial.pderiv s (T i j))
  let D := observationCoordinateDifferential V b A v
  have hd : HasDerivAt (fun t => b.equivFun (observationTranslate V (gamma t) F))
      (b.equivFun (D F)) 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    exact original_translation_coefficient_hasDerivAt V b coord T hT c gamma v
      (by rw [hg0]; exact hc) hcurve F i
  let S : Submodule ℝ (iota → ℝ) := U'.map b.equivFun.toLinearMap
  have hmem : b.equivFun (D F) ∈ S := by
    apply S.closed_of_finiteDimensional.mem_of_tendsto hd.tendsto_slope_zero
    apply Filter.Eventually.of_forall
    intro t
    apply S.smul_mem
    simp only [zero_add, hg0, observationTranslate_one, ← map_sub]
    exact Submodule.mem_map.mpr ⟨observationTranslate V (gamma t) F - F, hdrop _ F hF, rfl⟩
  obtain ⟨Q, hQ, he⟩ := Submodule.mem_map.mp hmem
  have hQD : Q = D F := b.equivFun.injective he
  simpa only [hQD] using hQ

end GMZP0
