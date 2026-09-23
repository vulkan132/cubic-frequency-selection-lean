import GMZP0.OneParameterFiber

/-! Construct and uniquely identify the actual observation-group
one-parameter lift over a specified genuine base subgroup. No base
exponential is assumed to exist merely from a coordinate formula. -/
noncomputable section
open Module
namespace GMZP0
variable {G : Type*} [Group G]

/-- The lifted path in the original group with its original fiber. -/
def observationOneParameterLift (V : ObservationModule G) (gamma : ℝ → G)
    (K : ℕ) (D : Module.End ℝ V.space) (Q : V.space) (t : ℝ) : ObservationGroup V :=
  ⟨gamma t, nilpotentFiberPath K D t Q⟩

/-- The lifted path starts at the actual group identity. -/
theorem observation_one_parameter_lift_zero
    (V : ObservationModule G) (gamma : ℝ → G)
    (hadd : ∀ s t, gamma (s + t) = gamma s * gamma t)
    (K : ℕ) (D : Module.End ℝ V.space) (Q : V.space) :
    observationOneParameterLift V gamma K D Q 0 = 1 := by
  apply ObservationGroup.ext
  · exact one_parameter_zero gamma hadd
  · change nilpotentFiberPath K D 0 Q = 0
    rw [nilpotent_fiber_path_zero]
    rfl

/-- The explicit lift satisfies the actual H multiplication at every
pair of real parameters, including the original right pullback order. -/
theorem observation_one_parameter_lift_add
    (V : ObservationModule G) (gamma : ℝ → G)
    (hadd : ∀ s t, gamma (s + t) = gamma s * gamma t)
    (K : ℕ) (D : Module.End ℝ V.space) (hD : D ^ K = 0)
    (hder : ∀ (F : V.space) (u : G),
      HasDerivAt (fun t => F (gamma t * u)) (D F u) 0)
    (Q : V.space) (s t : ℝ) :
    observationOneParameterLift V gamma K D Q (s + t) =
      observationOneParameterLift V gamma K D Q s * observationOneParameterLift V gamma K D Q t := by
  apply ObservationGroup.ext
  · exact hadd s t
  · exact nilpotent_fiber_path_cocycle V gamma hadd D K hD hder Q s t

/-- The original vertical tangent is exactly Q, pointwise on all of G. -/
theorem observation_one_parameter_lift_vertical_tangent
    (V : ObservationModule G) (gamma : ℝ → G)
    (hadd : ∀ s t, gamma (s + t) = gamma s * gamma t)
    (K : ℕ) (D : Module.End ℝ V.space) (hD : D ^ K = 0)
    (hder : ∀ (F : V.space) (u : G),
      HasDerivAt (fun t => F (gamma t * u)) (D F u) 0)
    (Q : V.space) (u : G) :
    HasDerivAt (fun t => (observationOneParameterLift V gamma K D Q t).obs u) (Q u) 0 := by
  simpa only [one_parameter_zero gamma hadd, one_mul, observationOneParameterLift] using
    nilpotent_fiber_path_hasDerivAt V gamma hadd D K hD hder Q u 0

set_option backward.isDefEq.respectTransparency false in
/-- Every actual H subgroup path propagates its original vertical
derivative at zero according to the original right semidirect law. -/
theorem observation_one_parameter_fiber_hasDerivAt
    (V : ObservationModule G) (eta : ℝ → ObservationGroup V)
    (hadd : ∀ s t, eta (s + t) = eta s * eta t) (Q : V.space)
    (hder : ∀ u, HasDerivAt (fun t => (eta t).obs u) (Q u) 0)
    (u : G) (t : ℝ) :
    HasDerivAt (fun s => (eta s).obs u) (Q ((eta t).base * u)) t := by
  have hz : HasDerivAt
      (fun s => (eta s).obs ((eta t).base * u) + (eta t).obs u)
      (Q ((eta t).base * u)) (t - t) := by
    convert! (hder ((eta t).base * u)).add_const ((eta t).obs u) using 1
    simp
  have hh := hz.comp_sub_const t t
  convert! hh using 1
  funext s
  have he := congrArg (fun a : ObservationGroup V => a.obs u) (hadd (s - t) t)
  simpa only [sub_add_cancel, observation_mul_obs] using he

/-- The constructed lift is the unique actual H subgroup path over
the same entire original base path with the specified vertical tangent. -/
theorem observation_one_parameter_lift_unique
    (V : ObservationModule G) (gamma : ℝ → G)
    (hadd : ∀ s t, gamma (s + t) = gamma s * gamma t)
    (K : ℕ) (D : Module.End ℝ V.space) (hD : D ^ K = 0)
    (hder : ∀ (F : V.space) (u : G),
      HasDerivAt (fun t => F (gamma t * u)) (D F u) 0)
    (Q : V.space) (eta : ℝ → ObservationGroup V)
    (heta : ∀ s t, eta (s + t) = eta s * eta t)
    (hbase : ∀ t, (eta t).base = gamma t)
    (hvertical : ∀ u, HasDerivAt (fun t => (eta t).obs u) (Q u) 0) :
    ∀ t, eta t = observationOneParameterLift V gamma K D Q t := by
  intro t
  apply ObservationGroup.ext
  · exact hbase t
  · apply Subtype.ext
    funext u
    apply real_functions_eq_of_derivative_and_initial
      (fun s => (eta s).obs u) (fun s => nilpotentFiberPath K D s Q u)
      (fun s => Q (gamma s * u))
    · intro s
      simpa only [hbase] using observation_one_parameter_fiber_hasDerivAt V eta heta Q hvertical u s
    · exact nilpotent_fiber_path_hasDerivAt V gamma hadd D K hD hder Q u
    · rw [one_parameter_zero eta heta, nilpotent_fiber_path_zero]
      rfl

/-- The time-one value of the actual constructed path has precisely
the factorial fiber polynomial appearing in the manuscript. -/
theorem observation_one_parameter_lift_one
    (V : ObservationModule G) (gamma : ℝ → G)
    (K : ℕ) (D : Module.End ℝ V.space) (hD : D ^ K = 0) (Q : V.space) :
    letI := Algebra.restrictScalars ℚ ℝ (Module.End ℝ V.space)
    observationOneParameterLift V gamma K D Q 1 = ⟨gamma 1, nilpotentFiberMatrix K D Q⟩ := by
  let := Algebra.restrictScalars ℚ ℝ (Module.End ℝ V.space)
  apply ObservationGroup.ext
  · rfl
  · change nilpotentFiberPath K D 1 Q = nilpotentFiberMatrix K D Q
    rw [nilpotent_fiber_path_one K D hD]

set_option backward.isDefEq.respectTransparency false in
/-- Finite actual evaluation recovery carries pointwise derivatives
back to the original basis coefficients, without changing the functions. -/
theorem observation_curve_coefficient_hasDerivAt
    {iota : Type*} [Fintype iota]
    (V : ObservationModule G) (b : Basis iota ℝ V.space)
    (F : ℝ → V.space) (Q : V.space)
    (hpoint : ∀ u, HasDerivAt (fun t => F t u) (Q u) 0) (i : iota) :
    HasDerivAt (fun t => b.equivFun (F t) i) (b.equivFun Q i) 0 := by
  classical
  obtain ⟨n, _, u, A, hA⟩ := observation_coefficients_from_finite_values V b
  have hh := HasDerivAt.fun_sum (u := Finset.univ) fun k _ =>
    (hpoint (u k)).const_mul (A i k)
  convert! hh using 1
  · funext t
    exact hA (F t) i
  · exact hA Q i

/-- The complete original H coordinates of the constructed path have
the prescribed base tangent and the unchanged original fiber coefficients. -/
theorem observation_one_parameter_lift_coordinate_tangent
    {sigma iota : Type*} [TopologicalSpace G] [Fintype sigma] [Fintype iota]
    (V : ObservationModule G) (coord : G ≃ₜ (sigma → ℝ)) (b : Basis iota ℝ V.space)
    (gamma : ℝ → G) (hadd : ∀ s t, gamma (s + t) = gamma s * gamma t)
    (v : sigma → ℝ) (hv : ∀ s, HasDerivAt (fun t => coord (gamma t) s) (v s) 0)
    (K : ℕ) (D : Module.End ℝ V.space) (hD : D ^ K = 0)
    (hder : ∀ (F : V.space) (u : G),
      HasDerivAt (fun t => F (gamma t * u)) (D F u) 0)
    (Q : V.space) :
    HasDerivAt (fun t => observationFullCoordinates V coord b
      (observationOneParameterLift V gamma K D Q t)) (Sum.elim v (b.equivFun Q)) 0 := by
  apply hasDerivAt_pi.mpr
  intro s
  cases s with
  | inl s =>
    simpa only [observation_full_coordinates_base, observationOneParameterLift, Sum.elim_inl] using hv s
  | inr i =>
    simp only [observation_full_coordinates_fiber, Sum.elim_inr]
    exact observation_curve_coefficient_hasDerivAt V b
      (fun t => (observationOneParameterLift V gamma K D Q t).obs) Q
      (observation_one_parameter_lift_vertical_tangent V gamma hadd K D hD hder Q) i

end GMZP0
