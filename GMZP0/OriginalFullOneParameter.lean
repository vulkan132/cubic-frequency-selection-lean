import GMZP0.OriginalBaseOneParameter
import GMZP0.OriginalOneParameterLift

/-! Every full original coordinate tangent now has a constructed, unique
actual observation-group subgroup. All rational data and the entire
integer lattice are chosen before all real tangents and observations. -/
noncomputable section
open Module
namespace GMZP0

set_option backward.isDefEq.respectTransparency false in
/-- A full original coordinate tangent gives both the actual base
tangent and the pointwise derivative of the unchanged original fiber. -/
theorem observation_full_coordinate_tangent_components
    {G sigma iota : Type*} [Group G] [TopologicalSpace G] [Fintype sigma] [Fintype iota]
    (V : ObservationModule G) (coord : G ≃ₜ (sigma → ℝ)) (b : Basis iota ℝ V.space)
    (eta : ℝ → ObservationGroup V) (v : sigma → ℝ) (Q : V.space)
    (hfull : HasDerivAt (fun t => observationFullCoordinates V coord b (eta t))
      (Sum.elim v (b.equivFun Q)) 0) :
    (∀ s, HasDerivAt (fun t => coord (eta t).base s) (v s) 0) ∧
      (∀ u, HasDerivAt (fun t => (eta t).obs u) (Q u) 0) := by
  classical
  have hh := hasDerivAt_pi.mp hfull
  constructor
  · intro s
    simpa only [observation_full_coordinates_base, Sum.elim_inl] using hh (Sum.inl s)
  · intro u
    have hd (i : iota) : HasDerivAt (fun t => b.equivFun (eta t).obs i) (b.equivFun Q i) 0 := by
      simpa only [observation_full_coordinates_fiber, Sum.elim_inr] using hh (Sum.inr i)
    have hs := HasDerivAt.fun_sum (u := Finset.univ) fun i _ => (hd i).mul_const (b i u)
    convert! hs using 1
    · funext t
      exact observation_evaluation_basis V b (eta t).obs u
    · exact observation_evaluation_basis V b Q u

/-- The literal original presentation constructs all base paths and
their unique H lifts. Neither base-path existence nor a lift formula is
supplied. Uniqueness ranges over every actual H subgroup with the same
full initial coordinate tangent, without assuming the same base path. -/
theorem original_integral_basis_full_one_parameter
    {G iota : Type*} [Group G] [TopologicalSpace G] [Fintype iota] {m : ℕ}
    (V : ObservationModule G) (Gamma : Subgroup G)
    (coord : G ≃ₜ (Fin m → ℝ)) (b : Basis iota ℝ V.space)
    (hint : ∀ gamma : Gamma, ∃ z : Fin m → ℤ, coord gamma = fun i => (z i : ℝ))
    (hcover : ∀ z : Fin m → ℤ, ∃ gamma : Gamma, coord gamma = fun i => (z i : ℝ))
    (p : Fin m → MvPolynomial (Fin m ⊕ Fin m) ℚ)
    (hjoint : ∀ g h i, coord (g * h) i = MvPolynomial.aeval (Sum.elim (coord g) (coord h)) (p i))
    (q : G → Fin m → MvPolynomial (Fin m) ℝ)
    (htri : ∀ g u i, coord (g * u) i = coord u i + MvPolynomial.aeval (coord u) (q g i))
    (hlow : ∀ g i d, d ∈ (q g i).support → ∀ j ∈ d.support, j.val < i.val)
    (P : iota → MvPolynomial (Fin m) ℚ)
    (hP : ∀ j g, b j g = MvPolynomial.aeval (coord g) (P j)) :
    letI := Algebra.restrictScalars ℚ ℝ (Module.End ℝ V.space)
    ∃ c : Fin m → ℚ, ∃ d : ℕ,
      ∃ bZ : Basis (Fin d) ℤ (observationIntegerLattice V Gamma),
      ∃ bR : Basis (Fin d) ℝ V.space, ∃ B : Fin d → MvPolynomial (Fin m) ℚ,
      ∃ K : ℕ, ∃ A : Fin d → Fin d → Fin m → ℚ, ∃ E L : Polynomial ℚ,
        coord 1 = (fun i => (c i : ℝ)) ∧ (∀ i, bR i = (bZ i).val) ∧
        (∀ i g, bR i g = MvPolynomial.aeval (coord g) (B i)) ∧ 0 < K ∧
        (∀ v : Fin m → ℝ, (observationCoordinateDifferential V bR A v) ^ K = 0) ∧
        (∀ v : Fin m → ℝ,
          Polynomial.aeval (observationCoordinateDifferential V bR A v) E =
            nilpotentFiberMatrix K (observationCoordinateDifferential V bR A v) ∧
          Polynomial.aeval (observationCoordinateDifferential V bR A v) L *
            Polynomial.aeval (observationCoordinateDifferential V bR A v) E = 1 ∧
          Polynomial.aeval (observationCoordinateDifferential V bR A v) E *
            Polynomial.aeval (observationCoordinateDifferential V bR A v) L = 1) ∧
        (∀ v : Fin m → ℝ,
          let gamma := originalBaseOneParameter coord.toEquiv p c v
          gamma 0 = 1 ∧ (∀ s t, gamma (s + t) = gamma s * gamma t) ∧
          (∀ i, HasDerivAt (fun t => coord (gamma t) i) (v i) 0) ∧
          (∀ i, coord (gamma 1) i = MvPolynomial.aeval v
            ((rationalTriangularFlowPolynomial (originalVelocityPolynomial p c) c i).eval 1)) ∧
          (∀ t, observationTranslate V (gamma t) =
            ∑ j ∈ Finset.range K, (t ^ j / (j.factorial : ℝ)) •
              (observationCoordinateDifferential V bR A v) ^ j) ∧
          (∀ Q : V.space,
            observationOneParameterLift V gamma K (observationCoordinateDifferential V bR A v) Q 0 = 1 ∧
            (∀ s t, observationOneParameterLift V gamma K (observationCoordinateDifferential V bR A v) Q (s + t) =
              observationOneParameterLift V gamma K (observationCoordinateDifferential V bR A v) Q s *
                observationOneParameterLift V gamma K (observationCoordinateDifferential V bR A v) Q t) ∧
            HasDerivAt (fun t => observationFullCoordinates V coord bR
              (observationOneParameterLift V gamma K (observationCoordinateDifferential V bR A v) Q t))
              (Sum.elim v (bR.equivFun Q)) 0 ∧
            observationOneParameterLift V gamma K (observationCoordinateDifferential V bR A v) Q 1 =
              ⟨gamma 1, Polynomial.aeval (observationCoordinateDifferential V bR A v) E Q⟩ ∧
            (∀ eta : ℝ → ObservationGroup V,
              (∀ s t, eta (s + t) = eta s * eta t) →
              HasDerivAt (fun t => observationFullCoordinates V coord bR (eta t))
                (Sum.elim v (bR.equivFun Q)) 0 →
              ∀ t, eta t = observationOneParameterLift V gamma K
                (observationCoordinateDifferential V bR A v) Q t))) := by
  let := Algebra.restrictScalars ℚ ℝ (Module.End ℝ V.space)
  obtain ⟨z, hz⟩ := hint ⟨1, Gamma.one_mem⟩
  let c : Fin m → ℚ := fun i => (z i : ℚ)
  have hc : coord 1 = fun i => (c i : ℝ) := by
    simpa only [c, Rat.cast_intCast] using hz
  obtain ⟨d, bZ, bR, B, K, A, E, L, hcompat, hB, hK, hpow, hpoly, hpaths⟩ :=
    original_integral_basis_one_parameter_lift V Gamma coord b hint hcover p hjoint q htri hlow P hP
  refine ⟨c, d, bZ, bR, B, K, A, E, L, hc, hcompat, hB, hK, hpow, hpoly, ?_⟩
  intro v
  let gamma := originalBaseOneParameter coord.toEquiv p c v
  have hadd := original_base_one_parameter_add coord.toEquiv p hjoint q htri hlow c hc v
  have hv := original_base_one_parameter_tangent coord.toEquiv p hjoint q htri hlow c hc v
  obtain ⟨hT, hLift⟩ := hpaths gamma v hadd hv
  refine ⟨original_base_one_parameter_zero coord.toEquiv p c hc v, hadd, hv,
    original_base_one_parameter_one coord.toEquiv p c v, hT, ?_⟩
  intro Q
  obtain ⟨h0, hm, hd, h1, hu⟩ := hLift Q
  refine ⟨h0, hm, hd, h1, ?_⟩
  intro eta heta hfull
  obtain ⟨hbase, hvertical⟩ := observation_full_coordinate_tangent_components V coord bR eta v Q hfull
  have hbaseadd (s t : ℝ) : (eta (s + t)).base = (eta s).base * (eta t).base := by
    exact congrArg ObservationGroup.base (heta s t)
  exact hu eta heta
    (original_base_one_parameter_unique coord.toEquiv p hjoint q htri hlow c hc v
      (fun t => (eta t).base) hbaseadd hbase) hvertical

end GMZP0
