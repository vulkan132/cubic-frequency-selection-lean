import GMZP0.ObservationOneParameter
import GMZP0.OriginalInfinitesimalFiber

/-! The same constructed full original integer basis and rational
fiber polynomials give the unique actual H lift over every specified
base one-parameter subgroup with its original coordinate tangent.
Existence of those base subgroups for every tangent is not a premise
silently supplied by the word exponential. -/
noncomputable section
open Module MvPolynomial
namespace GMZP0

/-- The original structural data select all rational basis, differential
and inverse data before every genuine base path, tangent and original
vertical observation. The explicit lifted path has the original group
law, full coordinate tangent and rational time-one fiber, and is unique
over the same entire base path. -/
theorem original_integral_basis_one_parameter_lift
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
    ∃ d : ℕ, ∃ bZ : Basis (Fin d) ℤ (observationIntegerLattice V Gamma),
      ∃ bR : Basis (Fin d) ℝ V.space, ∃ B : Fin d → MvPolynomial (Fin m) ℚ,
      ∃ K : ℕ, ∃ A : Fin d → Fin d → Fin m → ℚ, ∃ E L : Polynomial ℚ,
        (∀ i, bR i = (bZ i).val) ∧
        (∀ i g, bR i g = MvPolynomial.aeval (coord g) (B i)) ∧ 0 < K ∧
        (∀ v : Fin m → ℝ, (observationCoordinateDifferential V bR A v) ^ K = 0) ∧
        (∀ v : Fin m → ℝ,
          Polynomial.aeval (observationCoordinateDifferential V bR A v) E =
            nilpotentFiberMatrix K (observationCoordinateDifferential V bR A v) ∧
          Polynomial.aeval (observationCoordinateDifferential V bR A v) L *
            Polynomial.aeval (observationCoordinateDifferential V bR A v) E = 1 ∧
          Polynomial.aeval (observationCoordinateDifferential V bR A v) E *
            Polynomial.aeval (observationCoordinateDifferential V bR A v) L = 1) ∧
        (∀ (gamma : ℝ → G) (v : Fin m → ℝ),
          (∀ s t, gamma (s + t) = gamma s * gamma t) →
          (∀ s, HasDerivAt (fun t => coord (gamma t) s) (v s) 0) →
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
              (∀ s t, eta (s + t) = eta s * eta t) → (∀ t, (eta t).base = gamma t) →
              (∀ u, HasDerivAt (fun t => (eta t).obs u) (Q u) 0) →
              ∀ t, eta t = observationOneParameterLift V gamma K (observationCoordinateDifferential V bR A v) Q t))) := by
  let := Algebra.restrictScalars ℚ ℝ (Module.End ℝ V.space)
  obtain ⟨d, bZ, bR, B, K, A, E, L, hcompat, hB, hK, hpow, hpoly, hder⟩ :=
    original_integral_basis_infinitesimal_fiber V Gamma coord.toEquiv b hint hcover p hjoint q htri hlow P hP
  refine ⟨d, bZ, bR, B, K, A, E, L, hcompat, hB, hK, hpow, hpoly, ?_⟩
  intro gamma v hadd hv
  have hd := hder gamma v (one_parameter_zero gamma hadd) hv
  refine ⟨one_parameter_translation_finite_series V gamma hadd _ K (hpow v) hd, ?_⟩
  intro Q
  refine ⟨observation_one_parameter_lift_zero V gamma hadd K _ Q,
    observation_one_parameter_lift_add V gamma hadd K _ (hpow v) hd Q,
    observation_one_parameter_lift_coordinate_tangent V coord bR gamma hadd v hv K _ (hpow v) hd Q,
    ?_, ?_⟩
  · rw [(hpoly v).1]
    exact observation_one_parameter_lift_one V gamma K _ (hpow v) Q
  · intro eta heta hbase hvertical
    exact observation_one_parameter_lift_unique V gamma hadd K _ (hpow v) hd Q eta heta hbase hvertical

end GMZP0
