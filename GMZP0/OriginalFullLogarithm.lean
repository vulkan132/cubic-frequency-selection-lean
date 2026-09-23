import GMZP0.ObservationTimeOneInverse
import GMZP0.ObservationLogCoordinates

/-! Both rational coordinate arrays of the actual full original H
time-one equivalence, in one constructed full integer/real basis. -/
noncomputable section
open Module
namespace GMZP0

/-- Original structural data construct literal rational coordinate arrays
for the full time-one map and its actual inverse. All choices precede all
unrestricted original tangents and observations; no coordinate formula,
base inverse, or fiber inverse is a new premise. -/
theorem original_integral_basis_rational_log_coordinates_with_subgroups
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
        ∃ logCoord : ObservationGroup V ≃ ((Fin m ⊕ Fin d) → ℝ),
        ∃ S T : (Fin m ⊕ Fin d) → MvPolynomial (Fin m ⊕ Fin d) ℚ,
          (∀ v Q, logCoord.symm (Sum.elim v (bR.equivFun Q)) =
            observationOneParameterLift V (originalBaseOneParameter coord.toEquiv p c v)
              K (observationCoordinateDifferential V bR A v) Q 1) ∧
          (∀ a : ObservationGroup V, logCoord a =
            Sum.elim (originalBaseLogarithm coord.toEquiv p c a.base)
              (bR.equivFun (Polynomial.aeval (observationCoordinateDifferential V bR A
                (originalBaseLogarithm coord.toEquiv p c a.base)) L a.obs))) ∧
          (∀ x i, observationFullCoordinates V coord bR (logCoord.symm x) i =
            MvPolynomial.aeval x (S i)) ∧
          (∀ a i, logCoord a i = MvPolynomial.aeval (observationFullCoordinates V coord bR a) (T i)) ∧
          logCoord 1 = 0 ∧
          (∀ v Q, OriginalCoordinateSubgroup (observationFullCoordinates V coord bR)
            (observationOneParameterLift V (originalBaseOneParameter coord.toEquiv p c v)
              K (observationCoordinateDifferential V bR A v) Q)
            (Sum.elim v (bR.equivFun Q))) := by
  let := Algebra.restrictScalars ℚ ℝ (Module.End ℝ V.space)
  obtain ⟨c, d, bZ, bR, B, K, A, E, L, hc, hb, hB, hK, hpow, hpoly, e, he, hi, he0, hsubgroups⟩ :=
    original_integral_basis_time_one_equiv_with_subgroups V Gamma coord b hint hcover p hjoint q htri hlow P hP
  let EG : Fin m → MvPolynomial (Fin m) ℚ :=
    fun i => (rationalTriangularFlowPolynomial (originalVelocityPolynomial p c) c i).eval 1
  let LG := originalBaseLogPolynomial p c
  let logCoord := observationLogCoordinates V bR e
  refine ⟨c, d, bZ, bR, B, K, A, E, L, hc, hb, hB, hK, hpow, hpoly, logCoord,
    observationForwardPolynomial EG A E, observationInversePolynomial LG A L, ?_, ?_, ?_, ?_, ?_, hsubgroups⟩
  · intro v Q
    change e (v, bR.equivFun.symm (bR.equivFun Q)) = _
    rw [bR.equivFun.symm_apply_apply, he]
  · intro a
    change Sum.elim (e.symm a).1 (bR.equivFun (e.symm a).2) = _
    rw [hi]
  · apply observation_forward_polynomial_eval V coord bR A E EG
      (fun v => originalBaseOneParameter coord.toEquiv p c v 1)
      (original_base_one_parameter_one coord.toEquiv p c) e
    intro v Q
    rw [he, observation_one_parameter_lift_one V _ K _ (hpow v), ← (hpoly v).1]
  · exact observation_inverse_polynomial_eval V coord bR A L LG
      (originalBaseLogarithm coord.toEquiv p c) (fun _ _ => rfl) e hi
  · have hz : e.symm 1 = (0, 0) := by rw [← he0, e.symm_apply_apply]
    change observationTangentCoordinates V bR (e.symm 1) = 0
    rw [hz]
    funext s
    cases s <;> simp [observationTangentCoordinates]

/-- Projection retaining the original F59 interface for existing consumers. -/
theorem original_integral_basis_rational_log_coordinates
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
        ∃ logCoord : ObservationGroup V ≃ ((Fin m ⊕ Fin d) → ℝ),
        ∃ S T : (Fin m ⊕ Fin d) → MvPolynomial (Fin m ⊕ Fin d) ℚ,
          (∀ v Q, logCoord.symm (Sum.elim v (bR.equivFun Q)) =
            observationOneParameterLift V (originalBaseOneParameter coord.toEquiv p c v)
              K (observationCoordinateDifferential V bR A v) Q 1) ∧
          (∀ a : ObservationGroup V, logCoord a =
            Sum.elim (originalBaseLogarithm coord.toEquiv p c a.base)
              (bR.equivFun (Polynomial.aeval (observationCoordinateDifferential V bR A
                (originalBaseLogarithm coord.toEquiv p c a.base)) L a.obs))) ∧
          (∀ x i, observationFullCoordinates V coord bR (logCoord.symm x) i =
            MvPolynomial.aeval x (S i)) ∧
          (∀ a i, logCoord a i = MvPolynomial.aeval (observationFullCoordinates V coord bR a) (T i)) ∧
          logCoord 1 = 0 := by
  obtain ⟨c, d, bZ, bR, B, K, A, E, L, hc, hb, hB, hK, hpow, hpoly,
      logCoord, S, T, htime, hinv, hS, hT, hzero, _⟩ :=
    original_integral_basis_rational_log_coordinates_with_subgroups V Gamma coord b
      hint hcover p hjoint q htri hlow P hP
  exact ⟨c, d, bZ, bR, B, K, A, E, L, hc, hb, hB, hK, hpow, hpoly,
    logCoord, S, T, htime, hinv, hS, hT, hzero⟩

end GMZP0
