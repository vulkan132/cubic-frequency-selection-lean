import GMZP0.OriginalRationalLieBracket
import GMZP0.OriginalFullLogLattice

/-! The actual rational Lie basis, original time-one coordinates and
entire original H lattice in one and the same constructed fiber basis. -/
noncomputable section
open Module
open scoped Manifold ContDiff
namespace GMZP0

/-- The original structural presentation constructs an actual smooth Lie
group and a rational basis of its Mathlib Lie algebra in the very same
coordinates used for the full original time-one map and lattice. This
does not assert uniform heights or complete the exponential interface. -/
theorem original_full_rational_lie_basis_and_lattice
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
    ∃ c : Fin m → ℚ, ∃ d : ℕ,
      ∃ bZ : Basis (Fin d) ℤ (observationIntegerLattice V Gamma),
      ∃ bR : Basis (Fin d) ℝ V.space, ∃ K : ℕ,
      ∃ A : Fin d → Fin d → Fin m → ℚ,
      ∃ logCoord : ObservationGroup V ≃ ((Fin m ⊕ Fin d) → ℝ),
      ∃ S T : (Fin m ⊕ Fin d) → MvPolynomial (Fin m ⊕ Fin d) ℚ,
      ∃ C : (Fin m ⊕ Fin d) → (Fin m ⊕ Fin d) → (Fin m ⊕ Fin d) → ℚ,
      ∃ den : ℕ,
        (∀ i, bR i = (bZ i).val) ∧ 0 < K ∧
        (∀ v : Fin m → ℝ, (observationCoordinateDifferential V bR A v) ^ K = 0) ∧
        (∀ v Q, logCoord.symm (Sum.elim v (bR.equivFun Q)) =
          observationOneParameterLift V (originalBaseOneParameter coord.toEquiv p c v)
            K (observationCoordinateDifferential V bR A v) Q 1) ∧
        (∀ x i, observationFullCoordinates V coord bR (logCoord.symm x) i =
          MvPolynomial.aeval x (S i)) ∧
        (∀ a i, logCoord a i = MvPolynomial.aeval (observationFullCoordinates V coord bR a) (T i)) ∧
        logCoord 1 = 0 ∧ 0 < den ∧
        (∀ z : (Fin m ⊕ Fin d) → ℤ, ∃ gamma : observationLatticeSubgroup V Gamma,
          ∀ i, logCoord gamma i = (den : ℝ) * (z i : ℝ)) ∧
        (∀ gamma : observationLatticeSubgroup V Gamma, ∃ z : (Fin m ⊕ Fin d) → ℤ,
          ∀ i, (den : ℝ) * logCoord gamma i = z i) ∧
        (letI := (observationFullCoordinates V coord bR).isOpenEmbedding.singletonChartedSpace;
          LieGroup 𝓘(ℝ, (Fin m ⊕ Fin d) → ℝ) ∞ (ObservationGroup V) ∧
          ∀ i j k, (originalTangentBasis (observationFullCoordinates V coord bR)).repr
            ⁅originalTangentBasis (observationFullCoordinates V coord bR) i,
              originalTangentBasis (observationFullCoordinates V coord bR) j⁆ k = (C i j k : ℝ)) := by
  obtain ⟨c, d, bZ, bR, B, K, A, E, L, hc, hb, hB, hK, hpow, hpoly,
      logCoord, S, T, htime, hinv, hS, hT, hzero⟩ :=
    original_integral_basis_rational_log_coordinates V Gamma coord b hint hcover p hjoint q htri hlow P hP
  obtain ⟨den, hden, hleft, hright⟩ :=
    observation_full_logarithmic_lattice_sandwich V Gamma coord hint hcover bZ bR hb logCoord S T hS hT hzero
  obtain ⟨M, hM⟩ :=
    observation_group_rational_polynomial_presentation V Gamma coord bR hint hcover p hjoint B hB
  let cH : (Fin m ⊕ Fin d) → ℚ := Sum.elim c (fun _ => 0)
  have hcH : observationFullCoordinates V coord bR (1 : ObservationGroup V) =
      fun i => (cH i : ℝ) := by
    funext i
    cases i with
    | inl i => exact congrFun hc i
    | inr i =>
      change bR.equivFun (0 : V.space) i = ((0 : ℚ) : ℝ)
      simp
  refine ⟨c, d, bZ, bR, K, A, logCoord, S, T,
    originalRationalLieCoefficient M cH, den, hb, hK, hpow, htime,
    hS, hT, hzero, hden, hleft, hright, ?_⟩
  let := (observationFullCoordinates V coord bR).isOpenEmbedding.singletonChartedSpace
  exact ⟨original_observation_coordinate_lie_group V Gamma coord bR hint hcover p hjoint q htri hlow B hB,
    original_tangent_basis_rational (observationFullCoordinates V coord bR) M hM cH hcH⟩

end GMZP0
