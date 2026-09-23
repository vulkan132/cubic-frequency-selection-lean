import GMZP0.OriginalFullLieFiltration
import GMZP0.OriginalExponentialFiltration

/-! The original structural construction and the exponential-set/lattice
conclusions use a single selection of original bases and coordinates. -/
noncomputable section
open Module
open scoped Manifold ContDiff
namespace GMZP0
attribute [local instance] original_real_lie_native_smoothness

/-- The full original presentation supplies the actual exponential sets
and original-lattice spans, retaining every F63 witness and finite-depth
height clause. No integrated subgroup or group-series matching is assumed. -/
theorem original_full_exponential_lie_filtration
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
    ∃ d : ℕ, ∃ bZ : Basis (Fin d) ℤ (observationIntegerLattice V Gamma),
      ∃ bR : Basis (Fin d) ℝ V.space,
      ∃ logCoord : ObservationGroup V ≃ ((Fin m ⊕ Fin d) → ℝ),
      ∃ S T : (Fin m ⊕ Fin d) → MvPolynomial (Fin m ⊕ Fin d) ℚ, ∃ Q : ℕ,
        (∀ i, bR i = (bZ i).val) ∧
        OriginalWeakBasisBound (observationFullCoordinates V coord bR)
          (observationLatticeSubgroup V Gamma) logCoord Q ∧
        (∀ x i, observationFullCoordinates V coord bR (logCoord.symm x) i =
          MvPolynomial.aeval x (S i)) ∧
        (∀ a i, logCoord a i = MvPolynomial.aeval (observationFullCoordinates V coord bR a) (T i)) ∧
        logCoord 1 = 0 ∧
        (∀ i, (S i).totalDegree ≤ Q ∧ (T i).totalDegree ≤ Q ∧
          ∀ e, rationalHeight ((S i).coeff e) ≤ Q ∧ rationalHeight ((T i).coeff e) ≤ Q) ∧
        (letI := (observationFullCoordinates V coord bR).isOpenEmbedding.singletonChartedSpace;
          ∃ hLie : LieGroup 𝓘(ℝ, (Fin m ⊕ Fin d) → ℝ) ∞ (ObservationGroup V),
          letI := hLie;
          ContMDiff 𝓘(ℝ, (Fin m ⊕ Fin d) → ℝ) 𝓘(ℝ, (Fin m ⊕ Fin d) → ℝ) ∞ logCoord.symm ∧
          ContMDiff 𝓘(ℝ, (Fin m ⊕ Fin d) → ℝ) 𝓘(ℝ, (Fin m ⊕ Fin d) → ℝ) ∞ logCoord ∧
          (∀ n : ℕ, OriginalExponentialSubspaceData (observationLatticeSubgroup V Gamma) logCoord
            (LieModule.lowerCentralSeries ℝ
              (GroupLieAlgebra 𝓘(ℝ, (Fin m ⊕ Fin d) → ℝ) (ObservationGroup V))
              (GroupLieAlgebra 𝓘(ℝ, (Fin m ⊕ Fin d) → ℝ) (ObservationGroup V)) n).toSubmodule) ∧
          (∀ n : ℕ, RationalInBasis (originalTangentBasis (observationFullCoordinates V coord bR))
            (LieModule.lowerCentralSeries ℝ
              (GroupLieAlgebra 𝓘(ℝ, (Fin m ⊕ Fin d) → ℝ) (ObservationGroup V))
              (GroupLieAlgebra 𝓘(ℝ, (Fin m ⊕ Fin d) → ℝ) (ObservationGroup V)) n).toSubmodule) ∧
          ∀ r : ℕ, ∃ H : ℕ, 2 < H ∧ ∀ n ≤ r,
            ∃ J : Set (GroupLieAlgebra 𝓘(ℝ, (Fin m ⊕ Fin d) → ℝ) (ObservationGroup V)), J.Finite ∧
              ∃ bN : Basis J ℝ (LieModule.lowerCentralSeries ℝ
                (GroupLieAlgebra 𝓘(ℝ, (Fin m ⊕ Fin d) → ℝ) (ObservationGroup V))
                (GroupLieAlgebra 𝓘(ℝ, (Fin m ⊕ Fin d) → ℝ) (ObservationGroup V)) n).toSubmodule,
                ∀ j : J, ∃ a : (Fin m ⊕ Fin d) → ℚ, ∀ i,
                  (originalTangentBasis (observationFullCoordinates V coord bR)).repr
                    (bN j : GroupLieAlgebra 𝓘(ℝ, (Fin m ⊕ Fin d) → ℝ) (ObservationGroup V)) i =
                      (a i : ℝ) ∧ rationalHeight (a i) ≤ H) := by
  obtain ⟨d, bZ, bR, logCoord, S, T, Q, hb, hweak, hS, hT, hzero, hbounds, hLieData⟩ :=
    original_full_bounded_lie_filtration V Gamma coord b hint hcover p hjoint q htri hlow P hP
  refine ⟨d, bZ, bR, logCoord, S, T, Q, hb, hweak, hS, hT, hzero, hbounds, ?_⟩
  let := (observationFullCoordinates V coord bR).isOpenEmbedding.singletonChartedSpace
  obtain ⟨hLie, hExp, hLog, hrat, hbases⟩ := hLieData
  let := hLie
  exact ⟨hLie, hExp, hLog,
    original_weak_basis_lower_central_exponential_data (observationFullCoordinates V coord bR)
      (observationLatticeSubgroup V Gamma) logCoord Q hweak S T hS hT hLie,
    hrat, hbases⟩

end GMZP0
