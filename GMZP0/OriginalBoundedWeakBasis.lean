import GMZP0.OriginalWeakBasis
import GMZP0.RationalPolynomialHeight

/-! One original structural presentation supplies bounded native weak
basis data and both rational coordinate arrays before all real inputs. -/
noncomputable section
open Module
open scoped Manifold ContDiff
namespace GMZP0

/-- The original structural assumptions construct one common bound for
the actual native weak basis, original lattice and both exponential/log
coordinate arrays. No bound is placed on original real observations. -/
theorem original_full_bounded_weak_basis
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
          LieGroup 𝓘(ℝ, (Fin m ⊕ Fin d) → ℝ) ∞ (ObservationGroup V) ∧
          ContMDiff 𝓘(ℝ, (Fin m ⊕ Fin d) → ℝ) 𝓘(ℝ, (Fin m ⊕ Fin d) → ℝ) ∞ logCoord.symm ∧
          ContMDiff 𝓘(ℝ, (Fin m ⊕ Fin d) → ℝ) 𝓘(ℝ, (Fin m ⊕ Fin d) → ℝ) ∞ logCoord) := by
  obtain ⟨c, d, bZ, bR, K, A, logCoord, S, T, C, den, hb, hK, hpow, htime,
      hS, hT, hzero, hden, hleft, hright, hlie, hnative, hsmooth⟩ :=
    original_full_native_exponential_and_lattice V Gamma coord b hint hcover p hjoint q htri hlow P hP
  let Q := max (originalWeakBasisHeight C den)
    (max (rationalPolynomialArrayBound S) (rationalPolynomialArrayBound T))
  have hweak := original_weak_basis_from_native_data (observationFullCoordinates V coord bR)
    (observationLatticeSubgroup V Gamma) logCoord C den hnative hlie.2 hden hleft hright
  have hSQ : rationalPolynomialArrayBound S ≤ Q := (le_max_left _ _).trans (le_max_right _ _)
  have hTQ : rationalPolynomialArrayBound T ≤ Q := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨d, bZ, bR, logCoord, S, T, Q, hb,
    original_weak_basis_bound_mono _ _ _ hweak (le_max_left _ _), hS, hT, hzero, ?_, ?_⟩
  · intro i
    have hs := (rational_polynomial_array_bounds S).2 i
    have ht := (rational_polynomial_array_bounds T).2 i
    exact ⟨hs.1.trans hSQ, ht.1.trans hTQ, fun e => ⟨(hs.2 e).trans hSQ, (ht.2 e).trans hTQ⟩⟩
  · let := (observationFullCoordinates V coord bR).isOpenEmbedding.singletonChartedSpace
    exact ⟨hlie.1, hsmooth⟩

end GMZP0
