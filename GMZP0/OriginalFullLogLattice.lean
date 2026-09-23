import GMZP0.OriginalFullLogarithm
import GMZP0.RationalLatticeSandwich
import GMZP0.RationalObservationLatticeCoordinates

/-! Both denominator inclusions for the actual full original H lattice,
using the constructed global time-one inverse in the same original bases.
The logarithmic lattice image is not assumed to be an additive subgroup. -/
noncomputable section
open Module
namespace GMZP0

/-- A literal rational full-coordinate equivalence with the correct origin
gives both inclusions for the entire original observation lattice. -/
theorem observation_full_logarithmic_lattice_sandwich
    {G sigma iota : Type*} [Group G] [TopologicalSpace G] [Fintype sigma] [Fintype iota]
    (V : ObservationModule G) (Gamma : Subgroup G) (coord : G ≃ₜ (sigma → ℝ))
    (hint : ∀ gamma : Gamma, ∃ z : sigma → ℤ, coord gamma = fun i => (z i : ℝ))
    (hcover : ∀ z : sigma → ℤ, ∃ gamma : Gamma, coord gamma = fun i => (z i : ℝ))
    (bZ : Basis iota ℤ (observationIntegerLattice V Gamma)) (bR : Basis iota ℝ V.space)
    (hb : ∀ i, bR i = (bZ i).val)
    (logCoord : ObservationGroup V ≃ ((sigma ⊕ iota) → ℝ))
    (S T : (sigma ⊕ iota) → MvPolynomial (sigma ⊕ iota) ℚ)
    (hS : ∀ x i, observationFullCoordinates V coord bR (logCoord.symm x) i =
      MvPolynomial.aeval x (S i))
    (hT : ∀ a i, logCoord a i = MvPolynomial.aeval (observationFullCoordinates V coord bR a) (T i))
    (hzero : logCoord 1 = 0) :
    ∃ den : ℕ, 0 < den ∧
      (∀ z : (sigma ⊕ iota) → ℤ, ∃ gamma : observationLatticeSubgroup V Gamma,
        ∀ i, logCoord gamma i = (den : ℝ) * (z i : ℝ)) ∧
      (∀ gamma : observationLatticeSubgroup V Gamma, ∃ z : (sigma ⊕ iota) → ℤ,
        ∀ i, (den : ℝ) * logCoord gamma i = z i) := by
  have hgrid := observation_lattice_full_integer_coordinates V Gamma coord hint hcover bZ bR hb
  apply original_logarithmic_lattice_sandwich (observationLatticeSubgroup V Gamma)
    (observationFullCoordinates V coord bR).toEquiv logCoord
    (fun gamma => (hgrid gamma).mp gamma.property) ?_ S T hS hT hzero
  intro z
  let a := (observationFullCoordinates V coord bR).symm (fun i => (z i : ℝ))
  have ha : observationFullCoordinates V coord bR a = fun i => (z i : ℝ) :=
    (observationFullCoordinates V coord bR).apply_symm_apply _
  exact ⟨⟨a, (hgrid a).mpr ⟨z, ha⟩⟩, ha⟩

/-- Original structural data alone supply the actual full time-one
equivalence, both rational arrays and one positive denominator for the
entire original H lattice. The fixed denominator precedes every integer
vector and every original lattice element. Lie-basis identification and
uniform heights are separate obligations. -/
theorem original_integral_basis_full_logarithmic_lattice
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
      ∃ den : ℕ,
        coord 1 = (fun i => (c i : ℝ)) ∧ (∀ i, bR i = (bZ i).val) ∧ 0 < K ∧
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
          ∀ i, (den : ℝ) * logCoord gamma i = z i) := by
  obtain ⟨c, d, bZ, bR, B, K, A, E, L, hc, hb, hB, hK, hpow, hpoly,
      logCoord, S, T, htime, hinv, hS, hT, hzero⟩ :=
    original_integral_basis_rational_log_coordinates V Gamma coord b hint hcover p hjoint q htri hlow P hP
  obtain ⟨den, hden, hleft, hright⟩ :=
    observation_full_logarithmic_lattice_sandwich V Gamma coord hint hcover bZ bR hb logCoord S T hS hT hzero
  exact ⟨c, d, bZ, bR, K, A, logCoord, S, T, den, hc, hb, hK, hpow,
    htime, hS, hT, hzero, hden, hleft, hright⟩

end GMZP0
