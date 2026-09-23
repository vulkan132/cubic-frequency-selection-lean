import GMZP0.InfinitesimalNilpotent
import GMZP0.NilpotentFiberPolynomial
import Mathlib.Algebra.Algebra.RestrictScalars

/-! The actual original integer basis, rational differential, uniform
nilpotency exponent and fixed rational fiber polynomials are selected
together, before every tangent, curve and unrestricted original function.
This is not yet an identification of the actual Lie exponential. -/
noncomputable section
open Module MvPolynomial
namespace GMZP0

/-- All infinitesimal and fiber polynomial data are derived in one
compatible basis of the entire original integer-valued function lattice.
The original pointwise derivative is retained for every original curve,
observation and evaluation point. -/
theorem original_integral_basis_infinitesimal_fiber
    {G iota : Type*} [Group G] [Fintype iota] {m : ℕ}
    (V : ObservationModule G) (Gamma : Subgroup G)
    (coord : G ≃ (Fin m → ℝ)) (b : Basis iota ℝ V.space)
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
        (∀ (gamma : ℝ → G) (v : Fin m → ℝ), gamma 0 = 1 →
          (∀ s, HasDerivAt (fun t => coord (gamma t) s) (v s) 0) →
          ∀ (F : V.space) (u : G), HasDerivAt (fun t => F (gamma t * u))
            (observationCoordinateDifferential V bR A v F u) 0) := by
  let := Algebra.restrictScalars ℚ ℝ (Module.End ℝ V.space)
  obtain ⟨d, bZ, bR, B, hcompat, hB⟩ :=
    observation_compatible_rational_bases V Gamma b coord hint hcover P hP
  obtain ⟨K, hK, A, hpow, hder⟩ :=
    original_rational_infinitesimal_translation V Gamma coord bR hint hcover p hjoint q htri hlow B hB
  obtain ⟨E, L, hEL⟩ := uniform_nilpotent_fiber_polynomial_inverse
    (A := Module.End ℝ V.space) K
  exact ⟨d, bZ, bR, B, K, A, E, L, hcompat, hB, hK, hpow, fun v => hEL _ (hpow v), hder⟩

end GMZP0
