import GMZP0.RationalEvaluationRecovery

/-! Every actual integer-valued observation has rational coordinates in
the original rational basis. Hence an actual integer lattice basis yields
compatible real and rational polynomial bases, without supplying them. -/
noncomputable section
open Module MvPolynomial
namespace GMZP0
variable {G sigma iota : Type*} [Group G] [Fintype iota]

/-- Integer values at the original determining points force rational
coordinates in the given rational polynomial basis. -/
theorem observation_integer_coordinates_rational
    (V : ObservationModule G) (Gamma : Subgroup G)
    (b : Basis iota ℝ V.space) (coord : G → sigma → ℝ)
    (hint : ∀ gamma : Gamma, ∃ z : sigma → ℤ, coord gamma = fun i => (z i : ℝ))
    (hcover : ∀ z : sigma → ℤ, ∃ gamma : Gamma, coord gamma = fun i => (z i : ℝ))
    (P : iota → MvPolynomial sigma ℚ)
    (hP : ∀ j g, b j g = MvPolynomial.aeval (coord g) (P j))
    (F : observationIntegerLattice V Gamma) :
    ∃ c : iota → ℚ, ∀ i, b.equivFun F.val i = (c i : ℝ) := by
  obtain ⟨n, _, u, _, _, A, hA⟩ :=
    observation_rational_recovery_on_integer_points V Gamma b coord hint hcover P hP
  choose v hv using fun k => F.property (u k)
  refine ⟨fun i => ∑ k, A i k * (v k : ℚ), ?_⟩
  intro i
  rw [hA]
  simp only [hv, Rat.cast_sum, Rat.cast_mul, Rat.cast_intCast]

/-- Every element of the full original integer-valued lattice is an
actual rational coordinate polynomial, not merely a real polynomial. -/
theorem observation_integer_rational_polynomial
    (V : ObservationModule G) (Gamma : Subgroup G)
    (b : Basis iota ℝ V.space) (coord : G → sigma → ℝ)
    (hint : ∀ gamma : Gamma, ∃ z : sigma → ℤ, coord gamma = fun i => (z i : ℝ))
    (hcover : ∀ z : sigma → ℤ, ∃ gamma : Gamma, coord gamma = fun i => (z i : ℝ))
    (P : iota → MvPolynomial sigma ℚ)
    (hP : ∀ j g, b j g = MvPolynomial.aeval (coord g) (P j))
    (F : observationIntegerLattice V Gamma) :
    ∃ Q : MvPolynomial sigma ℚ, ∀ g, F.val g = MvPolynomial.aeval (coord g) Q := by
  classical
  obtain ⟨c, hc⟩ := observation_integer_coordinates_rational V Gamma b coord hint hcover P hP F
  refine ⟨∑ j, C (c j) * P j, ?_⟩
  intro g
  rw [observation_evaluation_basis V b F.val g]
  simp [hc, hP]

/-- The original rational data construct an integer lattice basis and a
compatible actual real basis whose functions remain rational polynomials.
No bounded-height or adapted-flag conclusion is inferred here. -/
theorem observation_compatible_rational_bases
    (V : ObservationModule G) (Gamma : Subgroup G)
    (b : Basis iota ℝ V.space) (coord : G → sigma → ℝ)
    (hint : ∀ gamma : Gamma, ∃ z : sigma → ℤ, coord gamma = fun i => (z i : ℝ))
    (hcover : ∀ z : sigma → ℤ, ∃ gamma : Gamma, coord gamma = fun i => (z i : ℝ))
    (P : iota → MvPolynomial sigma ℚ)
    (hP : ∀ j g, b j g = MvPolynomial.aeval (coord g) (P j)) :
    ∃ d : ℕ, ∃ bZ : Basis (Fin d) ℤ (observationIntegerLattice V Gamma),
      ∃ bR : Basis (Fin d) ℝ V.space, ∃ Q : Fin d → MvPolynomial sigma ℚ,
        (∀ i, bR i = (bZ i).val) ∧ ∀ i g, bR i g = MvPolynomial.aeval (coord g) (Q i) := by
  let : FiniteDimensional ℝ V.space := b.finiteDimensional_of_finite
  have hsep := observation_integer_points_separate V Gamma coord hcover
    (observation_representatives_of_rational_basis V b coord P hP)
  have hfull := observation_integer_span_top V Gamma b coord hint P hP
  obtain ⟨d, ⟨bZ⟩⟩ := observation_integer_basis V Gamma hsep
  let bR := observationRealBasis V Gamma bZ hsep hfull
  choose Q hQ using fun i => observation_integer_rational_polynomial V Gamma b coord hint hcover P hP (bZ i)
  refine ⟨d, bZ, bR, Q, observationRealBasis_apply V Gamma bZ hsep hfull, ?_⟩
  intro i g
  rw [observationRealBasis_apply]
  exact hQ i g

end GMZP0
