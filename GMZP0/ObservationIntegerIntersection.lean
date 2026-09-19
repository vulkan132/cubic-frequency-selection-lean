import GMZP0.ObservationRealBasis

/-! Rationality of the actual difference space makes its integer intersection
span that same real space. Both the rational presentation and the actual
integer-coordinate condition are explicit. -/
noncomputable section
open Module MvPolynomial
namespace GMZP0
variable {G sigma iota : Type*} [Group G] [Fintype iota]

/-- A rational combination of the supplied actual rational polynomial basis has that
same rational polynomial representative, at every point of the original group. -/
theorem observation_rational_combination_evaluation (V : ObservationModule G)
    (b : Basis iota ℝ V.space) (coord : G → sigma → ℝ)
    (P : iota → MvPolynomial sigma ℚ)
    (hb : ∀ i g, b i g = MvPolynomial.aeval (coord g) (P i)) (q : iota → ℚ) (g : G) :
    rationalBasisVector b q g =
      MvPolynomial.aeval (coord g) (∑ i, MvPolynomial.C (q i) * P i) := by
  classical
  change observationEvaluation V g (rationalBasisVector b q) = _
  simp only [rationalBasisVector, map_sum, map_smul, observationEvaluation_apply,
    hb, map_mul, MvPolynomial.aeval_C, smul_eq_mul]
  rfl

/-- A positive integer multiple of every rational-coordinate vector belongs to the original V_Z. -/
theorem observation_rational_combination_integer_multiple (V : ObservationModule G)
    (Gamma : Subgroup G) (b : Basis iota ℝ V.space) (coord : G → sigma → ℝ)
    (hint : ∀ gamma : Gamma, ∃ z : sigma → ℤ, coord gamma = fun i => (z i : ℝ))
    (P : iota → MvPolynomial sigma ℚ)
    (hb : ∀ i g, b i g = MvPolynomial.aeval (coord g) (P i)) (q : iota → ℚ) :
    ∃ k : ℕ, 0 < k ∧ (k : ℝ) • rationalBasisVector b q ∈ observationIntegerLattice V Gamma := by
  classical
  exact observation_rational_integer_multiple V Gamma coord hint (rationalBasisVector b q)
    (∑ i, MvPolynomial.C (q i) * P i) (observation_rational_combination_evaluation V b coord P hb q)

/-- Rationality relative to the actual polynomial basis implies that W cap V_Z spans exactly W. -/
theorem observation_integer_intersection_real_span (V : ObservationModule G) (Gamma : Subgroup G)
    (b : Basis iota ℝ V.space) (coord : G → sigma → ℝ)
    (hint : ∀ gamma : Gamma, ∃ z : sigma → ℤ, coord gamma = fun i => (z i : ℝ))
    (P : iota → MvPolynomial sigma ℚ)
    (hb : ∀ i g, b i g = MvPolynomial.aeval (coord g) (P i))
    (hW : RationalInBasis b (observationDifferenceSpace V)) :
    Submodule.span ℝ {F : V.space | F ∈ observationDifferenceSpace V ∧
      F ∈ observationIntegerLattice V Gamma} = observationDifferenceSpace V := by
  classical
  obtain ⟨S, hS⟩ := hW
  apply le_antisymm
  · exact Submodule.span_le.mpr (fun _ h => h.1)
  · apply hS.le.trans
    apply Submodule.span_le.mpr
    rintro _ ⟨q, hq, rfl⟩
    have hqW : rationalBasisVector b q ∈ observationDifferenceSpace V := by
      rw [hS]
      exact Submodule.subset_span ⟨q, hq, rfl⟩
    obtain ⟨k, hk, hmem⟩ := observation_rational_combination_integer_multiple
      V Gamma b coord hint P hb q
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    let T := Submodule.span ℝ {F : V.space | F ∈ observationDifferenceSpace V ∧
      F ∈ observationIntegerLattice V Gamma}
    have hscaled : (k : ℝ) • rationalBasisVector b q ∈ T :=
      Submodule.subset_span ⟨(observationDifferenceSpace V).smul_mem _ hqW, hmem⟩
    have h := T.smul_mem (k : ℝ)⁻¹ hscaled
    change rationalBasisVector b q ∈ T
    simpa only [smul_smul, inv_mul_cancel₀ hk0, one_smul] using h

end GMZP0
