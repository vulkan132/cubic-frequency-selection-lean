import GMZP0.ObservationIntegerDiscrete
import Mathlib.Algebra.Module.Submodule.Lattice

/-! Full-lattice conclusions for the actual integer-valued observation subgroup,
derived from a literal rational polynomial basis and integer-coordinate coverage.
Discreteness and real spanning are conclusions, never presentation fields. -/
noncomputable section
open Module
namespace GMZP0
variable {G sigma iota : Type*} [Group G]

/-- The original integer-valued subgroup regarded as an actual integer submodule. -/
def observationIntegerLattice (V : ObservationModule G) (Gamma : Subgroup G) : Submodule ℤ V.space :=
  (observationIntegerFunctions V Gamma).toIntSubmodule

/-- The integer module retains exactly the original pointwise integer-value condition. -/
theorem observationIntegerLattice_mem (V : ObservationModule G) (Gamma : Subgroup G) (F : V.space) :
    F ∈ observationIntegerLattice V Gamma ↔ ∀ gamma : Gamma, ∃ n : ℤ, F gamma = n := Iff.rfl

/-- A genuine rational coordinate polynomial has a positive integer multiple in the actual V_Z. -/
theorem observation_rational_integer_multiple (V : ObservationModule G) (Gamma : Subgroup G)
    (coord : G → sigma → ℝ)
    (hint : ∀ gamma : Gamma, ∃ z : sigma → ℤ, coord gamma = fun i => (z i : ℝ))
    (F : V.space) (P : MvPolynomial sigma ℚ)
    (hF : ∀ g, F g = MvPolynomial.aeval (coord g) P) :
    ∃ k : ℕ, 0 < k ∧ (k : ℝ) • F ∈ observationIntegerLattice V Gamma := by
  obtain ⟨k, hk, hP⟩ := rational_polynomial_integer_multiple P
  refine ⟨k, hk, ?_⟩
  intro gamma
  obtain ⟨z, hz⟩ := hint gamma
  obtain ⟨n, hn⟩ := hP z
  refine ⟨n, ?_⟩
  change (k : ℝ) * F gamma = (n : ℝ)
  rw [hF, hz]
  exact hn

/-- An actual rational polynomial basis proves that V_Z spans the whole original real space. -/
theorem observation_integer_span_top [Fintype iota]
    (V : ObservationModule G) (Gamma : Subgroup G) (b : Basis iota ℝ V.space)
    (coord : G → sigma → ℝ)
    (hint : ∀ gamma : Gamma, ∃ z : sigma → ℤ, coord gamma = fun i => (z i : ℝ))
    (P : iota → MvPolynomial sigma ℚ)
    (hb : ∀ i g, b i g = MvPolynomial.aeval (coord g) (P i)) :
    Submodule.span ℝ (observationIntegerLattice V Gamma : Set V.space) = ⊤ := by
  apply top_unique
  rw [← b.span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  change b i ∈ Submodule.span ℝ (observationIntegerLattice V Gamma : Set V.space)
  obtain ⟨k, hk, hmem⟩ := observation_rational_integer_multiple V Gamma coord hint (b i) (P i) (hb i)
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have h := (Submodule.span ℝ (observationIntegerLattice V Gamma : Set V.space)).smul_mem
    (k : ℝ)⁻¹ (Submodule.subset_span hmem)
  simpa only [smul_smul, inv_mul_cancel₀ hk0, one_smul] using h

/-- Every actual real observation inherits a polynomial representative from the rational polynomial basis. -/
theorem observation_representatives_of_rational_basis [Fintype iota]
    (V : ObservationModule G) (b : Basis iota ℝ V.space) (coord : G → sigma → ℝ)
    (P : iota → MvPolynomial sigma ℚ)
    (hb : ∀ i g, b i g = MvPolynomial.aeval (coord g) (P i)) (F : V.space) :
    ∃ Q : MvPolynomial sigma ℝ, coordinatePolynomialEvaluation coord Q = F.val := by
  classical
  have hbi (i : iota) : coordinatePolynomialEvaluation coord ((P i).map (algebraMap ℚ ℝ)) = (b i).val := by
    funext g
    change MvPolynomial.eval (coord g) ((P i).map (algebraMap ℚ ℝ)) = b i g
    rw [MvPolynomial.eval_map]
    exact (hb i g).symm
  refine ⟨∑ i, b.repr F i • (P i).map (algebraMap ℚ ℝ), ?_⟩
  rw [map_sum]
  simp_rw [map_smul, hbi]
  have he := congrArg V.space.subtype (b.sum_repr F)
  simpa only [map_sum, map_smul, Submodule.subtype_apply] using he

/-- A rational polynomial basis with actual integer-coordinate coverage gives a discrete full lattice.
Both properties refer to the original subgroup, with its inherited pointwise topology. -/
theorem observation_integer_full_lattice [Fintype iota]
    (V : ObservationModule G) (Gamma : Subgroup G) (b : Basis iota ℝ V.space)
    (coord : G → sigma → ℝ)
    (hint : ∀ gamma : Gamma, ∃ z : sigma → ℤ, coord gamma = fun i => (z i : ℝ))
    (hcover : ∀ z : sigma → ℤ, ∃ gamma : Gamma, coord gamma = fun i => (z i : ℝ))
    (P : iota → MvPolynomial sigma ℚ)
    (hb : ∀ i g, b i g = MvPolynomial.aeval (coord g) (P i)) :
    DiscreteTopology (observationIntegerLattice V Gamma) ∧
      Submodule.span ℝ (observationIntegerLattice V Gamma : Set V.space) = ⊤ := by
  let : FiniteDimensional ℝ V.space := b.finiteDimensional_of_finite
  refine ⟨?_, observation_integer_span_top V Gamma b coord hint P hb⟩
  change DiscreteTopology (observationIntegerFunctions V Gamma)
  apply observation_integer_discrete V Gamma
  exact observation_integer_points_separate V Gamma coord hcover
    (observation_representatives_of_rational_basis V b coord P hb)

end GMZP0
