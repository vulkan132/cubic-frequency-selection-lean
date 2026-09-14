import GMZP0.FiniteObservationEvaluations
import GMZP0.IntegerPolynomialValues
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Tactic.NormNum

/-! Discreteness of the actual subgroup of integer-valued functions.
No lattice conclusion is assumed in the hypotheses. -/
noncomputable section
namespace GMZP0
variable {G : Type*} [Group G]

/-- Finite actual integer evaluations isolate zero in the original integer-valued subgroup. -/
theorem observation_integer_discrete_of_evaluations (V : ObservationModule G)
    (Gamma : Subgroup G) {n : ℕ} (gamma : Fin n → Gamma)
    (hsep : ∀ P : V.space, (∀ i, P (gamma i) = 0) → P = 0) :
    DiscreteTopology (observationIntegerFunctions V Gamma) := by
  classical
  apply discreteTopology_iff_isOpen_singleton_zero.mpr
  have he : ({0} : Set (observationIntegerFunctions V Gamma)) =
      ⋂ i : Fin n, {P : observationIntegerFunctions V Gamma | |(P : V.space) (gamma i)| < (1 : ℝ)} := by
    ext P
    simp only [Set.mem_singleton_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    constructor
    · intro h
      subst P
      intro i
      norm_num
    · intro h
      apply Subtype.ext
      apply hsep
      intro i
      obtain ⟨m, hm⟩ := P.property (gamma i)
      have hi : |(m : ℝ)| < 1 := by simpa only [hm] using h i
      have hm0 : m = 0 := by
        have hi' : |m| < (1 : ℤ) := by exact_mod_cast hi
        have hb := abs_lt.mp hi'
        omega
      simpa only [hm0, Int.cast_zero] using hm
  rw [he]
  apply isOpen_iInter_of_finite
  intro i
  have hc : Continuous (fun P : observationIntegerFunctions V Gamma => (P : V.space) (gamma i)) :=
    (continuous_apply (gamma i : G)).comp (continuous_subtype_val.comp continuous_subtype_val)
  exact isOpen_lt hc.abs continuous_const

/-- Finite dimension and separation on the whole actual subgroup imply discreteness of V_Z. -/
theorem observation_integer_discrete (V : ObservationModule G) [FiniteDimensional ℝ V.space]
    (Gamma : Subgroup G)
    (hsep : ∀ P : V.space, (∀ gamma : Gamma, P gamma = 0) → P = 0) :
    DiscreteTopology (observationIntegerFunctions V Gamma) := by
  obtain ⟨n, _, gamma, hgamma⟩ := observation_finite_determining_points V Gamma hsep
  exact observation_integer_discrete_of_evaluations V Gamma gamma hgamma

/-- Polynomial representatives and actual integer-coordinate coverage make subgroup evaluation separating. -/
theorem observation_integer_points_separate (V : ObservationModule G) (Gamma : Subgroup G)
    {sigma : Type*} (coord : G → sigma → ℝ)
    (hcover : ∀ z : sigma → ℤ, ∃ gamma : Gamma, coord gamma = fun i => (z i : ℝ))
    (hP : ∀ F : V.space, ∃ P : MvPolynomial sigma ℝ, coordinatePolynomialEvaluation coord P = F.val)
    (F : V.space) (hF : ∀ gamma : Gamma, F gamma = 0) : F = 0 := by
  obtain ⟨P, he⟩ := hP F
  have hz : P = 0 := by
    apply real_polynomial_zero_of_integer_values
    intro z
    obtain ⟨gamma, hgamma⟩ := hcover z
    have hf := congrFun he gamma
    change MvPolynomial.eval (coord gamma) P = F gamma at hf
    rw [hgamma, hF gamma] at hf
    exact hf
  apply Subtype.ext
  change F.val = 0
  simpa only [hz, map_zero] using he.symm

/-- The actual bounded polynomial presentation and integer-coordinate coverage imply discreteness. -/
theorem observation_integer_discrete_of_coordinates (V : ObservationModule G) (Gamma : Subgroup G)
    {sigma : Type*} [Finite sigma] (coord : G → sigma → ℝ) (R : ℕ)
    (hcover : ∀ z : sigma → ℤ, ∃ gamma : Gamma, coord gamma = fun i => (z i : ℝ))
    (hP : ∀ F : V.space, ∃ P : MvPolynomial sigma ℝ,
      P.totalDegree ≤ R ∧ coordinatePolynomialEvaluation coord P = F.val) :
    DiscreteTopology (observationIntegerFunctions V Gamma) := by
  let : FiniteDimensional ℝ V.space := observation_finiteDimensional_of_degree V coord R hP
  apply observation_integer_discrete V Gamma
  exact observation_integer_points_separate V Gamma coord hcover
    (fun F => let ⟨P, _, he⟩ := hP F; ⟨P, he⟩)

end GMZP0
