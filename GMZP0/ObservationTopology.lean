import GMZP0.ObservationFiniteDimension
import Mathlib.Topology.Algebra.MvPolynomial

/-! Joint continuity of evaluation and of the actual translation action.
Finite dimension is essential to passing from pointwise to joint evaluation.
This gives the genuine topological group, without postulating a Lie structure. -/
noncomputable section
open Module
namespace GMZP0
variable {G : Type*} [Group G] [TopologicalSpace G]

omit [TopologicalSpace G] in
/-- An actual finite basis reconstructs evaluation at every original group point. -/
theorem observation_evaluation_basis (V : ObservationModule G)
    {iota : Type*} [Fintype iota] (b : Basis iota ℝ V.space) (P : V.space) (u : G) :
    P u = ∑ i, b.equivFun P i * b i u := by
  let ev : V.space →ₗ[ℝ] ℝ := (LinearMap.proj u).comp V.space.subtype
  calc
    P u = ev (∑ i, b.equivFun P i • b i) := by rw [b.sum_equivFun]; rfl
    _ = _ := by simp only [map_sum, map_smul, smul_eq_mul]; rfl

/-- Evaluation is jointly continuous for the actual finite-dimensional space of continuous functions. -/
theorem observation_evaluation_continuous (V : ObservationModule G) [FiniteDimensional ℝ V.space]
    (hcont : ∀ P : V.space, Continuous (fun u : G => P u)) :
    Continuous (fun z : V.space × G => z.1 z.2) := by
  let b := Module.finBasis ℝ V.space
  have he : (fun z : V.space × G => z.1 z.2) =
      fun z => ∑ i, b.equivFun z.1 i * b i z.2 := by
    funext z
    exact observation_evaluation_basis V b z.1 z.2
  rw [he]
  apply continuous_finsetSum
  intro i _
  exact ((continuous_apply i).comp ((continuous_equivFun_basis b).comp continuous_fst)).mul
    ((hcont (b i)).comp continuous_snd)

/-- The actual pullback action is jointly continuous, with the original multiplication order. -/
theorem observation_translate_joint_continuous [IsTopologicalGroup G]
    (V : ObservationModule G) [FiniteDimensional ℝ V.space]
    (hcont : ∀ P : V.space, Continuous (fun u : G => P u)) :
    Continuous (fun z : G × V.space => observationTranslate V z.1 z.2) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro u
  exact (observation_evaluation_continuous V hcont).comp
    (continuous_snd.prodMk (continuous_fst.mul continuous_const))

/-- The two actual pair coordinates are continuous in H's product topology. -/
theorem observation_pair_coordinates_continuous (V : ObservationModule G) :
    Continuous (fun a : ObservationGroup V => (a.base, a.obs)) := continuous_induced_dom

/-- Actual group multiplication is continuous when the original functions and base action are continuous. -/
theorem observation_group_mul_continuous [IsTopologicalGroup G]
    (V : ObservationModule G) [FiniteDimensional ℝ V.space]
    (hcont : ∀ P : V.space, Continuous (fun u : G => P u)) :
    Continuous (fun z : ObservationGroup V × ObservationGroup V => z.1 * z.2) := by
  have hb := (observation_pair_coordinates_continuous V).fst
  have hv := (observation_pair_coordinates_continuous V).snd
  apply continuous_induced_rng.mpr
  exact ((hb.comp continuous_fst).mul (hb.comp continuous_snd)).prodMk
    (((observation_translate_joint_continuous V hcont).comp
      ((hb.comp continuous_snd).prodMk (hv.comp continuous_fst))).add (hv.comp continuous_snd))

/-- The actual inverse, including its inverse-base pullback, is continuous. -/
theorem observation_group_inv_continuous [IsTopologicalGroup G]
    (V : ObservationModule G) [FiniteDimensional ℝ V.space]
    (hcont : ∀ P : V.space, Continuous (fun u : G => P u)) :
    Continuous (fun a : ObservationGroup V => a⁻¹) := by
  have hb := (observation_pair_coordinates_continuous V).fst
  have hv := (observation_pair_coordinates_continuous V).snd
  apply continuous_induced_rng.mpr
  exact hb.inv.prodMk (((observation_translate_joint_continuous V hcont).comp (hb.inv.prodMk hv)).neg)

/-- The constructed product topology and exact multiplication make H a topological group. -/
theorem observation_isTopologicalGroup [IsTopologicalGroup G]
    (V : ObservationModule G) [FiniteDimensional ℝ V.space]
    (hcont : ∀ P : V.space, Continuous (fun u : G => P u)) :
    IsTopologicalGroup (ObservationGroup V) where
  continuous_mul := observation_group_mul_continuous V hcont
  continuous_inv := observation_group_inv_continuous V hcont

/-- Actual continuous coordinates make each represented observation function continuous. -/
theorem observation_function_continuous_of_coordinates (V : ObservationModule G)
    {sigma : Type*} (coord : G → sigma → ℝ) (hc : Continuous coord)
    (hP : ∀ F : V.space, ∃ P : MvPolynomial sigma ℝ, coordinatePolynomialEvaluation coord P = F.val)
    (F : V.space) : Continuous (fun u : G => F u) := by
  obtain ⟨P, he⟩ := hP F
  change Continuous F.val
  rw [← he]
  exact P.continuous_eval.comp hc

/-- The same polynomial presentation supplies both finite dimension and topological group structure. -/
theorem observation_topologicalGroup_of_degree [IsTopologicalGroup G]
    (V : ObservationModule G) {sigma : Type*} [Finite sigma]
    (coord : G → sigma → ℝ) (hc : Continuous coord) (R : ℕ)
    (hP : ∀ F : V.space, ∃ P : MvPolynomial sigma ℝ,
      P.totalDegree ≤ R ∧ coordinatePolynomialEvaluation coord P = F.val) :
    IsTopologicalGroup (ObservationGroup V) := by
  let : FiniteDimensional ℝ V.space := observation_finiteDimensional_of_degree V coord R hP
  apply observation_isTopologicalGroup V
  exact observation_function_continuous_of_coordinates V coord hc
    (fun F => let ⟨P, _, he⟩ := hP F; ⟨P, he⟩)

end GMZP0
