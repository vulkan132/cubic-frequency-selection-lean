import GMZP0.ObservationGroup
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic.Group
import Mathlib.Tactic.Abel

/-! Exact commutators of the actual right semidirect observation group.
The difference space is its full real span; passage from group generators to
real scalar multiples is proved explicitly, without topological closure. -/
noncomputable section
open scoped commutatorElement
namespace GMZP0
variable {G : Type*} [Group G]

/-- The actual group projection to the original base group. -/
def observationBaseProjection (V : ObservationModule G) : ObservationGroup V →* G where
  toFun a := a.base
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The original base group inside the observation group. -/
def observationBaseInclusion (V : ObservationModule G) : G →* ObservationGroup V where
  toFun g := ⟨g, 0⟩
  map_one' := rfl
  map_mul' g h := by
    apply ObservationGroup.ext
    · rfl
    · apply Subtype.ext; funext u; simp

/-- The actual additive observation fiber, written as a multiplicative group. -/
def observationFiberInclusion (V : ObservationModule G) : Multiplicative V.space →* ObservationGroup V where
  toFun P := ⟨1, P.toAdd⟩
  map_one' := rfl
  map_mul' P Q := by
    apply ObservationGroup.ext
    · simp
    · apply Subtype.ext; funext u; simp

@[simp] theorem observation_base_inclusion_base (V : ObservationModule G) (g : G) :
    (observationBaseInclusion V g).base = g := rfl

@[simp] theorem observation_base_inclusion_obs (V : ObservationModule G) (g : G) :
    (observationBaseInclusion V g).obs = 0 := rfl

@[simp] theorem observation_fiber_inclusion_base (V : ObservationModule G) (P : V.space) :
    (observationFiberInclusion V (Multiplicative.ofAdd P)).base = 1 := rfl

@[simp] theorem observation_fiber_inclusion_obs (V : ObservationModule G) (P : V.space) :
    (observationFiberInclusion V (Multiplicative.ofAdd P)).obs = P := rfl

/-- Every actual pair has the base-then-fiber factorization in the correct order. -/
theorem observation_base_fiber_decomposition (V : ObservationModule G) (a : ObservationGroup V) :
    observationBaseInclusion V a.base * observationFiberInclusion V (Multiplicative.ofAdd a.obs) = a := by
  apply ObservationGroup.ext
  · simp
  · apply Subtype.ext; funext u; simp

/-- Projection is surjective by the actual base inclusion. -/
theorem observation_base_projection_surjective (V : ObservationModule G) :
    Function.Surjective (observationBaseProjection V) := by
  intro g
  exact ⟨observationBaseInclusion V g, rfl⟩

/-- The base of the full commutator is the commutator of the original bases. -/
theorem observation_commutator_base (V : ObservationModule G) (a b : ObservationGroup V) :
    (⁅a, b⁆).base = ⁅a.base, b.base⁆ :=
  map_commutatorElement (observationBaseProjection V) a b

/-- Full real fiber formula, with all four noncommutative translation factors retained. -/
theorem observation_commutator_obs (V : ObservationModule G) (a b : ObservationGroup V) :
    (⁅a, b⁆).obs =
      (observationTranslate V (b.base * a.base⁻¹ * b.base⁻¹) a.obs -
        observationTranslate V (a.base⁻¹ * b.base⁻¹) a.obs) +
      (observationTranslate V (a.base⁻¹ * b.base⁻¹) b.obs -
        observationTranslate V b.base⁻¹ b.obs) := by
  apply Subtype.ext
  funext u
  change (⁅a, b⁆).obs u =
    (a.obs ((b.base * a.base⁻¹ * b.base⁻¹) * u) - a.obs ((a.base⁻¹ * b.base⁻¹) * u)) +
    (b.obs ((a.base⁻¹ * b.base⁻¹) * u) - b.obs (b.base⁻¹ * u))
  simp only [commutatorElement_def, observation_mul_obs, observation_mul_base,
    observation_inv_obs, observation_inv_base, mul_assoc]
  abel

/-- A base-fiber commutator realizes every actual translation difference exactly. -/
theorem observation_commutator_base_fiber (V : ObservationModule G) (g : G) (P : V.space) :
    ⁅observationBaseInclusion V g⁻¹, observationFiberInclusion V (Multiplicative.ofAdd P)⁆ =
      observationFiberInclusion V (Multiplicative.ofAdd (observationTranslate V g P - P)) := by
  apply ObservationGroup.ext
  · simp only [observation_commutator_base, observation_base_inclusion_base,
      observation_fiber_inclusion_base, commutatorElement_one_right]
  · rw [observation_commutator_obs]
    simp only [observation_base_inclusion_base, observation_base_inclusion_obs,
      observation_fiber_inclusion_base, observation_fiber_inclusion_obs, inv_one, inv_inv,
      one_mul, mul_one, map_zero, sub_self, zero_add, observationTranslate_one]

/-- Commuting a pure fiber with any observation element lowers by one actual translation difference. -/
theorem observation_commutator_fiber (V : ObservationModule G) (P : V.space) (a : ObservationGroup V) :
    ⁅observationFiberInclusion V (Multiplicative.ofAdd P), a⁆ =
      observationFiberInclusion V (Multiplicative.ofAdd (P - observationTranslate V a.base⁻¹ P)) := by
  apply ObservationGroup.ext
  · simp only [observation_commutator_base, observation_fiber_inclusion_base,
      commutatorElement_one_left]
  · rw [observation_commutator_obs]
    simp only [observation_fiber_inclusion_base, observation_fiber_inclusion_obs,
      inv_one, one_mul, mul_one, mul_inv_cancel, observationTranslate_one, sub_self, add_zero]

/-- The difference between any two actual translates lies in W. -/
theorem observation_two_translates_difference_mem (V : ObservationModule G) (g h : G) (P : V.space) :
    observationTranslate V g P - observationTranslate V h P ∈ observationDifferenceSpace V := by
  have he : observationTranslate V g P - observationTranslate V h P =
      (observationTranslate V g P - P) - (observationTranslate V h P - P) := by abel
  rw [he]
  exact (observationDifferenceSpace V).sub_mem
    (observation_difference_mem V g P) (observation_difference_mem V h P)

/-- Every full commutator has its actual observation component in W. -/
theorem observation_commutator_obs_mem (V : ObservationModule G) (a b : ObservationGroup V) :
    (⁅a, b⁆).obs ∈ observationDifferenceSpace V := by
  rw [observation_commutator_obs]
  exact (observationDifferenceSpace V).add_mem
    (observation_two_translates_difference_mem V _ _ a.obs)
    (observation_two_translates_difference_mem V _ _ b.obs)

/-- The claimed product of the base commutator with W is an actual subgroup of H. -/
def observationCommutatorSubgroup (V : ObservationModule G) : Subgroup (ObservationGroup V) where
  carrier := {a | a.base ∈ commutator G ∧ a.obs ∈ observationDifferenceSpace V}
  one_mem' := ⟨(commutator G).one_mem, (observationDifferenceSpace V).zero_mem⟩
  mul_mem' := by
    intro a b ha hb
    refine ⟨(commutator G).mul_mem ha.1 hb.1, ?_⟩
    exact (observationDifferenceSpace V).add_mem
      (observation_difference_translate_mem V b.base a.obs ha.2) hb.2
  inv_mem' := by
    intro a ha
    refine ⟨(commutator G).inv_mem ha.1, ?_⟩
    exact (observationDifferenceSpace V).neg_mem
      (observation_difference_translate_mem V a.base⁻¹ a.obs ha.2)

/-- Actual scalar multiples of every generator already belong to the group commutator. -/
theorem observation_difference_fiber_smul_mem (V : ObservationModule G) (P : V.space)
    (hP : P ∈ observationDifferenceSpace V) :
    ∀ t : ℝ, observationFiberInclusion V (Multiplicative.ofAdd (t • P)) ∈ commutator (ObservationGroup V) := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨g, Q, rfl⟩ := hP
    intro t
    have he : t • (observationTranslate V g Q - Q) =
        observationTranslate V g (t • Q) - t • Q := by rw [smul_sub, map_smul]
    rw [he, ← observation_commutator_base_fiber]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  | zero => intro t; simp
  | add P Q hP hQ ihP ihQ =>
    intro t
    rw [smul_add, ofAdd_add, map_mul]
    exact (commutator (ObservationGroup V)).mul_mem (ihP t) (ihQ t)
  | smul s P hP ih =>
    intro t
    rw [← mul_smul]
    exact ih (t * s)

/-- The entire real difference space, with no closure enlargement, lies in the group commutator fiber. -/
theorem observation_difference_fiber_mem (V : ObservationModule G) (P : V.space)
    (hP : P ∈ observationDifferenceSpace V) :
    observationFiberInclusion V (Multiplicative.ofAdd P) ∈ commutator (ObservationGroup V) := by
  simpa only [one_smul] using observation_difference_fiber_smul_mem V P hP 1

/-- Base commutators embed in the observation-group commutator. -/
theorem observation_base_commutator_mem (V : ObservationModule G) (g : G) (hg : g ∈ commutator G) :
    observationBaseInclusion V g ∈ commutator (ObservationGroup V) := by
  have hmap : (commutator G).map (observationBaseInclusion V) ≤ commutator (ObservationGroup V) := by
    rw [commutator_def, Subgroup.map_commutator, commutator_def]
    exact Subgroup.commutator_mono le_top le_top
  exact hmap (Subgroup.mem_map_of_mem (observationBaseInclusion V) hg)

/-- The manuscript's full identity [H,H] = [G,G] times W, as an equality of actual subgroups. -/
theorem observation_commutator_eq (V : ObservationModule G) :
    commutator (ObservationGroup V) = observationCommutatorSubgroup V := by
  apply le_antisymm
  · rw [commutator_def]
    apply Subgroup.commutator_le.mpr
    intro a _ b _
    refine ⟨?_, observation_commutator_obs_mem V a b⟩
    rw [observation_commutator_base]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  · intro a ha
    rw [← observation_base_fiber_decomposition V a]
    exact (commutator (ObservationGroup V)).mul_mem
      (observation_base_commutator_mem V a.base ha.1)
      (observation_difference_fiber_mem V a.obs ha.2)

end GMZP0
