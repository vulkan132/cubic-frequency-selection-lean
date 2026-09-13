import GMZP0.ObservationModule
import Mathlib.GroupTheory.Coset.Defs

/-! The manuscript's right semidirect group, with its actual integer-valued subgroup.
Neither a nilpotent structure nor a cocompact lattice is inferred from these algebraic facts. -/
noncomputable section
namespace GMZP0
variable {G : Type*} [Group G]

/-- The pair (g,P), before choosing any representatives or taking any quotient. -/
@[ext] structure ObservationGroup (V : ObservationModule G) where
  base : G
  obs : V.space

instance (V : ObservationModule G) : Mul (ObservationGroup V) where
  mul a b := ⟨a.base * b.base, observationTranslate V b.base a.obs + b.obs⟩

instance (V : ObservationModule G) : One (ObservationGroup V) where
  one := ⟨1, 0⟩

instance (V : ObservationModule G) : Inv (ObservationGroup V) where
  inv a := ⟨a.base⁻¹, -observationTranslate V a.base⁻¹ a.obs⟩

@[simp] theorem observation_mul_base (V : ObservationModule G) (a b : ObservationGroup V) :
    (a * b).base = a.base * b.base := rfl

@[simp] theorem observation_mul_obs (V : ObservationModule G) (a b : ObservationGroup V) (u : G) :
    (a * b).obs u = a.obs (b.base * u) + b.obs u := rfl

@[simp] theorem observation_one_base (V : ObservationModule G) :
    (1 : ObservationGroup V).base = 1 := rfl

@[simp] theorem observation_one_obs (V : ObservationModule G) (u : G) :
    (1 : ObservationGroup V).obs u = 0 := rfl

@[simp] theorem observation_inv_base (V : ObservationModule G) (a : ObservationGroup V) :
    a⁻¹.base = a.base⁻¹ := rfl

@[simp] theorem observation_inv_obs (V : ObservationModule G) (a : ObservationGroup V) (u : G) :
    a⁻¹.obs u = -a.obs (a.base⁻¹ * u) := rfl

/-- Associativity and inverses follow from the actual pullback order. -/
instance (V : ObservationModule G) : Group (ObservationGroup V) where
  mul_assoc a b c := by
    apply ObservationGroup.ext
    · exact mul_assoc _ _ _
    · apply Subtype.ext; funext u; simp [mul_assoc, add_assoc]
  one_mul a := by
    apply ObservationGroup.ext
    · exact one_mul _
    · apply Subtype.ext; funext u; simp
  mul_one a := by
    apply ObservationGroup.ext
    · exact mul_one _
    · apply Subtype.ext; funext u; simp
  inv_mul_cancel a := by
    apply ObservationGroup.ext
    · exact inv_mul_cancel _
    · apply Subtype.ext; funext u; simp

/-- The claimed product Gamma times V_Z is proved to be a subgroup. -/
def observationLatticeSubgroup (V : ObservationModule G) (Gamma : Subgroup G) :
    Subgroup (ObservationGroup V) where
  carrier := {a | a.base ∈ Gamma ∧ a.obs ∈ observationIntegerFunctions V Gamma}
  one_mem' := ⟨Gamma.one_mem, (observationIntegerFunctions V Gamma).zero_mem⟩
  mul_mem' := by
    intro a b ha hb
    refine ⟨Gamma.mul_mem ha.1 hb.1, ?_⟩
    exact (observationIntegerFunctions V Gamma).add_mem
      (observation_integer_translate V Gamma ⟨b.base, hb.1⟩ a.obs ha.2) hb.2
  inv_mem' := by
    intro a ha
    refine ⟨Gamma.inv_mem ha.1, ?_⟩
    exact (observationIntegerFunctions V Gamma).neg_mem
      (observation_integer_translate V Gamma ⟨a.base⁻¹, Gamma.inv_mem ha.1⟩ a.obs ha.2)

/-- Explicit membership, without claiming the subgroup is discrete or cocompact. -/
theorem observation_lattice_mem (V : ObservationModule G) (Gamma : Subgroup G)
    (a : ObservationGroup V) : a ∈ observationLatticeSubgroup V Gamma ↔
      a.base ∈ Gamma ∧ ∀ gamma : Gamma, ∃ n : ℤ, a.obs gamma = n := Iff.rfl

end GMZP0
