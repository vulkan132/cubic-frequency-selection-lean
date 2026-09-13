import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.Data.Real.Basic

/-! The actual space of observation functions and its translation-difference space.
This algebra applies to the manuscript's polynomial module. Rationality, finite
dimension, and the common unipotent flag are separate obligations. -/
noncomputable section
namespace GMZP0

/-- A real function space closed under pullback by every left translation. -/
structure ObservationModule (G : Type*) [Group G] where
  space : Submodule ℝ (G → ℝ)
  translate_mem : ∀ (g : G) (P : G → ℝ), P ∈ space → (fun u => P (g * u)) ∈ space

variable {G : Type*} [Group G]

instance (V : ObservationModule G) : CoeFun V.space (fun _ => G → ℝ) := ⟨fun P => P.val⟩

/-- Pullback, with the order used by the paper's right semidirect product. -/
def observationTranslate (V : ObservationModule G) (g : G) : V.space →ₗ[ℝ] V.space where
  toFun P := ⟨fun u => P (g * u), V.translate_mem g P P.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem observationTranslate_apply (V : ObservationModule G) (g : G)
    (P : V.space) (u : G) : observationTranslate V g P u = P (g * u) := rfl

/-- Pullback reverses the order of composition; no commutativity is assumed. -/
theorem observationTranslate_comp (V : ObservationModule G) (g h : G) (P : V.space) :
    observationTranslate V h (observationTranslate V g P) = observationTranslate V (g * h) P := by
  apply Subtype.ext
  funext u
  simp only [observationTranslate_apply, mul_assoc]

@[simp] theorem observationTranslate_one (V : ObservationModule G) (P : V.space) :
    observationTranslate V 1 P = P := by
  apply Subtype.ext
  funext u
  simp

/-- The difference space is constructed from actual translated functions. -/
def observationDifferenceSpace (V : ObservationModule G) : Submodule ℝ V.space :=
  Submodule.span ℝ {Q | ∃ (g : G) (P : V.space), Q = observationTranslate V g P - P}

/-- Each actual translation difference belongs to the constructed space. -/
theorem observation_difference_mem (V : ObservationModule G) (g : G) (P : V.space) :
    observationTranslate V g P - P ∈ observationDifferenceSpace V :=
  Submodule.subset_span ⟨g, P, rfl⟩

/-- The difference space is invariant under all left-translation pullbacks. -/
theorem observation_difference_translate_mem (V : ObservationModule G) (g : G)
    (P : V.space) (hP : P ∈ observationDifferenceSpace V) :
    observationTranslate V g P ∈ observationDifferenceSpace V := by
  have hdiff := observation_difference_mem V g P
  have hsum := (observationDifferenceSpace V).add_mem hdiff hP
  simpa only [sub_add_cancel] using hsum

/-- An invariant observation function is constant, by transitivity on the group. -/
theorem observation_invariant_constant (V : ObservationModule G) (P : V.space)
    (hP : ∀ g, observationTranslate V g P = P) (u : G) : P u = P 1 := by
  have he := congrArg (fun Q : V.space => Q 1) (hP u)
  simpa using he

/-- Annihilating the actual difference space is exactly invariance of a linear functional. -/
theorem observation_annihilator_iff (V : ObservationModule G) (ell : V.space →ₗ[ℝ] ℝ) :
    observationDifferenceSpace V ≤ LinearMap.ker ell ↔
      ∀ g P, ell (observationTranslate V g P) = ell P := by
  constructor
  · intro h g P
    have he := h (observation_difference_mem V g P)
    simpa only [LinearMap.mem_ker, map_sub, sub_eq_zero] using he
  · intro h
    apply Submodule.span_le.mpr
    rintro Q ⟨g, P, rfl⟩
    change ell (observationTranslate V g P - P) = 0
    rw [map_sub, h, sub_self]

/-- Integer-valued observations on the actual subgroup; no compactness is presupposed. -/
def observationIntegerFunctions (V : ObservationModule G) (Gamma : Subgroup G) :
    AddSubgroup V.space where
  carrier := {P | ∀ gamma : Gamma, ∃ n : ℤ, P gamma = n}
  zero_mem' := by intro gamma; exact ⟨0, by simp⟩
  add_mem' := by
    intro P Q hP hQ gamma
    obtain ⟨m, hm⟩ := hP gamma
    obtain ⟨n, hn⟩ := hQ gamma
    exact ⟨m + n, by change P gamma + Q gamma = _; rw [hm, hn, Int.cast_add]⟩
  neg_mem' := by
    intro P hP gamma
    obtain ⟨m, hm⟩ := hP gamma
    exact ⟨-m, by change -P gamma = _; rw [hm, Int.cast_neg]⟩

/-- Lattice translations preserve integer values, including inverse translations. -/
theorem observation_integer_translate (V : ObservationModule G) (Gamma : Subgroup G)
    (gamma : Gamma) (P : V.space) (hP : P ∈ observationIntegerFunctions V Gamma) :
    observationTranslate V gamma P ∈ observationIntegerFunctions V Gamma := by
  intro delta
  exact hP (gamma * delta)

/-- Constant observations are represented by actual constant functions. -/
def observationConstant (V : ObservationModule G) (h1 : (fun _ : G => (1 : ℝ)) ∈ V.space)
    (a : ℝ) : V.space :=
  ⟨fun _ => a, by simpa only [Pi.smul_def, smul_eq_mul, mul_one] using V.space.smul_mem a h1⟩

@[simp] theorem observationConstant_apply (V : ObservationModule G)
    (h1 : (fun _ : G => (1 : ℝ)) ∈ V.space) (a : ℝ) (u : G) :
    observationConstant V h1 a u = a := rfl

/-- Every constant term lies in W once the actual constant one lies in W. -/
theorem observation_constant_mem_difference (V : ObservationModule G)
    (h1 : (fun _ : G => (1 : ℝ)) ∈ V.space)
    (hW : observationConstant V h1 1 ∈ observationDifferenceSpace V) (a : ℝ) :
    observationConstant V h1 a ∈ observationDifferenceSpace V := by
  convert (observationDifferenceSpace V).smul_mem a hW using 1
  apply Subtype.ext
  funext u
  simp

end GMZP0
