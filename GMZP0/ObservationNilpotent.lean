import GMZP0.ObservationCommutator
import GMZP0.TriangularCoordinates
import Mathlib.GroupTheory.Nilpotent

/-! A finite lowering flag kills the observation fiber of the actual lower
central series. The resulting nilpotency bound is uniform in coefficients. -/
noncomputable section
open scoped commutatorElement
namespace GMZP0
variable {G : Type*} [Group G]

/-- An actual additive subspace embedded in the identity base fiber. -/
def observationFiberSubgroup (V : ObservationModule G) (U : Submodule ℝ V.space) :
    Subgroup (ObservationGroup V) where
  carrier := {a | a.base = 1 ∧ a.obs ∈ U}
  one_mem' := ⟨rfl, U.zero_mem⟩
  mul_mem' := by
    intro a b ha hb
    refine ⟨by simp [ha.1, hb.1], ?_⟩
    change observationTranslate V b.base a.obs + b.obs ∈ U
    rw [hb.1, observationTranslate_one]
    exact U.add_mem ha.2 hb.2
  inv_mem' := by
    intro a ha
    refine ⟨by simp [ha.1], ?_⟩
    change -observationTranslate V a.base⁻¹ a.obs ∈ U
    rw [ha.1, inv_one, observationTranslate_one]
    exact U.neg_mem ha.2

/-- The zero subspace gives the trivial group fiber. -/
theorem observationFiberSubgroup_bot (V : ObservationModule G) :
    observationFiberSubgroup V ⊥ = ⊥ := by
  apply le_antisymm
  · intro a ha
    change a = 1
    apply ObservationGroup.ext
    · exact ha.1
    · exact ha.2
  · exact bot_le

/-- An element with identity base is exactly its actual fiber inclusion. -/
theorem observation_eq_fiber_of_base_one (V : ObservationModule G) (a : ObservationGroup V)
    (ha : a.base = 1) : a = observationFiberInclusion V (Multiplicative.ofAdd a.obs) := by
  apply ObservationGroup.ext
  · exact ha
  · rfl

/-- A genuine one-step lowering of function differences gives a lowering of group commutators. -/
theorem observation_fiber_commutator_le (V : ObservationModule G)
    (U U' : Submodule ℝ V.space)
    (hdrop : ∀ (g : G) (P : V.space), P ∈ U → observationTranslate V g P - P ∈ U') :
    ⁅observationFiberSubgroup V U, (⊤ : Subgroup (ObservationGroup V))⁆ ≤ observationFiberSubgroup V U' := by
  apply Subgroup.commutator_le.mpr
  intro a ha b _
  rw [observation_eq_fiber_of_base_one V a ha.1, observation_commutator_fiber]
  refine ⟨rfl, ?_⟩
  change a.obs - observationTranslate V b.base⁻¹ a.obs ∈ U'
  simpa only [neg_sub] using U'.neg_mem (hdrop b.base⁻¹ a.obs ha.2)

/-- The actual lower central series projects to that of the original base group. -/
theorem observation_lowerCentral_projection (V : ObservationModule G) (n : ℕ) :
    (⊤ : Subgroup (ObservationGroup V)).lowerCentralSeries n ≤
      ((⊤ : Subgroup G).lowerCentralSeries n).comap (observationBaseProjection V) := by
  intro a ha
  have hm := Subgroup.mem_map_of_mem (observationBaseProjection V) ha
  rw [Subgroup.map_lowerCentralSeries, Subgroup.map_top_of_surjective _
    (observation_base_projection_surjective V)] at hm
  exact hm

/-- After the base lower central series vanishes, the remaining elements are in the full fiber. -/
theorem observation_lowerCentral_fiber_start (V : ObservationModule G)
    (U : Submodule ℝ V.space) (hU : ∀ P : V.space, P ∈ U) (c : ℕ)
    (hc : (⊤ : Subgroup G).lowerCentralSeries c = ⊥) :
    (⊤ : Subgroup (ObservationGroup V)).lowerCentralSeries c ≤ observationFiberSubgroup V U := by
  intro a ha
  refine ⟨?_, hU a.obs⟩
  have h := observation_lowerCentral_projection V c ha
  rw [hc] at h
  exact h

/-- Every additional commutator consumes one actual flag level of the remaining fiber. -/
theorem observation_lowerCentral_fiber_descent (V : ObservationModule G)
    (flag : ℕ → Submodule ℝ V.space) (K c : ℕ)
    (htop : ∀ P : V.space, P ∈ flag K)
    (hdrop : ∀ (n : ℕ) (g : G) (P : V.space), P ∈ flag (n + 1) →
      observationTranslate V g P - P ∈ flag n)
    (hc : (⊤ : Subgroup G).lowerCentralSeries c = ⊥) :
    ∀ n : ℕ, n ≤ K → (⊤ : Subgroup (ObservationGroup V)).lowerCentralSeries (c + n) ≤
      observationFiberSubgroup V (flag (K - n)) := by
  intro n
  induction n with
  | zero =>
    intro _
    simpa only [Nat.add_zero, Nat.sub_zero] using
      observation_lowerCentral_fiber_start V (flag K) htop c hc
  | succ n ih =>
    intro hn
    rw [Nat.add_succ, Subgroup.lowerCentralSeries_succ]
    apply le_trans (Subgroup.commutator_mono (ih (by omega)) le_rfl)
    apply observation_fiber_commutator_le
    intro g P hP
    apply hdrop
    have he : K - (n + 1) + 1 = K - n := by omega
    simpa only [he] using hP

/-- The actual lower central series is trivial by c+K, with an explicit finite bound. -/
theorem observation_lowerCentral_vanishes_of_flag (V : ObservationModule G)
    (flag : ℕ → Submodule ℝ V.space) (K c : ℕ)
    (hzero : flag 0 = ⊥) (htop : ∀ P : V.space, P ∈ flag K)
    (hdrop : ∀ (n : ℕ) (g : G) (P : V.space), P ∈ flag (n + 1) →
      observationTranslate V g P - P ∈ flag n)
    (hc : (⊤ : Subgroup G).lowerCentralSeries c = ⊥) :
    (⊤ : Subgroup (ObservationGroup V)).lowerCentralSeries (c + K) = ⊥ := by
  have h := observation_lowerCentral_fiber_descent V flag K c htop hdrop hc K le_rfl
  rw [Nat.sub_self, hzero, observationFiberSubgroup_bot] at h
  exact le_bot_iff.mp h

/-- A nilpotent base and the actual common lowering flag prove nilpotence of the observation group. -/
theorem observation_nilpotent_of_flag (V : ObservationModule G) [Group.IsNilpotent G]
    (flag : ℕ → Submodule ℝ V.space) (K : ℕ)
    (hzero : flag 0 = ⊥) (htop : ∀ P : V.space, P ∈ flag K)
    (hdrop : ∀ (n : ℕ) (g : G) (P : V.space), P ∈ flag (n + 1) →
      observationTranslate V g P - P ∈ flag n) :
    Group.IsNilpotent (ObservationGroup V) := by
  apply Subgroup.nilpotent_iff_lowerCentralSeries.mpr
  exact ⟨Group.nilpotencyClass G + K,
    observation_lowerCentral_vanishes_of_flag V flag K (Group.nilpotencyClass G)
      hzero htop hdrop (Subgroup.lowerCentralSeries_nilpotencyClass (G := G))⟩

/-- With the constructed triangular coordinate flag, nilpotence has a coefficient-independent bound.
The base group's nilpotence is an explicit structural hypothesis; no analytic input is used. -/
theorem observation_nilpotent_of_triangular (V : ObservationModule G) [Group.IsNilpotent G]
    {m : ℕ} (coord : G → Fin m → ℝ)
    (q : G → Fin m → MvPolynomial (Fin m) ℝ) (D R : ℕ)
    (hcoord : ∀ g u i, coord (g * u) i = coord u i + MvPolynomial.aeval (coord u) (q g i))
    (hqdeg : ∀ g i, (q g i).totalDegree ≤ D)
    (hqlow : ∀ g i d, d ∈ (q g i).support → ∀ j ∈ d.support, j.val < i.val)
    (hP : ∀ F : V.space, ∃ P : MvPolynomial (Fin m) ℝ,
      P.totalDegree ≤ R ∧ coordinatePolynomialEvaluation coord P = F.val) :
    Group.IsNilpotent (ObservationGroup V) ∧
      Group.nilpotencyClass (ObservationGroup V) ≤ Group.nilpotencyClass G + (R * (D + 1) ^ m + 1) := by
  let flag := coordinateObservationFlag V coord (triangularCoordinateWeight D)
  let K := R * (D + 1) ^ m + 1
  have hzero : flag 0 = ⊥ := coordinateObservationFlag_zero V coord _
  have htop : ∀ P : V.space, P ∈ flag K := coordinateObservationFlag_top V coord _ K
    (triangular_observation_uniform_bound V coord D R hP)
  have hdrop : ∀ (n : ℕ) (g : G) (P : V.space), P ∈ flag (n + 1) →
      observationTranslate V g P - P ∈ flag n := by
    apply coordinateObservationFlag_lowers V coord _ q hcoord
    intro g i
    exact triangular_correction_mem D i (q g i) (hqdeg g i) (hqlow g i)
  have hn := observation_nilpotent_of_flag V flag K hzero htop hdrop
  let : Group.IsNilpotent (ObservationGroup V) := hn
  refine ⟨hn, ?_⟩
  apply Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp
  exact observation_lowerCentral_vanishes_of_flag V flag K (Group.nilpotencyClass G)
    hzero htop hdrop (Subgroup.lowerCentralSeries_nilpotencyClass (G := G))

end GMZP0
