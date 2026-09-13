import GMZP0.ObservationModule
import Mathlib.Tactic.Linarith

/-! The constant-in-W step from an explicit common translation-lowering flag.
Existence of this flag for rational Malcev polynomial modules is a separate
structural obligation; it is not inserted as an external analytic theorem. -/
noncomputable section
namespace GMZP0
variable {G : Type*} [Group G]

/-- A nonconstant observation has a nonzero actual translation difference. -/
theorem observation_difference_nonzero (V : ObservationModule G)
    (hnonconstant : ∃ (P : V.space) (u : G), P u ≠ P 1) :
    ∃ Q : V.space, Q ∈ observationDifferenceSpace V ∧ Q ≠ 0 := by
  obtain ⟨P, u, hu⟩ := hnonconstant
  refine ⟨observationTranslate V u P - P, observation_difference_mem V u P, ?_⟩
  intro h
  have he := congrArg (fun Q : V.space => Q 1) h
  have hh : P u - P 1 = 0 := by simpa using he
  exact hu (sub_eq_zero.mp hh)

/-- The common lowering flag forces 1 into W whenever V is nonconstant.
The proof minimizes actual flag level inside W; it does not assume a preferred
coordinate or a nonvanishing declared top coefficient. -/
theorem observation_one_mem_difference_of_flag (V : ObservationModule G)
    (h1 : (fun _ : G => (1 : ℝ)) ∈ V.space)
    (flag : ℕ → Submodule ℝ V.space) (K : ℕ)
    (hzero : flag 0 = ⊥) (htop : ∀ P : V.space, P ∈ flag K)
    (hdrop : ∀ (n : ℕ) (g : G) (P : V.space), P ∈ flag (n + 1) →
      observationTranslate V g P - P ∈ flag n)
    (hnonconstant : ∃ (P : V.space) (u : G), P u ≠ P 1) :
    observationConstant V h1 1 ∈ observationDifferenceSpace V := by
  classical
  obtain ⟨R, hRW, hR⟩ := observation_difference_nonzero V hnonconstant
  have hex : ∃ n : ℕ, ∃ Q : V.space,
      Q ∈ observationDifferenceSpace V ∧ Q ∈ flag n ∧ Q ≠ 0 :=
    ⟨K, R, hRW, htop R, hR⟩
  obtain ⟨Q, hQW, hQlevel, hQ⟩ := Nat.find_spec hex
  have hn : 0 < Nat.find hex := by
    by_contra h
    have he : Nat.find hex = 0 := by omega
    rw [he, hzero] at hQlevel
    exact hQ hQlevel
  have hinvariant (g : G) : observationTranslate V g Q = Q := by
    by_contra h
    have hd : observationTranslate V g Q - Q ≠ 0 := fun hd => h (sub_eq_zero.mp hd)
    have hl : observationTranslate V g Q - Q ∈ flag (Nat.find hex - 1) := by
      apply hdrop
      simpa only [Nat.sub_add_cancel hn] using hQlevel
    have hmin := Nat.find_min' hex ⟨observationTranslate V g Q - Q,
      observation_difference_mem V g Q, hl, hd⟩
    omega
  have hvalue (u : G) : Q u = Q 1 := observation_invariant_constant V Q hinvariant u
  have hQone : Q 1 ≠ 0 := by
    intro h
    apply hQ
    apply Subtype.ext
    funext u
    exact (hvalue u).trans h
  have hrescale : (Q 1)⁻¹ • Q = observationConstant V h1 1 := by
    apply Subtype.ext
    funext u
    change (Q 1)⁻¹ * Q u = 1
    rw [hvalue u, inv_mul_cancel₀ hQone]
  rw [← hrescale]
  exact (observationDifferenceSpace V).smul_mem _ hQW

end GMZP0
