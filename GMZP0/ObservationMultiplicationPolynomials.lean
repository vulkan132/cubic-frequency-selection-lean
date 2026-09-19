import GMZP0.ObservationCoefficientRecovery
import GMZP0.ObservationFullCoordinates

/-! Literal joint multiplication polynomials of the original observation
group are constructed from the original base law and basis polynomials.
Finite evaluations recover coefficients of the actual translated function. -/
noncomputable section
open Module MvPolynomial
namespace GMZP0
variable {sigma iota : Type*}

/-- Substitute the two original base coordinate blocks into a base law. -/
def observationBaseProductPolynomial (p : sigma → MvPolynomial (sigma ⊕ sigma) ℝ) (s : sigma) :
    MvPolynomial ((sigma ⊕ iota) ⊕ (sigma ⊕ iota)) ℝ :=
  MvPolynomial.aeval (Sum.elim (fun j => X (Sum.inl (Sum.inl j)))
    (fun j => X (Sum.inr (Sum.inl j)))) (p s)

/-- Evaluate a translated original basis polynomial at one fixed actual
group point. The translating base is the second original group factor. -/
def observationTranslatedValuePolynomial (p : sigma → MvPolynomial (sigma ⊕ sigma) ℝ)
    (P : MvPolynomial sigma ℝ) (u : sigma → ℝ) :
    MvPolynomial ((sigma ⊕ iota) ⊕ (sigma ⊕ iota)) ℝ :=
  MvPolynomial.aeval (fun s => MvPolynomial.aeval
    (Sum.elim (fun j => X (Sum.inr (Sum.inl j))) (fun j => C (u j))) (p s)) P

/-- The base polynomial uses precisely the two actual base blocks. -/
theorem observation_base_product_polynomial_eval
    (p : sigma → MvPolynomial (sigma ⊕ sigma) ℝ) (s : sigma)
    (x y : (sigma ⊕ iota) → ℝ) :
    MvPolynomial.aeval (Sum.elim x y) (observationBaseProductPolynomial p s) =
      MvPolynomial.aeval (Sum.elim (fun j => x (Sum.inl j)) (fun j => y (Sum.inl j))) (p s) := by
  simp only [observationBaseProductPolynomial, MvPolynomial.comp_aeval_apply]
  apply congrArg (fun v : (sigma ⊕ sigma) → ℝ => MvPolynomial.aeval v (p s))
  funext j
  cases j <;> simp

/-- Substitution keeps the original order h*u at the selected actual point. -/
theorem observation_translated_value_polynomial_eval
    (p : sigma → MvPolynomial (sigma ⊕ sigma) ℝ) (P : MvPolynomial sigma ℝ)
    (u : sigma → ℝ) (x y : (sigma ⊕ iota) → ℝ) :
    MvPolynomial.aeval (Sum.elim x y) (observationTranslatedValuePolynomial p P u) =
      MvPolynomial.aeval (fun s => MvPolynomial.aeval
        (Sum.elim (fun j => y (Sum.inl j)) u) (p s)) P := by
  simp only [observationTranslatedValuePolynomial, MvPolynomial.comp_aeval_apply]
  apply congrArg (fun v : sigma → ℝ => MvPolynomial.aeval v P)
  funext s
  apply congrArg (fun v : (sigma ⊕ sigma) → ℝ => MvPolynomial.aeval v (p s))
  funext j
  cases j <;> simp

variable [Fintype iota]

/-- The full original semidirect multiplication polynomial, including the
unrestricted first fiber coefficients and the unchanged second fiber. -/
def observationFullProductPolynomial {n : ℕ}
    (p : sigma → MvPolynomial (sigma ⊕ sigma) ℝ)
    (P : iota → MvPolynomial sigma ℝ) (u : Fin n → sigma → ℝ)
    (A : iota → Fin n → ℝ) (j : sigma ⊕ iota) :
    MvPolynomial ((sigma ⊕ iota) ⊕ (sigma ⊕ iota)) ℝ :=
  match j with
  | Sum.inl s => observationBaseProductPolynomial p s
  | Sum.inr i => X (Sum.inr (Sum.inr i)) +
      ∑ k, ∑ j, C (A i k) * X (Sum.inl (Sum.inr j)) * observationTranslatedValuePolynomial p (P j) (u k)

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- A single fixed finite array of actual polynomials represents the
complete original H multiplication for every pair of original elements.
No translation matrix, coefficient bound or new group law is supplied. -/
theorem observation_group_joint_polynomial_presentation
    (V : ObservationModule G) (coord : G ≃ₜ (sigma → ℝ)) (b : Basis iota ℝ V.space)
    (p : sigma → MvPolynomial (sigma ⊕ sigma) ℝ)
    (hgroup : ∀ g h s, coord (g * h) s = MvPolynomial.aeval (Sum.elim (coord g) (coord h)) (p s))
    (P : iota → MvPolynomial sigma ℝ)
    (hP : ∀ j g, b j g = MvPolynomial.aeval (coord g) (P j)) :
    ∃ Q : (sigma ⊕ iota) → MvPolynomial ((sigma ⊕ iota) ⊕ (sigma ⊕ iota)) ℝ,
      ∀ a e : ObservationGroup V, ∀ s,
        observationFullCoordinates V coord b (a * e) s =
          MvPolynomial.aeval (Sum.elim (observationFullCoordinates V coord b a)
            (observationFullCoordinates V coord b e)) (Q s) := by
  classical
  obtain ⟨n, _, u, A, hA⟩ := observation_coefficients_from_finite_values V b
  refine ⟨observationFullProductPolynomial p P (fun k => coord (u k)) A, ?_⟩
  intro a e s
  cases s with
  | inl s =>
    change coord (a.base * e.base) s = MvPolynomial.aeval _ (observationBaseProductPolynomial p s)
    rw [observation_base_product_polynomial_eval]
    exact hgroup a.base e.base s
  | inr i =>
    have heval (k : Fin n) (j : iota) :
        MvPolynomial.aeval (Sum.elim (observationFullCoordinates V coord b a)
          (observationFullCoordinates V coord b e))
          (observationTranslatedValuePolynomial p (P j) (coord (u k))) = b j (e.base * u k) := by
      rw [observation_translated_value_polynomial_eval, hP]
      apply congrArg (fun v : sigma → ℝ => MvPolynomial.aeval v (P j))
      funext s
      exact (hgroup e.base (u k) s).symm
    change b.equivFun (observationTranslate V e.base a.obs + e.obs) i = _
    rw [map_add, Pi.add_apply, hA]
    simp only [observationFullProductPolynomial, map_add, map_sum, map_mul,
      MvPolynomial.aeval_C, MvPolynomial.aeval_X,
      Sum.elim_inr, Sum.elim_inl, observation_full_coordinates_fiber, heval,
      observationTranslate_apply]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [observation_evaluation_basis V b a.obs (e.base * u k), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact (mul_assoc _ _ _).symm

end GMZP0
