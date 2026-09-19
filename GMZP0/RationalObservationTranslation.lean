import GMZP0.RationalEvaluationRecovery

/-! Derive a rational translation matrix from the original rational base
law and original polynomial basis. No translation matrix is assumed. -/
noncomputable section
open Module MvPolynomial
namespace GMZP0
variable {sigma iota : Type*}

/-- The polynomial in the translating coordinate for one original basis
function evaluated at a fixed original integer-coordinate group point. -/
def rationalTranslatedBasisPolynomial
    (p : sigma → MvPolynomial (sigma ⊕ sigma) ℚ)
    (P : MvPolynomial sigma ℚ) (z : sigma → ℤ) : MvPolynomial sigma ℚ :=
  MvPolynomial.aeval (fun s => MvPolynomial.aeval
    (Sum.elim X (fun j => C (z j : ℚ))) (p s)) P

/-- The rational substitution evaluates in the unchanged order g*u. -/
theorem rational_translated_basis_polynomial_eval
    (p : sigma → MvPolynomial (sigma ⊕ sigma) ℚ)
    (P : MvPolynomial sigma ℚ) (z : sigma → ℤ) (x : sigma → ℝ) :
    MvPolynomial.aeval x (rationalTranslatedBasisPolynomial p P z) =
      MvPolynomial.aeval (fun s => MvPolynomial.aeval
        (Sum.elim x (fun j => (z j : ℝ))) (p s)) P := by
  simp only [rationalTranslatedBasisPolynomial, MvPolynomial.comp_aeval_apply]
  apply congrArg (fun v : sigma → ℝ => MvPolynomial.aeval v P)
  funext s
  apply congrArg (fun v : (sigma ⊕ sigma) → ℝ => MvPolynomial.aeval v (p s))
  funext j
  cases j <;> simp

variable {G : Type*} [Group G] [Fintype iota]

/-- The literal rational joint base law and rational original basis
functions determine one rational polynomial matrix for every actual left
translation, before the translating point and original real observation. -/
theorem observation_rational_translation_matrix
    (V : ObservationModule G) (Gamma : Subgroup G)
    (b : Basis iota ℝ V.space) (coord : G → sigma → ℝ)
    (hint : ∀ gamma : Gamma, ∃ z : sigma → ℤ, coord gamma = fun i => (z i : ℝ))
    (hcover : ∀ z : sigma → ℤ, ∃ gamma : Gamma, coord gamma = fun i => (z i : ℝ))
    (p : sigma → MvPolynomial (sigma ⊕ sigma) ℚ)
    (hgroup : ∀ g h s, coord (g * h) s = MvPolynomial.aeval (Sum.elim (coord g) (coord h)) (p s))
    (P : iota → MvPolynomial sigma ℚ)
    (hP : ∀ j g, b j g = MvPolynomial.aeval (coord g) (P j)) :
    ∃ T : iota → iota → MvPolynomial sigma ℚ, ∀ g j i,
      b.equivFun (observationTranslate V g (b j)) i = MvPolynomial.aeval (coord g) (T i j) := by
  classical
  obtain ⟨n, _, u, z, hz, A, hA⟩ :=
    observation_rational_recovery_on_integer_points V Gamma b coord hint hcover P hP
  refine ⟨fun i j => ∑ k, C (A i k) * rationalTranslatedBasisPolynomial p (P j) (z k), ?_⟩
  intro g j i
  rw [hA]
  simp only [map_sum, map_mul, MvPolynomial.aeval_C, rational_translated_basis_polynomial_eval,
    observationTranslate_apply]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  rw [hP]
  apply congrArg (fun v : sigma → ℝ => MvPolynomial.aeval v (P j))
  funext s
  rw [hgroup, hz]

/-- In particular the rational translation-difference matrix is derived,
including the exact identity subtraction in the original basis. -/
theorem observation_rational_difference_matrix
    (V : ObservationModule G) (Gamma : Subgroup G)
    (b : Basis iota ℝ V.space) (coord : G → sigma → ℝ)
    (hint : ∀ gamma : Gamma, ∃ z : sigma → ℤ, coord gamma = fun i => (z i : ℝ))
    (hcover : ∀ z : sigma → ℤ, ∃ gamma : Gamma, coord gamma = fun i => (z i : ℝ))
    (p : sigma → MvPolynomial (sigma ⊕ sigma) ℚ)
    (hgroup : ∀ g h s, coord (g * h) s = MvPolynomial.aeval (Sum.elim (coord g) (coord h)) (p s))
    (P : iota → MvPolynomial sigma ℚ)
    (hP : ∀ j g, b j g = MvPolynomial.aeval (coord g) (P j)) :
    ∃ T : iota → iota → MvPolynomial sigma ℚ, ∀ g j i,
      b.repr (observationTranslate V g (b j) - b j) i = MvPolynomial.aeval (coord g) (T i j) := by
  classical
  obtain ⟨T, hT⟩ := observation_rational_translation_matrix V Gamma b coord hint hcover p hgroup P hP
  refine ⟨fun i j => T i j - if i = j then 1 else 0, ?_⟩
  intro g j i
  change b.equivFun (observationTranslate V g (b j) - b j) i = _
  simp only [map_sub, Pi.sub_apply, hT]
  by_cases h : i = j
  · subst j
    simp
  · simp [h, Ne.symm h]

/-- The actual difference space W is rational in the original basis,
derived from the rational base law and original function polynomials. -/
theorem observation_difference_rational_from_base_law
    (V : ObservationModule G) (Gamma : Subgroup G)
    (b : Basis iota ℝ V.space) (coord : G → sigma → ℝ) (hsurj : Function.Surjective coord)
    (hint : ∀ gamma : Gamma, ∃ z : sigma → ℤ, coord gamma = fun i => (z i : ℝ))
    (hcover : ∀ z : sigma → ℤ, ∃ gamma : Gamma, coord gamma = fun i => (z i : ℝ))
    (p : sigma → MvPolynomial (sigma ⊕ sigma) ℚ)
    (hgroup : ∀ g h s, coord (g * h) s = MvPolynomial.aeval (Sum.elim (coord g) (coord h)) (p s))
    (P : iota → MvPolynomial sigma ℚ)
    (hP : ∀ j g, b j g = MvPolynomial.aeval (coord g) (P j)) :
    RationalInBasis b (observationDifferenceSpace V) := by
  obtain ⟨T, hT⟩ := observation_rational_difference_matrix V Gamma b coord hint hcover p hgroup P hP
  exact observation_difference_rational_of_matrix V b coord hsurj T hT

end GMZP0
