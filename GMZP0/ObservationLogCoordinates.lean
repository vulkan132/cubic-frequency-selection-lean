import GMZP0.ObservationFiberPolynomials
import GMZP0.ObservationFullCoordinates

/-! The same original fiber basis identifies full tangents and gives
literal rational arrays for both directions of a fibered time-one map. -/
noncomputable section
open Module MvPolynomial
namespace GMZP0
variable {G sigma iota : Type*} [Group G] [Fintype sigma] [Fintype iota]

/-- Full tangent coefficients in the original base coordinates and fiber basis. -/
def observationTangentCoordinates (V : ObservationModule G) (b : Basis iota ℝ V.space) :
    ((sigma → ℝ) × V.space) ≃ ((sigma ⊕ iota) → ℝ) where
  toFun a := Sum.elim a.1 (b.equivFun a.2)
  invFun x := (fun s => x (Sum.inl s), b.equivFun.symm (fun i => x (Sum.inr i)))
  left_inv := by intro a; simp
  right_inv := by
    intro x
    funext s
    cases s with
    | inl s => rfl
    | inr i => exact congrFun (b.equivFun.apply_symm_apply (fun j => x (Sum.inr j))) i

/-- The actual inverse time-one map expressed in all original tangent coefficients. -/
def observationLogCoordinates (V : ObservationModule G) (b : Basis iota ℝ V.space)
    (e : ((sigma → ℝ) × V.space) ≃ ObservationGroup V) :
    ObservationGroup V ≃ ((sigma ⊕ iota) → ℝ) :=
  e.symm.trans (observationTangentCoordinates V b)

/-- Forward array: original base time-one polynomials and original fiber operator. -/
def observationForwardPolynomial (EG : sigma → MvPolynomial sigma ℚ)
    (A : iota → iota → sigma → ℚ) (E : Polynomial ℚ) :
    (sigma ⊕ iota) → MvPolynomial (sigma ⊕ iota) ℚ :=
  Sum.elim (fun s => rename Sum.inl (EG s)) (fiberOperatorPolynomial A E)

/-- Inverse array: substitute the actual base logarithm into the fiber
inverse, retaining the original fiber-coordinate variables unchanged. -/
def observationInversePolynomial (LG : sigma → MvPolynomial sigma ℚ)
    (A : iota → iota → sigma → ℚ) (L : Polynomial ℚ) :
    (sigma ⊕ iota) → MvPolynomial (sigma ⊕ iota) ℚ :=
  Sum.elim (fun s => rename Sum.inl (LG s)) (fun i =>
    aeval (Sum.elim (fun s => rename Sum.inl (LG s)) (fun j => X (Sum.inr j)))
      (fiberOperatorPolynomial A L i))

variable [TopologicalSpace G]

/-- The forward array evaluates to the actual time-one map in the same
original coordinates, for every full tangent. -/
theorem observation_forward_polynomial_eval
    (V : ObservationModule G) (coord : G ≃ₜ (sigma → ℝ)) (b : Basis iota ℝ V.space)
    (A : iota → iota → sigma → ℚ) (E : Polynomial ℚ)
    (EG : sigma → MvPolynomial sigma ℚ) (g : (sigma → ℝ) → G)
    (hG : ∀ v s, coord (g v) s = aeval v (EG s))
    (e : ((sigma → ℝ) × V.space) ≃ ObservationGroup V) :
    letI := Algebra.restrictScalars ℚ ℝ (Module.End ℝ V.space)
    (∀ v Q, e (v, Q) = (⟨g v, Polynomial.aeval
      (observationCoordinateDifferential V b A v) E Q⟩ : ObservationGroup V)) →
    ∀ x s, observationFullCoordinates V coord b ((observationLogCoordinates V b e).symm x) s =
      aeval x (observationForwardPolynomial EG A E s) := by
  let := Algebra.restrictScalars ℚ ℝ (Module.End ℝ V.space)
  intro he x s
  have hx : Sum.elim (fun s => x (Sum.inl s)) (fun i => x (Sum.inr i)) = x := by
    funext j; cases j <;> rfl
  change observationFullCoordinates V coord b
    (e (fun s => x (Sum.inl s), b.equivFun.symm (fun i => x (Sum.inr i)))) s = _
  rw [he]
  cases s with
  | inl s =>
    change coord (g (fun s => x (Sum.inl s))) s = aeval x (rename Sum.inl (EG s))
    rw [hG, aeval_rename]
    rfl
  | inr i =>
    change b.equivFun (Polynomial.aeval (observationCoordinateDifferential V b A
      (fun s => x (Sum.inl s))) E (b.equivFun.symm (fun i => x (Sum.inr i)))) i = _
    rw [← fiber_operator_polynomial_eval, b.equivFun.apply_symm_apply, hx]
    rfl

/-- The inverse array evaluates to the actual inverse time-one map on
every original group element and its unchanged original observation. -/
theorem observation_inverse_polynomial_eval
    (V : ObservationModule G) (coord : G ≃ₜ (sigma → ℝ)) (b : Basis iota ℝ V.space)
    (A : iota → iota → sigma → ℚ) (L : Polynomial ℚ)
    (LG : sigma → MvPolynomial sigma ℚ) (l : G → (sigma → ℝ))
    (hl : ∀ g s, l g s = aeval (coord g) (LG s))
    (e : ((sigma → ℝ) × V.space) ≃ ObservationGroup V) :
    letI := Algebra.restrictScalars ℚ ℝ (Module.End ℝ V.space)
    (∀ a : ObservationGroup V, e.symm a = (l a.base,
      Polynomial.aeval (observationCoordinateDifferential V b A (l a.base)) L a.obs)) →
    ∀ a s, observationLogCoordinates V b e a s =
      aeval (observationFullCoordinates V coord b a) (observationInversePolynomial LG A L s) := by
  let := Algebra.restrictScalars ℚ ℝ (Module.End ℝ V.space)
  intro hi a s
  change observationTangentCoordinates V b (e.symm a) s = _
  rw [hi]
  cases s with
  | inl s =>
    change l a.base s = aeval (observationFullCoordinates V coord b a) (rename Sum.inl (LG s))
    rw [hl, aeval_rename]
    rfl
  | inr i =>
    change b.equivFun (Polynomial.aeval (observationCoordinateDifferential V b A (l a.base)) L a.obs) i =
      aeval (observationFullCoordinates V coord b a)
        (aeval (Sum.elim (fun s => rename Sum.inl (LG s)) (fun j => X (Sum.inr j)))
          (fiberOperatorPolynomial A L i))
    rw [← fiber_operator_polynomial_eval, comp_aeval_apply]
    apply congrArg (fun z : (sigma ⊕ iota) → ℝ => aeval z (fiberOperatorPolynomial A L i))
    funext j
    cases j with
    | inl s =>
      simpa only [Sum.elim_inl, aeval_rename, Function.comp_def,
        observation_full_coordinates_base] using hl a.base s
    | inr i => simp only [Sum.elim_inr, aeval_X, observation_full_coordinates_fiber]

end GMZP0
