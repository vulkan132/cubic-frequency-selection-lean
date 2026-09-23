import GMZP0.TriangularIntegerCell
import Mathlib.Algebra.Algebra.Rat

/-! The actual inverse coordinate polynomials are derived recursively from
the joint rational law and strict triangular left law. No inverse formula
is supplied, and the original identity coordinate is retained. -/
noncomputable section
open MvPolynomial
namespace GMZP0

/-- Solve the coordinates of the original inverse in strict prefix order.
The rational identity vector is kept explicitly rather than silently set to zero. -/
def rationalTriangularInversePolynomial {m : ℕ}
    (p : Fin m → MvPolynomial (Fin m ⊕ Fin m) ℚ) (c : Fin m → ℚ)
    (i : Fin m) : MvPolynomial (Fin m) ℚ :=
  C (c i) - MvPolynomial.aeval (Sum.elim X (fun j =>
    if _h : j.val < i.val then rationalTriangularInversePolynomial p c j else 0)) (p i)
termination_by i.val

/-- The recursive rational polynomial equals the coordinate of the actual
group inverse at every original point, including arbitrary real coordinates. -/
theorem rational_triangular_inverse_polynomial_eval
    {G : Type*} [Group G] {m : ℕ} (coord : G ≃ (Fin m → ℝ))
    (p : Fin m → MvPolynomial (Fin m ⊕ Fin m) ℚ)
    (hjoint : ∀ g h i, coord (g * h) i = MvPolynomial.aeval (Sum.elim (coord g) (coord h)) (p i))
    (q : G → Fin m → MvPolynomial (Fin m) ℝ)
    (htri : ∀ g u i, coord (g * u) i = coord u i + MvPolynomial.aeval (coord u) (q g i))
    (hlow : ∀ g i d, d ∈ (q g i).support → ∀ j ∈ d.support, j.val < i.val)
    (c : Fin m → ℚ) (hc : ∀ i, coord 1 i = (c i : ℝ)) :
    ∀ i : Fin m, ∀ g : G,
      MvPolynomial.aeval (coord g) (rationalTriangularInversePolynomial p c i) = coord g⁻¹ i := by
  classical
  intro i
  induction i using (measure (fun j : Fin m => j.val)).wf.induction with
  | h i ih =>
    intro g
    let y : Fin m → ℝ := fun j => if j.val < i.val then coord g⁻¹ j else 0
    have hyp (j : Fin m) :
        MvPolynomial.aeval (coord g)
          (if h : j.val < i.val then rationalTriangularInversePolynomial p c j else 0) = y j := by
      by_cases hj : j.val < i.val
      · simp only [dif_pos hj, y, if_pos hj]
        exact ih j hj g
      · simp only [dif_neg hj, map_zero, y, if_neg hj]
    have hsub : MvPolynomial.aeval (coord g)
        (MvPolynomial.aeval (Sum.elim X (fun j =>
          if h : j.val < i.val then rationalTriangularInversePolynomial p c j else 0)) (p i)) =
        MvPolynomial.aeval (Sum.elim (coord g) y) (p i) := by
      rw [MvPolynomial.comp_aeval_apply]
      apply congrArg (fun v : (Fin m ⊕ Fin m) → ℝ => MvPolynomial.aeval v (p i))
      funext j
      cases j with
      | inl j => simp
      | inr j => exact hyp j
    have hprefix : MvPolynomial.aeval y (q g i) = MvPolynomial.aeval (coord g⁻¹) (q g i) :=
      polynomial_eval_eq_of_prefix i (q g i) (hlow g i) y (coord g⁻¹)
        (fun j hj => if_pos hj)
    have hy : coord (coord.symm y) = y := coord.apply_symm_apply y
    have hp := hjoint g (coord.symm y) i
    rw [htri, hy] at hp
    have hzero : y i = 0 := if_neg (lt_irrefl _)
    rw [hzero, zero_add, hprefix] at hp
    have hinv := htri g g⁻¹ i
    rw [mul_inv_cancel, hc] at hinv
    rw [rationalTriangularInversePolynomial, map_sub, MvPolynomial.aeval_C, hsub, ← hp]
    change (c i : ℝ) - MvPolynomial.aeval (coord g⁻¹) (q g i) = coord g⁻¹ i
    linarith

/-- Original integer identity coordinates and literal rational/triangular
group laws construct one rational array for all original inverse coordinates. -/
theorem original_group_rational_inverse_polynomials
    {G : Type*} [Group G] {m : ℕ} (coord : G ≃ (Fin m → ℝ)) (Gamma : Subgroup G)
    (hint : ∀ gamma : Gamma, ∃ z : Fin m → ℤ, coord gamma = fun i => (z i : ℝ))
    (p : Fin m → MvPolynomial (Fin m ⊕ Fin m) ℚ)
    (hjoint : ∀ g h i, coord (g * h) i = MvPolynomial.aeval (Sum.elim (coord g) (coord h)) (p i))
    (q : G → Fin m → MvPolynomial (Fin m) ℝ)
    (htri : ∀ g u i, coord (g * u) i = coord u i + MvPolynomial.aeval (coord u) (q g i))
    (hlow : ∀ g i d, d ∈ (q g i).support → ∀ j ∈ d.support, j.val < i.val) :
    ∃ r : Fin m → MvPolynomial (Fin m) ℚ, ∀ g i,
      coord g⁻¹ i = MvPolynomial.aeval (coord g) (r i) := by
  obtain ⟨z, hz⟩ := hint ⟨1, Gamma.one_mem⟩
  have hc (i : Fin m) : coord 1 i = ((z i : ℚ) : ℝ) := by
    simpa only [Rat.cast_intCast] using congrFun hz i
  exact ⟨rationalTriangularInversePolynomial p (fun i => (z i : ℚ)), fun g i =>
    (rational_triangular_inverse_polynomial_eval coord p hjoint q htri hlow _ hc i g).symm⟩

end GMZP0
