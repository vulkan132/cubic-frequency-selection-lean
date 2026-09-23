import GMZP0.FiniteDerivativeTower

/-! Global uniqueness for a strictly triangular differential equation.
No existence or subgroup law is assumed by this uniqueness argument. -/
noncomputable section
namespace GMZP0

/-- The actual initial vector and derivatives determine every coordinate
of a global triangular solution, including dimension zero. -/
theorem triangular_differential_solution_unique {m : ℕ}
    (F : (Fin m → ℝ) → Fin m → ℝ)
    (hprefix : ∀ i x y, (∀ j, j.val < i.val → x j = y j) → F x i = F y i)
    (f g : ℝ → Fin m → ℝ)
    (hf : ∀ t i, HasDerivAt (fun s => f s i) (F (f t) i) t)
    (hg : ∀ t i, HasDerivAt (fun s => g s i) (F (g t) i) t)
    (hzero : f 0 = g 0) : ∀ t, f t = g t := by
  have he : ∀ i : Fin m, ∀ t, f t i = g t i := by
    intro i
    induction i using (measure (fun j : Fin m => j.val)).wf.induction with
    | h i ih =>
      apply real_functions_eq_of_derivative_and_initial
        (fun t => f t i) (fun t => g t i) (fun t => F (f t) i)
      · exact fun t => hf t i
      · intro t
        rw [hprefix i (f t) (g t) (fun j hj => ih j hj t)]
        exact hg t i
      · exact congrFun hzero i
  exact fun t => funext fun i => he i t

end GMZP0
