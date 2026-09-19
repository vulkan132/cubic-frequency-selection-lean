import GMZP0.TriangularCoordinates
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith

/-! Exact integer rounding in a triangular half-open coordinate cell.
All coordinates are retained, including at cell faces. The correction at
coordinate i may depend on all earlier coordinates, but not on i or later ones. -/
noncomputable section
namespace GMZP0

/-- Two integer translates of the same real number cannot lie in one half-open unit interval. -/
theorem integer_half_open_cell_unique (a r : ℝ) (u v : ℤ)
    (hu : (u : ℝ) + r ∈ Set.Ico a (a + 1))
    (hv : (v : ℝ) + r ∈ Set.Ico a (a + 1)) : u = v := by
  have hlo : (-1 : ℝ) < ((u - v : ℤ) : ℝ) := by
    push_cast
    have := hu.1
    have := hv.2
    linarith
  have hhi : ((u - v : ℤ) : ℝ) < 1 := by
    push_cast
    have := hu.2
    have := hv.1
    linarith
  have hlo' : (-1 : ℤ) < u - v := by exact_mod_cast hlo
  have hhi' : u - v < (1 : ℤ) := by exact_mod_cast hhi
  omega

/-- A triangular correction has a unique integer reduction into every translated half-open unit cell. -/
theorem triangular_integer_cell {m : ℕ} (q : Fin m → (Fin m → ℝ) → ℝ) (a : Fin m → ℝ)
    (htri : ∀ i u v, (∀ j, j.val < i.val → u j = v j) → q i u = q i v) :
    ∃! z : Fin m → ℤ, ∀ i, (z i : ℝ) + q i (fun j => (z j : ℝ)) ∈ Set.Ico (a i) (a i + 1) := by
  classical
  have hex : ∀ n : ℕ, n ≤ m → ∃ z : Fin m → ℤ,
      ∀ i, i.val < n → (z i : ℝ) + q i (fun j => (z j : ℝ)) ∈ Set.Ico (a i) (a i + 1) := by
    intro n
    induction n with
    | zero =>
        intro _
        exact ⟨fun _ => 0, fun i hi => by omega⟩
    | succ n ih =>
        intro hnm
        obtain ⟨z, hz⟩ := ih (by omega)
        let i : Fin m := ⟨n, by omega⟩
        let r : ℝ := q i (fun j => (z j : ℝ)) - a i
        let z' : Fin m → ℤ := Function.update z i (-⌊r⌋)
        have hq (j : Fin m) (hj : j.val ≤ n) :
            q j (fun k => (z' k : ℝ)) = q j (fun k => (z k : ℝ)) := by
          apply htri
          intro k hk
          have hki : k ≠ i := by intro he; have he' := congrArg Fin.val he; dsimp [i] at he'; omega
          simp only [z', Function.update_of_ne hki]
        refine ⟨z', ?_⟩
        intro j hj
        by_cases hjn : j.val < n
        · have hji : j ≠ i := by intro he; have he' := congrArg Fin.val he; dsimp [i] at he'; omega
          rw [hq j (by omega)]
          simpa only [z', Function.update_of_ne hji] using hz j hjn
        · have hji : j = i := Fin.ext (by dsimp [i]; omega)
          subst j
          rw [hq i (by rfl)]
          simp only [z', Function.update_self, Int.cast_neg]
          have h0 := Int.floor_le r
          have h1 := Int.lt_floor_add_one r
          have hr : r = q i (fun j => (z j : ℝ)) - a i := rfl
          constructor <;> linarith only [h0, h1, hr]
  obtain ⟨z, hz⟩ := hex m le_rfl
  have hzall (i : Fin m) := hz i i.isLt
  refine ⟨z, hzall, ?_⟩
  intro w hw
  have hprefix : ∀ n : ℕ, ∀ i : Fin m, i.val < n → w i = z i := by
    intro n
    induction n with
    | zero => intro i hi; omega
    | succ n ih =>
        intro i hi
        have hq : q i (fun j => (w j : ℝ)) = q i (fun j => (z j : ℝ)) := by
          apply htri
          intro j hj
          rw [ih j (by omega)]
        apply integer_half_open_cell_unique (a i) (q i (fun j => (z j : ℝ))) (w i) (z i)
        · rw [← hq]
          exact hw i
        · exact hzall i
  funext i
  exact hprefix m i i.isLt

/-- Actual strictly lower-coordinate polynomial support gives the required prefix dependence. -/
theorem polynomial_eval_eq_of_prefix {m : ℕ} (i : Fin m) (P : MvPolynomial (Fin m) ℝ)
    (hlow : ∀ d ∈ P.support, ∀ j ∈ d.support, j.val < i.val)
    (u v : Fin m → ℝ) (huv : ∀ j, j.val < i.val → u j = v j) :
    MvPolynomial.aeval u P = MvPolynomial.aeval v P := by
  apply MvPolynomial.eval₂_congr (algebraMap ℝ ℝ) u v
  intro j d hj hd
  exact huv j (hlow d (MvPolynomial.mem_support_iff.mpr hd) j hj)

/-- Dependence on the current coordinate can destroy uniqueness completely. -/
theorem triangular_diagonal_cancellation_obstruction :
    ¬ ∃! z : Fin 1 → ℤ, ∀ i, (z i : ℝ) + (-(z i : ℝ)) ∈ Set.Ico (0 : ℝ) 1 := by
  intro ⟨z, _, huniq⟩
  have h0 := huniq (fun _ => 0) (by intro i; norm_num)
  have h1 := huniq (fun _ => 1) (by intro i; norm_num)
  have h := congrFun (h0.trans h1.symm) 0
  norm_num at h

end GMZP0
