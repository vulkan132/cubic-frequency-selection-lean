import GMZP0.HorizontalBlocks

/-! Nonparallel parabola collisions and exact nonzero horizontal kernel entries. -/

noncomputable section
open scoped BigOperators ComplexConjugate
namespace GMZP0

/-- The finite endpoint equality is equivalent to the original signed integer collision. -/
theorem endpointIndex_collision_iff {N : ℕ} (z w : Base N) (r s : Fin N) :
    endpointIndex z r = endpointIndex w s ↔
      ((label s : ℤ) = (label r : ℤ) - ((basePoint w).1 - (basePoint z).1) ∧
        (basePoint w).2 = (basePoint z).2 +
          2 * ((basePoint w).1 - (basePoint z).1) * (label r : ℤ) -
            ((basePoint w).1 - (basePoint z).1) ^ 2) := by
  rw [← integer_parabola_collision]
  constructor
  · intro h
    have he := congrArg inputPoint h
    rw [← endpoint_eq_inputPoint, ← endpoint_eq_inputPoint] at he
    exact ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩
  · rintro ⟨hx, hy⟩
    apply inputPoint_injective
    rw [← endpoint_eq_inputPoint, ← endpoint_eq_inputPoint]
    exact Prod.ext hx hy

/-- Two distinct horizontal fibers have at most one pair of labels joining fixed base points. -/
theorem nonparallel_collision_unique {N : ℕ} (z w : Base N) (hx : z.1 ≠ w.1)
    (r s t u : Fin N) (hrs : endpointIndex z r = endpointIndex w s)
    (htu : endpointIndex z t = endpointIndex w u) : r = t ∧ s = u := by
  have h1 := (endpointIndex_collision_iff z w r s).1 hrs
  have h2 := (endpointIndex_collision_iff z w t u).1 htu
  have hh : (basePoint w).1 - (basePoint z).1 ≠ 0 := by
    intro hzero
    apply hx
    apply Fin.ext
    simp only [basePoint] at hzero
    omega
  have heq : (2 * ((basePoint w).1 - (basePoint z).1)) * ((label r : ℤ) - (label t : ℤ)) = 0 := by
    nlinarith only [h1.2, h2.2]
  have hlabel := (mul_eq_zero.mp heq).resolve_left (mul_ne_zero (by decide) hh)
  have hrt : r = t := by
    apply Fin.ext
    simp only [label, Nat.cast_add, Nat.cast_one] at hlabel
    omega
  subst t
  exact ⟨rfl, endpointIndex_label_injective w (hrs.symm.trans htu)⟩

/-- Fixing the first label determines the target point and target label on a chosen fiber. -/
theorem collision_target_unique {N : ℕ} (z : Base N) (x' : Fin N) (r : Fin N)
    (v v' : Fin (N ^ 2)) (s s' : Fin N)
    (hv : endpointIndex z r = endpointIndex (x', v) s)
    (hv' : endpointIndex z r = endpointIndex (x', v') s') : v = v' ∧ s = s' := by
  have h := endpointIndex_same_horizontal (x', v) (x', v') s s' rfl (hv.symm.trans hv')
  exact ⟨congrArg Prod.snd h.1, h.2⟩

/-- Every nonzero horizontal kernel entry consists of this one original collision. -/
theorem horizontalKernel_of_collision {N : ℕ} (p : Base N → Frequency)
    (x x' : Fin N) (hx : x ≠ x') (y v : Fin (N ^ 2)) (r s : Fin N)
    (he : endpointIndex (x, y) r = endpointIndex (x', v) s) :
    horizontalKernel N p x x' y v =
      cubicPhase (p (x, y)) r * conj (cubicPhase (p (x', v)) s) / (N : ℂ) ^ 2 := by
  classical
  rw [horizontalKernel, responseKernel_gram]
  have hterm : ∀ t u : Fin N,
      (if endpointIndex (x, y) t = endpointIndex (x', v) u then
        cubicPhase (p (x, y)) t * conj (cubicPhase (p (x', v)) u) else 0) =
      if t = r then (if u = s then cubicPhase (p (x, y)) r *
        conj (cubicPhase (p (x', v)) s) else 0) else 0 := by
    intro t u
    by_cases htu : endpointIndex (x, y) t = endpointIndex (x', v) u
    · obtain ⟨ht, hu⟩ := nonparallel_collision_unique (x, y) (x', v) hx t u r s htu he
      subst t
      subst u
      simp [he]
    · by_cases ht : t = r
      · subst t
        have hu : u ≠ s := fun hu => htu (hu ▸ he)
        simp [htu, hu]
      · simp [htu, ht]
  simp_rw [hterm]
  simp

theorem horizontalKernel_no_collision {N : ℕ} (p : Base N → Frequency)
    (x x' : Fin N) (y v : Fin (N ^ 2))
    (hne : ∀ r s : Fin N, endpointIndex (x, y) r ≠ endpointIndex (x', v) s) :
    horizontalKernel N p x x' y v = 0 := by
  classical
  simp only [horizontalKernel, responseKernel_gram, hne, if_false,
    Finset.sum_const_zero, zero_div]

/-- The absolute size is N^(-2), precisely when an original collision exists. -/
theorem horizontalKernel_norm {N : ℕ} (p : Base N → Frequency)
    (x x' : Fin N) (hx : x ≠ x') (y v : Fin (N ^ 2)) :
    ‖horizontalKernel N p x x' y v‖ =
      if ∃ r s : Fin N, endpointIndex (x, y) r = endpointIndex (x', v) s
        then (N : ℝ)⁻¹ ^ 2 else 0 := by
  classical
  split_ifs with he
  · obtain ⟨r, s, hrs⟩ := he
    rw [horizontalKernel_of_collision p x x' hx y v r s hrs]
    simp only [norm_div, norm_mul, norm_pow, Complex.norm_conj, norm_cubicPhase,
      one_mul, Complex.norm_natCast, one_div, inv_pow]
  · rw [horizontalKernel_no_collision p x x' y v]
    · exact norm_zero
    · intro r s hrs
      exact he ⟨r, s, hrs⟩

end GMZP0
