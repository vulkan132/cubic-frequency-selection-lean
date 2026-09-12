import GMZP0.OriginalBlockSchur

noncomputable section
open scoped BigOperators
namespace GMZP0

/-- Disjoint output assignment can double energy even when each individual operator is a contraction. -/
theorem disjoint_assignment_energy_obstruction :
    ∃ K : Bool → Bool → Unit → ℂ,
      (∀ i, KernelEnergyBound (K i) 1) ∧
      ∃ g : Unit → ℂ, finiteEnergy g < finiteEnergy (fun z => kernelAction (K z) g z) := by
  refine ⟨fun i z _ => if i = z then 1 else 0, ?_, fun _ => 1, ?_⟩
  · intro i g
    cases i <;> simp [kernelAction, finiteEnergy]
  · norm_num [finiteEnergy, kernelAction]

/-- The exact pointwise assignment mask; no regularity or rowwise assignment is imposed. -/
def assignmentOutputMask {Z J : Type*} (m : Z → ℂ) (j : Z → J) (i : J) : Z → ℂ := by
  classical
  exact fun z => if j z = i then m z else 0

/-- A single-valued assignment splits finite output energy exactly into disjoint pieces. -/
theorem finiteEnergy_assignment_eq_sum {Z J : Type*} [Fintype Z] [Fintype J]
    (F : J → Z → ℂ) (m : Z → ℂ) (j : Z → J) :
    finiteEnergy (fun z => m z * F (j z) z) =
      ∑ i, finiteEnergy (fun z => assignmentOutputMask m j i z * F i z) := by
  classical
  simp only [finiteEnergy]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  have hi (i : J) : ‖assignmentOutputMask m j i z * F i z‖ ^ 2 =
      if j z = i then ‖m z * F i z‖ ^ 2 else 0 := by
    by_cases h : j z = i <;> simp [assignmentOutputMask, h]
  simp_rw [hi]
  simp

/-- Each piece of an arbitrary assignment inherits the original mask contraction. -/
theorem assignmentOutputMask_bound {Z J : Type*} (m : Z → ℂ) (j : Z → J) (i : J)
    (hm : ∀ z, ‖m z‖ ≤ 1) (z : Z) : ‖assignmentOutputMask m j i z‖ ≤ 1 := by
  classical
  unfold assignmentOutputMask
  split_ifs <;> simp [hm]

/-- A parent minor-arc output mask may be further restricted to any subset of its support. -/
theorem masked_minor_energy_le (Q N : ℕ) (p : Base N → Frequency) (m : Base N → ℂ)
    (hm : ∀ z, ‖m z‖ ≤ 1) (hsupport : ∀ z, m z ≠ 0 → ¬ MajorArc Q N (p z))
    (g : InputBox N → ℂ) :
    finiteEnergy (fun z => m z * finiteResponse N p g z) ≤
      finiteEnergy (fun z => minorOutputMask Q N p z * finiteResponse N p g z) := by
  have he : (fun z => m z * finiteResponse N p g z) =
      fun z => m z * (minorOutputMask Q N p z * finiteResponse N p g z) := by
    funext z
    by_cases hmz : m z = 0
    · simp [hmz]
    · simp [minorOutputMask, hsupport z hmz]
  rw [he]
  exact finiteEnergy_mask_le _ _ hm

/-- An actual minor-arc estimate controls every contractive mask supported on its minor points. -/
theorem masked_finiteMinorEstimate (Q N : ℕ) (p : Base N → Frequency) (m : Base N → ℂ)
    (hm : ∀ z, ‖m z‖ ≤ 1) (hsupport : ∀ z, m z ≠ 0 → ¬ MajorArc Q N (p z))
    (t : ℝ) (hestimate : FiniteMinorEstimate Q N t p) (g : InputBox N → ℂ) :
    finiteEnergy (fun z => m z * finiteResponse N p g z) ≤ t ^ 2 * finiteEnergy g := by
  have h := masked_minor_energy_le Q N p m hm hsupport g
  rw [minorOutputMask_energy] at h
  exact h.trans (hestimate g)

/-- Different child major-arc cutoffs and an arbitrary pointwise assignment are retained exactly. -/
theorem assigned_masked_minor_energy {N J : ℕ}
    (Q : Fin J → ℕ) (p : Fin J → Base N → Frequency) (j : Base N → Fin J)
    (m : Base N → ℂ) (hm : ∀ z, ‖m z‖ ≤ 1)
    (hsupport : ∀ z, m z ≠ 0 → ¬ MajorArc (Q (j z)) N (p (j z) z))
    (t : ℝ) (hestimates : ∀ i, FiniteMinorEstimate (Q i) N t (p i)) (g : InputBox N → ℂ) :
    finiteEnergy (fun z => m z * finiteResponse N (fun z => p (j z) z) g z) ≤
      (J : ℝ) * t ^ 2 * finiteEnergy g := by
  classical
  have he (z : Base N) : finiteResponse N (fun z => p (j z) z) g z =
      finiteResponse N (p (j z)) g z := rfl
  simp_rw [he]
  rw [finiteEnergy_assignment_eq_sum (fun i z => finiteResponse N (p i) g z) m j]
  calc
    _ ≤ ∑ _i : Fin J, t ^ 2 * finiteEnergy g := by
      apply Finset.sum_le_sum
      intro i _
      apply masked_finiteMinorEstimate (Q i) N (p i) (assignmentOutputMask m j i)
        (assignmentOutputMask_bound m j i hm) _ t (hestimates i) g
      intro z hz
      have hj : j z = i := by
        by_contra hn
        exact hz (by simp [assignmentOutputMask, hn])
      have hmz : m z ≠ 0 := by simpa [assignmentOutputMask, hj] using hz
      simpa only [hj] using hsupport z hmz
    _ = _ := by simp [mul_assoc]

/-- The chosen child tolerance exactly compensates for the number of disjoint pieces. -/
theorem assigned_child_error_budget (s : ℝ) {J : ℕ} (hJ : 0 < J) :
    (J : ℝ) * (s / (3 * Real.sqrt (J : ℝ))) ^ 2 = (s / 3) ^ 2 := by
  have hj : (0 : ℝ) < J := by exact_mod_cast hJ
  rw [div_pow, mul_pow, Real.sq_sqrt hj.le]
  field_simp

end GMZP0
