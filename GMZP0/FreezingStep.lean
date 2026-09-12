import GMZP0.OperatorStability
import GMZP0.AssignedOperator
import GMZP0.FiniteEnergyTriangle
import GMZP0.MajorArcStability

/-! The final elementary gluing step of freezing, with its recursive premises explicit. -/
noncomputable section
open scoped BigOperators
namespace GMZP0

/-- Restrict an arbitrary output mask to actual original points. -/
def restrictOutputMask {Z : Type*} (m : Z → ℂ) (A : Finset Z) : Z → ℂ := by
  classical
  exact fun z => if z ∈ A then m z else 0

/-- The complementary pointwise piece of the same original mask. -/
def complementOutputMask {Z : Type*} (m : Z → ℂ) (A : Finset Z) : Z → ℂ := by
  classical
  exact fun z => if z ∈ A then 0 else m z

/-- Restriction preserves every pointwise contraction bound. -/
theorem restrictOutputMask_bound {Z : Type*} (m : Z → ℂ) (A : Finset Z)
    (hm : ∀ z, ‖m z‖ ≤ 1) (z : Z) : ‖restrictOutputMask m A z‖ ≤ 1 := by
  classical
  by_cases h : z ∈ A <;> simp [restrictOutputMask, h, hm]

/-- Nonzero restricted masks remember both actual point membership and the original nonzero mask. -/
theorem restrictOutputMask_ne_zero {Z : Type*} (m : Z → ℂ) (A : Finset Z) (z : Z) :
    restrictOutputMask m A z ≠ 0 ↔ z ∈ A ∧ m z ≠ 0 := by
  classical
  by_cases h : z ∈ A <;> simp [restrictOutputMask, h]

/-- The complementary output piece is also a contraction. -/
theorem complementOutputMask_bound {Z : Type*} (m : Z → ℂ) (A : Finset Z)
    (hm : ∀ z, ‖m z‖ ≤ 1) (z : Z) : ‖complementOutputMask m A z‖ ≤ 1 := by
  classical
  by_cases h : z ∈ A <;> simp [complementOutputMask, h, hm]

/-- A nonzero complementary mask preserves nonmembership and the actual nonzero mask. -/
theorem complementOutputMask_ne_zero {Z : Type*} (m : Z → ℂ) (A : Finset Z) (z : Z) :
    complementOutputMask m A z ≠ 0 ↔ z ∉ A ∧ m z ≠ 0 := by
  classical
  by_cases h : z ∈ A <;> simp [complementOutputMask, h]

/-- The parent output is exactly the no-relation, replacement-error, and assigned-child pieces. -/
theorem outputMask_three_piece_decomposition {Z : Type*}
    (m F G : Z → ℂ) (A : Finset Z) :
    (fun z => m z * F z) =
      (fun z => restrictOutputMask m A z * F z +
        complementOutputMask m A z * (F z - G z) +
        complementOutputMask m A z * G z) := by
  classical
  funext z
  by_cases hz : z ∈ A
  · simp [restrictOutputMask, complementOutputMask, hz]
  · simp only [restrictOutputMask, complementOutputMask, hz, ↓reduceIte, zero_mul, zero_add]
    ring

/-- The core freezing step consumes actual estimates and approximations for supplied children.
It does not assert that those children or the no-relation estimate exist. -/
theorem masked_freezing_step {N J : ℕ} (hN : 0 < N) (hJ : 0 < J)
    (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1)
    (Q : ℕ) (Qchild : Fin J → ℕ) (hQ : ∀ i, 2 * Qchild i ≤ Q)
    (p : Base N → Frequency) (child : Fin J → Base N → Frequency)
    (j : Base N → Fin J) (m : Base N → ℂ) (A : Finset (Base N))
    (hm : ∀ z, ‖m z‖ ≤ 1) (hminor : ∀ z, m z ≠ 0 → ¬ MajorArc Q N (p z))
    (hclose : ∀ z, z ∉ A → m z ≠ 0 →
      ‖p z - child (j z) z‖ ≤ (s / 12) / (2 * Real.pi * (N : ℝ) ^ 3))
    (hnoRelation : ∀ g : InputBox N → ℂ,
      finiteEnergy (fun z => restrictOutputMask m A z * finiteResponse N p g z) ≤
        (s / 3) ^ 2 * finiteEnergy g)
    (hchildren : ∀ i, FiniteMinorEstimate (Qchild i) N
      (s / (3 * Real.sqrt (J : ℝ))) (child i)) (g : InputBox N → ℂ) :
    finiteEnergy (fun z => m z * finiteResponse N p g z) ≤ s ^ 2 * finiteEnergy g := by
  classical
  let mR := complementOutputMask m A
  let q : Base N → Frequency := fun z => child (j z) z
  have hmR : ∀ z, ‖mR z‖ ≤ 1 := complementOutputMask_bound m A hm
  have hR (z : Base N) (hz : mR z ≠ 0) : z ∉ A ∧ m z ≠ 0 := by
    exact (complementOutputMask_ne_zero m A z).mp hz
  have hnear (z : Base N) (hz : mR z ≠ 0) :
      ‖p z - q z‖ ≤ (s / 12) / (2 * Real.pi * (N : ℝ) ^ 3) :=
    hclose z (hR z hz).1 (hR z hz).2
  have hchildMinor (z : Base N) (hz : mR z ≠ 0) :
      ¬ MajorArc (Qchild (j z)) N (child (j z) z) := by
    exact minorArc_nearby_transfer hN Q (Qchild (j z)) (hQ (j z)) (p z) (q z)
      ((hnear z hz).trans (freezing_circle_error_le_unit_scale hN s hs1))
      (hminor z (hR z hz).2)
  have herror := masked_response_circle_stability hN p q mR hmR (s / 12) (by positivity) hnear g
  have hchild := assigned_masked_minor_energy Qchild child j mR hmR hchildMinor
    (s / (3 * Real.sqrt (J : ℝ))) hchildren g
  rw [assigned_child_error_budget s hJ] at hchild
  rw [outputMask_three_piece_decomposition m (finiteResponse N p g) (finiteResponse N q g) A]
  exact finiteEnergy_three_piece_budget _ _ _ (finiteEnergy g) s (finiteEnergy_nonneg g)
    hs.le (hnoRelation g) herror hchild

/-- The same elementary step supplies the pre-existing full original minor-arc interface. -/
theorem finiteMinorEstimate_freezing_step {N J : ℕ} (hN : 0 < N) (hJ : 0 < J)
    (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1)
    (Q : ℕ) (Qchild : Fin J → ℕ) (hQ : ∀ i, 2 * Qchild i ≤ Q)
    (p : Base N → Frequency) (child : Fin J → Base N → Frequency)
    (j : Base N → Fin J) (A : Finset (Base N))
    (hclose : ∀ z, z ∉ A → ¬ MajorArc Q N (p z) →
      ‖p z - child (j z) z‖ ≤ (s / 12) / (2 * Real.pi * (N : ℝ) ^ 3))
    (hnoRelation : ∀ g : InputBox N → ℂ,
      finiteEnergy (fun z => restrictOutputMask (minorOutputMask Q N p) A z * finiteResponse N p g z) ≤
        (s / 3) ^ 2 * finiteEnergy g)
    (hchildren : ∀ i, FiniteMinorEstimate (Qchild i) N
      (s / (3 * Real.sqrt (J : ℝ))) (child i)) : FiniteMinorEstimate Q N s p := by
  classical
  have hm (z : Base N) (hz : minorOutputMask Q N p z ≠ 0) : ¬ MajorArc Q N (p z) := by
    by_contra h
    exact hz (by simp [minorOutputMask, h])
  intro g
  have h := masked_freezing_step hN hJ s hs hs1 Q Qchild hQ p child j (minorOutputMask Q N p) A
    (minorOutputMask_bound Q N p) hm (fun z hz hmz => hclose z hz (hm z hmz)) hnoRelation hchildren g
  rw [minorOutputMask_energy] at h
  exact h

/-- Uniform numerical parameters precede all data; the no-relation input is reduced to actual
compressed-block counts. Structural production of the children and counts remains a premise. -/
theorem uniform_freezing_step_from_compressed_counts (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) :
    ∃ ρ v : ℝ, 0 < ρ ∧ 0 < v ∧ ∃ N₀ : ℕ, 0 < N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ J : ℕ, 0 < J →
      ∀ (Q : ℕ) (Qchild : Fin J → ℕ), (∀ i, 2 * Qchild i ≤ Q) →
      ∀ (p : Base N → Frequency) (child : Fin J → Base N → Frequency)
        (j : Base N → Fin J) (A : Finset (Base N)),
        (∀ z, z ∉ A → ¬ MajorArc Q N (p z) →
          ‖p z - child (j z) z‖ ≤ (s / 12) / (2 * Real.pi * (N : ℝ) ^ 3)) →
        (∀ x : Fin N,
          ((largeBlockNeighbors (outputMaskedKernel (responseKernel N p)
            (restrictOutputMask (minorOutputMask Q N p) A)) Finset.univ v x).card : ℝ) ≤ ρ * N) →
        (∀ i, FiniteMinorEstimate (Qchild i) N
          (s / (3 * Real.sqrt (J : ℝ))) (child i)) →
        FiniteMinorEstimate Q N s p := by
  classical
  obtain ⟨ρ, v, hρ, hv, N₀, hN₀, hbudget⟩ :=
    uniform_compressed_block_error_budget (s / 3) (by positivity)
  refine ⟨ρ, v, hρ, hv, N₀, hN₀, ?_⟩
  intro N hN J hJ Q Qchild hQ p child j A hclose hcount hchildren
  have hn : 0 < N := lt_of_lt_of_le hN₀ hN
  apply finiteMinorEstimate_freezing_step hn hJ s hs hs1 Q Qchild hQ p child j A hclose _ hchildren
  intro g
  have h := masked_original_energy_of_few_large_blocks hn p
    (restrictOutputMask (minorOutputMask Q N p) A) Finset.univ
    (restrictOutputMask_bound _ A (minorOutputMask_bound Q N p)) (by simp)
    v ρ hv.le hρ.le (fun x _ => hcount x) g
  exact h.trans (mul_le_mul_of_nonneg_right (hbudget N hN) (finiteEnergy_nonneg g))

end GMZP0
