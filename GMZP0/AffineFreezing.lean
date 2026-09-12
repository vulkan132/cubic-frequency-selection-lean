import GMZP0.AffineChildren
import GMZP0.FreezingStep

/-! Complete affine freezing reduced to the explicitly unproved degree-zero core case.
The child list and the no-relation estimate are constructed, not hypothesized. -/
noncomputable section
namespace GMZP0

/-- The exact degree-zero core interface, with constants preceding N and every horizontal coefficient.
This proposition is not established here and is not declared as an axiom. -/
def UniformConstantFreezing : Prop :=
  ∀ s : ℝ, 0 < s → s ≤ 1 → ∃ Q N₀ : ℕ, 0 < Q ∧ 0 < N₀ ∧
    ∀ N : ℕ, N₀ ≤ N → ∀ b : Fin N → Frequency,
      FiniteMinorEstimate Q N s (fun z : Base N => b z.1)

/-- The actual no-relation point set in the original box. -/
def affineNoRelationPoints {N : ℕ} (Q : ℕ) (E : ℝ) (a : Fin N → Frequency) : Finset (Base N) := by
  classical
  exact Finset.univ.filter (fun z => ¬ AffineTopRelation Q E N (a z.1))

/-- Membership records precisely failure of the current row's slope relation. -/
theorem mem_affineNoRelationPoints {N : ℕ} (Q : ℕ) (E : ℝ) (a : Fin N → Frequency) (z : Base N) :
    z ∈ affineNoRelationPoints Q E a ↔ ¬ AffineTopRelation Q E N (a z.1) := by
  classical
  simp only [affineNoRelationPoints, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The complementary actual point set consists of the relation rows where child approximation is proved. -/
theorem not_mem_affineNoRelationPoints {N : ℕ} (Q : ℕ) (E : ℝ) (a : Fin N → Frequency) (z : Base N) :
    z ∉ affineNoRelationPoints Q E a ↔ AffineTopRelation Q E N (a z.1) := by
  classical
  simp only [mem_affineNoRelationPoints, not_not]

/-- Constant-in-y children and the checked affine no-relation bound yield full affine freezing,
conditional only on the exact degree-zero core interface stated above. -/
theorem uniform_affine_freezing_of_constant (hconstant : UniformConstantFreezing)
    (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) :
    ∃ Q N₀ : ℕ, 0 < Q ∧ 0 < N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ a b : Fin N → Frequency,
      FiniteMinorEstimate Q N s (affineOriginalProfile a b) := by
  classical
  obtain ⟨Q₁, E, N₁, hQ₁, hE, hN₁, hno⟩ := uniform_affine_no_relation_operator (s / 3) (by positivity)
  obtain ⟨J, hJ, hlist⟩ := uniform_affine_constant_children Q₁ hQ₁ E hE.le
    (s / (12 * Real.pi)) (by positivity)
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  have hJ1 : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have hroot : (1 : ℝ) ≤ Real.sqrt J := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg J), Real.sqrt_nonneg (J : ℝ)]
  have ht : 0 < s / (3 * Real.sqrt (J : ℝ)) := by positivity
  have ht1 : s / (3 * Real.sqrt (J : ℝ)) ≤ 1 := by
    apply (div_le_one (by positivity : 0 < 3 * Real.sqrt (J : ℝ))).2
    linarith
  obtain ⟨Q₂, N₂, hQ₂, hN₂, hbase⟩ := hconstant _ ht ht1
  refine ⟨2 * Q₂, max N₁ N₂, by positivity, hN₁.trans_le (le_max_left _ _), ?_⟩
  intro N hN a b
  have hn : 0 < N := hN₁.trans_le ((le_max_left _ _).trans hN)
  obtain ⟨offset, hassign⟩ := hlist N hn
  obtain ⟨j, hj⟩ := hassign a
  let p := affineOriginalProfile a b
  let A := affineNoRelationPoints Q₁ E a
  apply finiteMinorEstimate_freezing_step hn hJ s hs hs1 (2 * Q₂) (fun _ => Q₂)
    (fun _ => le_rfl) p (affineConstantChild b offset) j A
  · intro z hz _
    have hrel := (not_mem_affineNoRelationPoints Q₁ E a z).1 hz
    simpa only [freezing_manuscript_circle_scale] using hj b z hrel
  · intro g
    apply hno N ((le_max_left _ _).trans hN) a b
      (restrictOutputMask (minorOutputMask (2 * Q₂) N p) A)
      (restrictOutputMask_bound _ A (minorOutputMask_bound _ _ _)) _ g
    intro x hx y
    simp only [restrictOutputMask, A, mem_affineNoRelationPoints, hx, not_true_eq_false, if_false]
  · intro i
    exact hbase N ((le_max_right _ _).trans hN) (fun x => b x + offset i)

end GMZP0
