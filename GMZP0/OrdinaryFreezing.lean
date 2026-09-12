import GMZP0.OrdinaryTopRelation
import GMZP0.FreezingStep

/-! Actual ordinary children and degree induction.
The modular induction takes MonomialDenseReturns explicitly; MonomialReturns proves
that internal statement and supplies the final ordinary theorem from only the two
external Weyl premises. This is not a proof of P0. -/
noncomputable section
open Polynomial
namespace GMZP0

/-- Exactly the original points in rows lacking a top relation. -/
def ordinaryNoRelationPoints {N : ℕ} (D Q : ℕ) (E : ℝ)
    (P : Fin N → ℝ[X]) : Finset (Base N) := by
  classical
  exact Finset.univ.filter (fun z => ¬ OrdinaryTopRelation D Q E N ((P z.1).coeff D : Frequency))

/-- The actual point set imposes no additional regularity or selection. -/
theorem mem_ordinaryNoRelationPoints {N : ℕ} (D Q : ℕ) (E : ℝ)
    (P : Fin N → ℝ[X]) (z : Base N) :
    z ∈ ordinaryNoRelationPoints D Q E P ↔
      ¬ OrdinaryTopRelation D Q E N ((P z.1).coeff D : Frequency) := by
  classical
  simp only [ordinaryNoRelationPoints, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Each complementary point retains its original top-coefficient witness. -/
theorem not_mem_ordinaryNoRelationPoints {N : ℕ} (D Q : ℕ) (E : ℝ)
    (P : Fin N → ℝ[X]) (z : Base N) :
    z ∉ ordinaryNoRelationPoints D Q E P ↔
      OrdinaryTopRelation D Q E N ((P z.1).coeff D : Frequency) := by
  classical
  simp only [mem_ordinaryNoRelationPoints, not_not]

/-- A true decrease in polynomial degree, using constructed children and actual original masks.
The child count precedes the recursive target, cutoff and threshold, which precede all original data. -/
theorem uniform_ordinary_freezing_step (hW : PolynomialLeadingWeylInput)
    (hR : MonomialDenseReturns) (D : ℕ) (hD : 2 ≤ D)
    (hlower : UniformOrdinaryFreezing (D - 1)) : UniformOrdinaryFreezing D := by
  classical
  intro s hs hs1
  obtain ⟨Q₁, E, N₁, hQ₁, hE, hN₁, hno⟩ :=
    uniform_ordinary_no_relation_operator hW hR D hD (s / 3) (by positivity)
  obtain ⟨J, hJ, hlist⟩ := uniform_ordinary_lower_children Q₁ hQ₁ E hE.le
    (s / (12 * Real.pi)) (by positivity)
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  have hJ1 : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have hroot : (1 : ℝ) ≤ Real.sqrt J := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg J), Real.sqrt_nonneg (J : ℝ)]
  have ht : 0 < s / (3 * Real.sqrt (J : ℝ)) := by positivity
  have ht1 : s / (3 * Real.sqrt (J : ℝ)) ≤ 1 := by
    apply (div_le_one (by positivity : 0 < 3 * Real.sqrt (J : ℝ))).2
    linarith
  obtain ⟨Q₂, N₂, hQ₂, hN₂, hbase⟩ := hlower _ ht ht1
  refine ⟨2 * Q₂, max N₁ N₂, by positivity, hN₁.trans_le (le_max_left _ _), ?_⟩
  intro N hN P hP
  have hn : 0 < N := hN₁.trans_le ((le_max_left _ _).trans hN)
  obtain ⟨c, hassign⟩ := hlist N hn
  obtain ⟨j, hj⟩ := hassign D (fun x => ((P x).coeff D : Frequency))
  let p := ordinaryOriginalProfile P
  let A := ordinaryNoRelationPoints D Q₁ E P
  let child : Fin J → Fin N → ℝ[X] := fun i x => ordinaryChildPolynomial D (P x) (c i)
  apply finiteMinorEstimate_freezing_step hn hJ s hs hs1 (2 * Q₂) (fun _ => Q₂)
    (fun _ => le_rfl) p (fun i => ordinaryOriginalProfile (child i)) j A
  · intro z hz _
    have hrel := (not_mem_ordinaryNoRelationPoints D Q₁ E P z).1 hz
    simpa only [freezing_manuscript_circle_scale] using hj P (fun _ => rfl) z hrel
  · intro g
    apply hno N ((le_max_left _ _).trans hN) P hP
      (restrictOutputMask (minorOutputMask (2 * Q₂) N p) A)
      (restrictOutputMask_bound _ A (minorOutputMask_bound _ _ _)) _ g
    intro x hx y
    simp only [restrictOutputMask, A, mem_ordinaryNoRelationPoints, hx, not_true_eq_false, if_false]
  · intro i
    exact hbase N ((le_max_right _ _).trans hN) (child i)
      (fun x => ordinaryChildPolynomial_degree D (by omega) (P x) (hP x) (c i))

/-- Finite ordinary degree induction is modular in the nonlinear return statement.
MonomialReturns supplies its proved witness. General structural freezing is separate. -/
theorem uniform_ordinary_freezing_of_returns (hW₀ : CubicTwoCoefficientWeylInput)
    (hW : PolynomialLeadingWeylInput) (hR : MonomialDenseReturns) (D : ℕ) :
    UniformOrdinaryFreezing D := by
  induction D using Nat.strong_induction_on with
  | h D ih =>
    by_cases hzero : D = 0
    · subst D
      exact uniform_ordinary_freezing_zero hW₀
    by_cases hone : D = 1
    · subst D
      exact uniform_ordinary_freezing_one hW₀
    exact uniform_ordinary_freezing_step hW hR D (by omega) (ih (D - 1) (by omega))

end GMZP0
