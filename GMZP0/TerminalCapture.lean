import GMZP0.FiniteOperator

/-!
The manuscript's terminal passage from model values and minor-arc energy to finite capture.
Model existence and the uniform operator theorem are explicit outstanding premises.
-/

noncomputable section
open scoped BigOperators
namespace GMZP0

/-- The exact energy budget produced by the manuscript's choice of freezing tolerance. -/
theorem freezing_energy_budget (η c : ℝ) (hc : 0 ≤ c) (J : ℕ) (hJ : 0 < J) :
    4 * (J : ℝ) * (η * Real.sqrt c / (8 * Real.sqrt (J : ℝ))) ^ 2 = c * η ^ 2 / 16 := by
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  simp only [div_pow, mul_pow, Real.sq_sqrt hc, Real.sq_sqrt (Nat.cast_nonneg J)]
  field_simp
  ring

/-- The list precedes all original data and model fields; only the retained assignment depends on them. -/
theorem finite_capture_from_model_energy (Q : ℕ) (hQ : 1 ≤ Q) (ε : ℝ) (hε : 0 < ε) :
    ∃ L : ℕ, 1 ≤ L ∧ ∀ N : ℕ, 1 ≤ N → ∃ β : Fin L → Frequency,
      ∀ (f : ℤ × ℤ → ℂ) (θ p : Base N → Frequency) (lam : Base N → ℂ)
        (μ : Base N → ℝ) (A : Finset (Base N)) (η c E : ℝ),
        (∀ w, ‖f w‖ ≤ 1) → 0 < η → ε ≤ η → 0 ≤ c →
        (∀ z ∈ A, 0 ≤ μ z) → c ≤ ∑ z ∈ A, μ z →
        (∀ z ∈ A, ‖lam z‖ = 1) →
        (∀ z ∈ A, η ≤ (lam z * response N f z (θ z)).re) →
        (∀ z ∈ A, cubicDistance N (θ z) (p z) ≤ ε / 2) →
        (∑ z ∈ minorPoints Q N p A, μ z * ‖response N f z (p z)‖ ^ 2) ≤ E →
        E ≤ c * η ^ 2 / 16 →
        ∃ A' : Finset (Base N), ∃ j : Base N → Fin L,
          A' ⊆ A ∧ c / 2 ≤ ∑ z ∈ A', μ z ∧
          ∀ z ∈ A', cubicDistance N (θ z) (β (j z)) ≤ ε := by
  classical
  obtain ⟨L, hL, hlist⟩ := majorArc_universal_list Q hQ ε hε
  refine ⟨L, hL, ?_⟩
  intro N hN
  obtain ⟨β, hβ⟩ := hlist N hN
  refine ⟨β, ?_⟩
  intro f θ p lam μ A η c E hf hη hεη hc hμ hmass hlam hresponse hclose henergy hbudget
  have hcloseη (z : Base N) (hz : z ∈ A) : cubicDistance N (θ z) (p z) ≤ η / 2 := by
    have h := hclose z hz
    linarith
  have hmajor := major_mass_of_minor_energy hN Q f hf θ p lam μ A η c E hη
    hμ hmass hlam hresponse hcloseη henergy
  have hquot : E / (η / 2) ^ 2 ≤ c / 4 := by
    apply (div_le_iff₀ (sq_pos_of_pos (by positivity : 0 < η / 2))).2
    nlinarith
  let A' := majorPoints Q N p A
  have hmass' : c / 2 ≤ ∑ z ∈ A', μ z := by
    dsimp [A']
    linarith
  have hsubset : A' ⊆ A := by
    intro z hz
    exact (Finset.mem_filter.mp hz).1
  have hchoice : ∀ z : Base N, ∃ i : Fin L,
      z ∈ A' → cubicDistance N (θ z) (β i) ≤ ε := by
    intro z
    by_cases hz : z ∈ A'
    · obtain ⟨hzA, hzmajor⟩ := Finset.mem_filter.mp hz
      obtain ⟨i, hi⟩ := hβ (p z) hzmajor
      refine ⟨i, fun _ => ?_⟩
      have htri := cubicDistance_triangle N (θ z) (p z) (β i)
      have hfirst := hclose z hzA
      linarith
    · exact ⟨⟨0, hL⟩, fun h => False.elim (hz h)⟩
  choose j hj using hchoice
  exact ⟨A', j, hsubset, hmass', hj⟩

/-- Complete terminal interface from model approximation and true finite operator estimates.
The model family and its estimates are hypotheses; their uniform existence remains to be proved. -/
theorem finite_capture_from_model_operators (Q : ℕ) (hQ : 1 ≤ Q) (ε : ℝ) (hε : 0 < ε) :
    ∃ L : ℕ, 1 ≤ L ∧ ∀ N : ℕ, 1 ≤ N → ∃ β : Fin L → Frequency,
      ∀ (J : ℕ), 1 ≤ J →
      ∀ (f : ℤ × ℤ → ℂ) (θ : Base N → Frequency) (p : Fin J → Base N → Frequency)
        (ι : Base N → Fin J) (lam : Base N → ℂ) (μ : Base N → ℝ)
        (A : Finset (Base N)) (η c : ℝ),
        (∀ w, ‖f w‖ ≤ 1) → 0 < η → ε ≤ η → 0 ≤ c →
        (∀ z ∈ A, 0 ≤ μ z ∧ μ z ≤ (N : ℝ)⁻¹ ^ 3) → c ≤ ∑ z ∈ A, μ z →
        (∀ z ∈ A, ‖lam z‖ = 1) →
        (∀ z ∈ A, η ≤ (lam z * response N f z (θ z)).re) →
        (∀ z ∈ A, cubicDistance N (θ z) (p (ι z) z) ≤ ε / 2) →
        (∀ i : Fin J, FiniteMinorEstimate Q N (η * Real.sqrt c / (8 * Real.sqrt (J : ℝ))) (p i)) →
        ∃ A' : Finset (Base N), ∃ j : Base N → Fin L,
          A' ⊆ A ∧ c / 2 ≤ ∑ z ∈ A', μ z ∧
          ∀ z ∈ A', cubicDistance N (θ z) (β (j z)) ≤ ε := by
  obtain ⟨L, hL, hlist⟩ := finite_capture_from_model_energy Q hQ ε hε
  refine ⟨L, hL, ?_⟩
  intro N hN
  obtain ⟨β, hβ⟩ := hlist N hN
  refine ⟨β, ?_⟩
  intro J hJ f θ p ι lam μ A η c hf hη hεη hc hμ hmass hlam hresponse hclose hestimates
  let s := η * Real.sqrt c / (8 * Real.sqrt (J : ℝ))
  have henergy := finite_estimates_assigned_energy hN Q s f hf p ι A μ
    (fun z hz => (hμ z hz).2) hestimates
  have hbudget : 4 * (J : ℝ) * s ^ 2 ≤ c * η ^ 2 / 16 :=
    (freezing_energy_budget η c hc J hJ).le
  exact hβ f θ (fun z => p (ι z) z) lam μ A η c (4 * (J : ℝ) * s ^ 2)
    hf hη hεη hc (fun z hz => (hμ z hz).1) hmass hlam hresponse hclose henergy hbudget

end GMZP0
