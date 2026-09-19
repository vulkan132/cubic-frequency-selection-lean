import GMZP0.BoundaryOrbitEstimate

/-! Transfer the manuscript's original N-normalized sum to the complete
interval mean, retaining the original cardinality and every orbit point. -/
noncomputable section
open MeasureTheory
namespace GMZP0
universe uI

/-- A large original N-normalized bounded sum forces a long nonempty
index set and a large full uniform mean when its cardinality is at most N. -/
theorem large_N_normalized_sum {I : Type*} [Fintype I]
    (N : ℕ) (hN : 0 < N) (hcard : Fintype.card I ≤ N)
    (F : I → ℂ) (hF : ∀ i, ‖F i‖ ≤ 1) (gamma : ℝ) (hg : 0 < gamma)
    (hlarge : gamma < ‖(∑ i, F i) / (N : ℂ)‖) :
    gamma * (N : ℝ) < Fintype.card I ∧ 0 < Fintype.card I ∧
      gamma < ‖complexUniformMean F‖ := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hbound : ‖∑ i, F i‖ ≤ (Fintype.card I : ℝ) := by
    apply (norm_sum_le _ _).trans
    simpa using Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hF i)
  rw [norm_div, Complex.norm_natCast] at hlarge
  have hbig := (lt_div_iff₀ hNr).mp hlarge
  have hlength : gamma * (N : ℝ) < Fintype.card I := hbig.trans_le hbound
  have hcpos : (0 : ℝ) < Fintype.card I := (mul_pos hg hNr).trans hlength
  refine ⟨hlength, by exact_mod_cast hcpos, ?_⟩
  rw [complexUniformMean, norm_div, Complex.norm_natCast]
  apply (lt_div_iff₀ hcpos).mpr
  exact (mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) hg.le).trans_lt hbig

/-- The same discrepancy tolerance applies to the full original
N-normalized orbit, without deleting endpoints or replacing its response. -/
theorem N_normalized_orbit_forcing {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (mu : Measure X) (psi : X → ℂ) (hpsi : ∀ x, ‖psi x‖ ≤ 1)
    (gamma alpha : ℝ) (hg : 0 < gamma)
    (hforce : ∀ (I : Type uI) [Fintype I] (u : I → X),
      gamma < ‖complexUniformMean (fun i => psi (u i))‖ → ¬ LipschitzOrbitDiscrepancy mu u alpha) :
    ∀ (N : ℕ), 0 < N → ∀ (I : Type uI) [Fintype I], Fintype.card I ≤ N →
      ∀ u : I → X, gamma < ‖(∑ i, psi (u i)) / (N : ℂ)‖ →
        gamma * (N : ℝ) < Fintype.card I ∧ ¬ LipschitzOrbitDiscrepancy mu u alpha := by
  intro N hN I _ hcard u hlarge
  have h := large_N_normalized_sum N hN hcard (fun i => psi (u i))
    (fun i => hpsi (u i)) gamma hg hlarge
  exact ⟨h.1, hforce I u h.2.2⟩

/-- Without the original cardinality bound, dividing by N can amplify a
small uniform mean. This exact obstruction does not concern P0 itself. -/
theorem interval_normalization_cardinality_obstruction :
    (3 / 2 : ℝ) < ‖(∑ _i : Fin 2, (1 : ℂ)) / (1 : ℂ)‖ ∧
      ‖complexUniformMean (fun _i : Fin 2 => (1 : ℂ))‖ ≤ (3 / 2 : ℝ) := by
  norm_num [complexUniformMean]

end GMZP0
