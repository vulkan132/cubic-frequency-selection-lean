import GMZP0.ReturnFiber

/-! Preserve actual successful denominators while choosing one dense fiber. -/

noncomputable section
namespace GMZP0

theorem finite_positive_denominator_fiber {Q : ℕ} (hQ : 0 < Q) (s : Finset ℤ)
    (P : ℤ → ℕ → Prop)
    (hp : ∀ h ∈ s, ∃ q : ℕ, 0 < q ∧ q ≤ Q ∧ P h q) :
    ∃ q : ℕ, 0 < q ∧ q ≤ Q ∧ ∃ t : Finset ℤ, t ⊆ s ∧
      (s.card : ℝ) / (Q : ℝ) ≤ (t.card : ℝ) ∧ ∀ h ∈ t, P h q := by
  classical
  let f (h : ℤ) : ℕ := if hh : h ∈ s then Classical.choose (hp h hh) else 1
  have hf (h : ℤ) (hh : h ∈ s) : 0 < f h ∧ f h ≤ Q ∧ P h (f h) := by
    simpa only [f, dif_pos hh] using Classical.choose_spec (hp h hh)
  have hm : ∀ h ∈ s, f h ∈ Finset.Icc 1 Q := by
    intro h hh
    exact Finset.mem_Icc.mpr ⟨(hf h hh).1, (hf h hh).2.1⟩
  have hT : (Finset.Icc 1 Q).Nonempty := ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hQ⟩⟩
  have hc : (Finset.Icc 1 Q).card = Q := by simp
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hb : (Finset.Icc 1 Q).card • ((s.card : ℝ) / (Q : ℝ)) ≤ (s.card : ℝ) := by
    rw [hc, nsmul_eq_mul, mul_div_cancel₀ _ hQR.ne']
  obtain ⟨q, hq, hj⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to hm hT hb
  have hq' := Finset.mem_Icc.mp hq
  refine ⟨q, hq'.1, hq'.2, s.filter (fun h => f h = q), Finset.filter_subset _ _, hj, ?_⟩
  intro h hh
  obtain ⟨hs, he⟩ := Finset.mem_filter.mp hh
  simpa only [he] using (hf h hs).2.2

end GMZP0
