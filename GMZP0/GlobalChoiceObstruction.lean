import GMZP0.GlobalFiniteChoice

/-! Separate witnesses for every event need not be compatible with one global choice. -/

noncomputable section
namespace GMZP0

theorem separate_witnesses_not_one_global_witness :
    (∀ i : Bool, ∃ c : Bool, i = c) ∧
      (¬ ∃ c : Bool, ∀ i : Bool, i = c) ∧
      (∀ c : Bool, realUniformMean (fun i : Bool => if i = c then 1 else 0) = 1 / 2) := by
  refine ⟨fun i => ⟨i, rfl⟩, ?_, ?_⟩
  · rintro ⟨c, hc⟩
    have he := (hc false).trans (hc true).symm
    cases he
  · intro c
    rw [uniform_singleton_probability]
    simp

end GMZP0
