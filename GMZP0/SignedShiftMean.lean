import GMZP0.CubeLagRemoval

/-! The full nonzero signed label set is exactly two copies of the original positive labels. -/

noncomputable section
namespace GMZP0

def signedHorizontalLabel (N : ℕ) (z : Bool × Fin N) : horizontalShiftLabels N :=
  ⟨if z.1 then -(label z.2 : ℤ) else (label z.2 : ℤ), by
    have hz := integer_label_bounds z.2
    simp only [horizontalShiftLabels, Finset.mem_erase, Finset.mem_Icc]
    split_ifs <;> omega⟩

theorem signedHorizontalLabel_injective (N : ℕ) : Function.Injective (signedHorizontalLabel N) := by
  intro z w he
  rcases z with ⟨b, r⟩
  rcases w with ⟨c, s⟩
  have hv := congrArg Subtype.val he
  cases b <;> cases c <;> simp_all [signedHorizontalLabel, Fin.ext_iff, label] <;> omega

theorem signedHorizontalLabel_surjective (N : ℕ) : Function.Surjective (signedHorizontalLabel N) := by
  intro h
  have hh := h.property
  simp only [horizontalShiftLabels, Finset.mem_erase, Finset.mem_Icc] at hh
  by_cases hp : 0 < h.val
  · let r : Fin N := ⟨(h.val - 1).toNat, by omega⟩
    refine ⟨(false, r), ?_⟩
    apply Subtype.ext
    simp only [signedHorizontalLabel, Bool.false_eq_true, ↓reduceIte, label, r, Nat.cast_add, Nat.cast_one]
    omega
  · let r : Fin N := ⟨(-h.val - 1).toNat, by omega⟩
    refine ⟨(true, r), ?_⟩
    apply Subtype.ext
    simp only [signedHorizontalLabel, ↓reduceIte, label, r, Nat.cast_add, Nat.cast_one]
    omega

def signedHorizontalEquiv (N : ℕ) : (Bool × Fin N) ≃ horizontalShiftLabels N :=
  Equiv.ofBijective (signedHorizontalLabel N)
    ⟨signedHorizontalLabel_injective N, signedHorizontalLabel_surjective N⟩

theorem real_signed_mean_eq_positive (N : ℕ) (g : ℤ → ℝ) (heven : ∀ h, g (-h) = g h) :
    realUniformMean (fun h : horizontalShiftLabels N => g h.val) =
      realUniformMean (fun h : Fin N => g (label h)) := by
  have he := realUniformMean_equiv (signedHorizontalEquiv N)
    (fun h : horizontalShiftLabels N => g h.val)
  change realUniformMean (fun z : Bool × Fin N =>
    g (if z.1 then -(label z.2 : ℤ) else (label z.2 : ℤ))) =
      realUniformMean (fun h : horizontalShiftLabels N => g h.val) at he
  rw [realUniformMean_prod (fun (b : Bool) (r : Fin N) =>
    g (if b then -(label r : ℤ) else (label r : ℤ)))] at he
  have hb (b : Bool) (r : Fin N) :
      g (if b then -(label r : ℤ) else (label r : ℤ)) = g (label r) := by
    cases b <;> simp [heven]
  simp only [hb, realUniformMean_const] at he
  exact he.symm

end GMZP0
