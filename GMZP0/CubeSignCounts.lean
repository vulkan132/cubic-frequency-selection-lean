import GMZP0.CubeConjugation

/-! Exact positive/negative sign counts and bounded integer cube sums. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

theorem cubeSign_one_or_neg_one (d : ℕ) : ∀ ω : Fin d → Bool,
    cubeSign d ω = 1 ∨ cubeSign d ω = -1 := by
  induction d with
  | zero => intro ω; exact Or.inl rfl
  | succ d ih =>
    intro ω
    have hi := ih (Fin.tail ω)
    unfold cubeSign
    split_ifs <;> rcases hi with hi | hi <;> simp [hi]

theorem cubeSign_abs (d : ℕ) (ω : Fin d → Bool) : |cubeSign d ω| = 1 := by
  rcases cubeSign_one_or_neg_one d ω with h | h <;> simp [h]

def positiveCubeVertices : Finset (Fin 4 → Bool) := Finset.univ.filter (fun ω => cubeSign 4 ω = 1)
def negativeCubeVertices : Finset (Fin 4 → Bool) := Finset.univ.filter (fun ω => cubeSign 4 ω = -1)

theorem card_positiveCubeVertices : positiveCubeVertices.card = 8 := by decide
theorem card_negativeCubeVertices : negativeCubeVertices.card = 8 := by decide

theorem bounded_integer_cube_sum (M : ℤ) (n : (Fin 4 → Bool) → ℤ)
    (hn : ∀ ω, 0 ≤ n ω ∧ n ω ≤ M) :
    |∑ ω, cubeSign 4 ω * n ω| ≤ 8 * M := by
  have hup (ω : Fin 4 → Bool) : cubeSign 4 ω * n ω ≤ if cubeSign 4 ω = 1 then M else 0 := by
    rcases cubeSign_one_or_neg_one 4 ω with h | h <;> simp [h] <;> linarith [(hn ω).1, (hn ω).2]
  have hlo (ω : Fin 4 → Bool) : -(cubeSign 4 ω * n ω) ≤ if cubeSign 4 ω = -1 then M else 0 := by
    rcases cubeSign_one_or_neg_one 4 ω with h | h <;> simp [h] <;> linarith [(hn ω).1, (hn ω).2]
  have hs₁ : (∑ ω : Fin 4 → Bool, if cubeSign 4 ω = 1 then M else 0) = 8 * M := by
    rw [← Finset.sum_filter]
    change (∑ _ ∈ positiveCubeVertices, M) = 8 * M
    simp only [Finset.sum_const, card_positiveCubeVertices, nsmul_eq_mul, Nat.cast_ofNat]
  have hs₂ : (∑ ω : Fin 4 → Bool, if cubeSign 4 ω = -1 then M else 0) = 8 * M := by
    rw [← Finset.sum_filter]
    change (∑ _ ∈ negativeCubeVertices, M) = 8 * M
    simp only [Finset.sum_const, card_negativeCubeVertices, nsmul_eq_mul, Nat.cast_ofNat]
  have h₁ := Finset.sum_le_sum (fun ω (_ : ω ∈ (Finset.univ : Finset (Fin 4 → Bool))) => hup ω)
  have h₂ := Finset.sum_le_sum (fun ω (_ : ω ∈ (Finset.univ : Finset (Fin 4 → Bool))) => hlo ω)
  rw [hs₁] at h₁
  rw [hs₂, Finset.sum_neg_distrib] at h₂
  exact abs_le.mpr ⟨by linarith, h₁⟩

end GMZP0
