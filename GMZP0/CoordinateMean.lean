import GMZP0.CubeLagRemoval

/-! Finite coordinate resampling and the probability bound for at most one successful value. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

def swapSampleCoordinate {I A : Type*} [DecidableEq I] (i : I) :
    ((I → A) × A) ≃ ((I → A) × A) where
  toFun z := (Function.update z.1 i z.2, z.1 i)
  invFun z := (Function.update z.1 i z.2, z.1 i)
  left_inv z := by
    rcases z with ⟨v, a⟩
    apply Prod.ext
    · funext j
      by_cases hj : j = i
      · subst j; simp
      · simp [Function.update_of_ne hj]
    · simp
  right_inv z := by
    rcases z with ⟨v, a⟩
    apply Prod.ext
    · funext j
      by_cases hj : j = i
      · subst j; simp
      · simp [Function.update_of_ne hj]
    · simp

theorem realUniformMean_resample {I A : Type*} [Fintype I] [DecidableEq I]
    [Fintype A] [Nonempty A] (i : I) (F : (I → A) → ℝ) :
    realUniformMean (fun v : I → A => realUniformMean (fun a : A => F (Function.update v i a))) =
      realUniformMean F := by
  have he := realUniformMean_equiv (swapSampleCoordinate (A := A) i)
    (fun z : (I → A) × A => F z.1)
  change realUniformMean (fun z : (I → A) × A => F (Function.update z.1 i z.2)) =
    realUniformMean (fun z : (I → A) × A => F z.1) at he
  rw [realUniformMean_prod (fun (v : I → A) (a : A) => F (Function.update v i a)),
    realUniformMean_prod (fun (v : I → A) (_ : A) => F v)] at he
  simpa only [realUniformMean_const] using he

theorem uniform_event_le_one_over_card {A : Type*} [Fintype A]
    (P : A → Prop) [DecidablePred P]
    (hunique : ∀ a b, P a → P b → a = b) :
    realUniformMean (fun a => if P a then 1 else 0) ≤ 1 / (Fintype.card A : ℝ) := by
  classical
  have hc : (Finset.univ.filter P).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    exact hunique a b (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
  unfold realUniformMean
  have he : (∑ a : A, if P a then (1 : ℝ) else 0) = ((Finset.univ.filter P).card : ℝ) := by simp
  rw [he]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast hc

theorem uniform_event_le_of_update_unique {I A : Type*} [Fintype I] [DecidableEq I]
    [Fintype A] [Nonempty A] (i : I) (P : (I → A) → Prop) [DecidablePred P]
    (hunique : ∀ v a b, P (Function.update v i a) → P (Function.update v i b) → a = b) :
    realUniformMean (fun v => if P v then 1 else 0) ≤ 1 / (Fintype.card A : ℝ) := by
  rw [← realUniformMean_resample i (fun v => if P v then 1 else 0)]
  apply (realUniformMean_mono _ (fun _ : I → A => 1 / (Fintype.card A : ℝ)) ?_).trans_eq
    (realUniformMean_const _)
  intro v
  exact uniform_event_le_one_over_card (fun a => P (Function.update v i a)) (hunique v)

end GMZP0
