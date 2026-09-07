import GMZP0.FiniteUnionMean
import Mathlib.Logic.Equiv.Set

/-! A global finite assignment restricts uniformly to any family of distinct actual points. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

def assignmentSplitEquiv {S V A : Type*} (e : V ↪ S) :
    (S → A) ≃ (V → A) × ({s : S // s ∉ Set.range e} → A) := by
  classical
  exact {
    toFun := fun f => (fun v => f (e v), fun s => f s.val)
    invFun := fun z s => if hs : s ∈ Set.range e
      then z.1 ((Equiv.ofInjective e e.injective).symm ⟨s, hs⟩) else z.2 ⟨s, hs⟩
    left_inv := by
      intro f
      funext s
      dsimp only
      split_ifs with hs
      · exact congrArg f (Equiv.apply_ofInjective_symm (f := e) e.injective ⟨s, hs⟩)
      · rfl
    right_inv := by
      intro z
      apply Prod.ext
      · funext v
        simp only [dif_pos (show e v ∈ Set.range e from ⟨v, rfl⟩), Equiv.ofInjective_symm_apply]
      · funext s
        simp only [dif_neg s.property] }

theorem realUniformMean_restrict {S V A : Type*} [Fintype S] [Fintype V]
    [DecidableEq S] [DecidableEq V] [Fintype A] [Nonempty A] (e : V ↪ S) (F : (V → A) → ℝ) :
    realUniformMean (fun f : S → A => F (fun v => f (e v))) = realUniformMean F := by
  classical
  let C := {s : S // s ∉ Set.range e}
  let split := assignmentSplitEquiv (A := A) e
  have hx (z : (V → A) × (C → A)) : (fun v => split.symm z (e v)) = z.1 :=
    congrArg Prod.fst (split.apply_symm_apply z)
  have he := realUniformMean_equiv split.symm (fun f : S → A => F (fun v => f (e v)))
  simp only [hx] at he
  rw [realUniformMean_prod (fun (v : V → A) (_ : C → A) => F v)] at he
  simpa only [realUniformMean_const] using he.symm

theorem uniform_singleton_probability {A : Type*} [Fintype A] [DecidableEq A] (a : A) :
    realUniformMean (fun b => if b = a then 1 else 0) = 1 / (Fintype.card A : ℝ) := by
  classical
  simp [realUniformMean]

theorem uniform_restricted_assignment_probability {S V A : Type*} [Fintype S] [Fintype V]
    [DecidableEq S] [DecidableEq V] [Fintype A] [DecidableEq A] [Nonempty A] (e : V ↪ S) (a : V → A) :
    realUniformMean (fun f : S → A => if (fun v => f (e v)) = a then 1 else 0) =
      1 / (Fintype.card A : ℝ) ^ Fintype.card V := by
  classical
  rw [realUniformMean_restrict e (fun g => if g = a then 1 else 0), uniform_singleton_probability]
  simp only [Fintype.card_fun, Nat.cast_pow]

theorem uniform_restricted_event_lower {S V A : Type*} [Fintype S] [Fintype V]
    [DecidableEq S] [DecidableEq V] [Fintype A] [Nonempty A] (e : V ↪ S) (P : (V → A) → Prop) [DecidablePred P]
    (a : V → A) (ha : P a) :
    1 / (Fintype.card A : ℝ) ^ Fintype.card V ≤
      realUniformMean (fun f : S → A => if P (fun v => f (e v)) then 1 else 0) := by
  classical
  rw [← uniform_restricted_assignment_probability e a]
  apply realUniformMean_mono
  intro f
  by_cases hf : (fun v => f (e v)) = a
  · simp only [hf, ha, ite_true, le_refl]
  · rw [if_neg hf]
    split_ifs <;> norm_num

theorem realUniformMean_comm {I J : Type*} [Fintype I] [Fintype J] (F : I → J → ℝ) :
    realUniformMean (fun i => realUniformMean (F i)) =
      realUniformMean (fun j => realUniformMean (fun i => F i j)) := by
  simp only [realUniformMean, div_eq_mul_inv, ← Finset.sum_mul]
  rw [Finset.sum_comm]
  ring

end GMZP0
