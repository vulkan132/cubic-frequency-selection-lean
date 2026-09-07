import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators

/-! The original parabola response and the full-label capture targets. -/

noncomputable section
open scoped BigOperators

namespace GMZP0

abbrev Frequency := AddCircle (1 : ℝ)
abbrev Base (N : ℕ) := Fin N × Fin (N ^ 2)

/-- Finite indexing of exactly [N] × [N²], with integer coordinates starting at one. -/
def basePoint {N : ℕ} (z : Base N) : ℤ × ℤ :=
  ((z.1.val : ℤ) + 1, (z.2.val : ℤ) + 1)

/-- Label r ranges through 1,...,N, without any discarded labels. -/
def label {N : ℕ} (r : Fin N) : ℕ := r.val + 1

def endpoint {N : ℕ} (z : Base N) (r : Fin N) : ℤ × ℤ :=
  ((basePoint z).1 + (label r : ℤ), (basePoint z).2 + (label r : ℤ) ^ 2)

/-- e(a r³) on the actual quotient R/Z; no real representative is selected. -/
def cubicPhase {N : ℕ} (a : Frequency) (r : Fin N) : ℂ :=
  ((label r ^ 3 • a).toCircle : ℂ)

/-- The original complete response of f at the original base point z. -/
def response (N : ℕ) (f : ℤ × ℤ → ℂ) (z : Base N) (a : Frequency) : ℂ :=
  (∑ r : Fin N, f (endpoint z r) * cubicPhase a r) / (N : ℂ)

/-- Square of the full-label cubic chord distance. -/
def cubicDistanceSq (N : ℕ) (a b : Frequency) : ℝ :=
  (∑ r : Fin N, ‖cubicPhase a r - cubicPhase b r‖ ^ 2) / (N : ℝ)

def cubicDistance (N : ℕ) (a b : Frequency) : ℝ :=
  Real.sqrt (cubicDistanceSq N a b)

def meanResponse (N : ℕ) (f : ℤ × ℤ → ℂ) (θ : Base N → Frequency) : ℝ :=
  (∑ z : Base N, ‖response N f z (θ z)‖) / (N : ℝ) ^ 3

/-- Main target, stated but not asserted or postulated as a theorem. -/
def P0 : Prop :=
  ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
    ∃ c : ℝ, 0 < c ∧
      ∀ N : ℕ, 1 ≤ N → ∀ (f : ℤ × ℤ → ℂ) (θ : Base N → Frequency),
        (∀ w, ‖f w‖ ≤ 1) → δ ≤ meanResponse N f θ →
        ∃ β : Frequency, c ≤ meanResponse N f (fun _ => β)

/-- The original response, alignment and weight hypotheses in the weighted theorem. -/
def Admissible (N : ℕ) (κ η : ℝ) (f : ℤ × ℤ → ℂ)
    (θ : Base N → Frequency) (lam : Base N → ℂ) (μ : Base N → ℝ) : Prop :=
  (∀ w, ‖f w‖ ≤ 1) ∧
  (∀ z, ‖lam z‖ = 1) ∧
  (∀ z, 0 ≤ μ z ∧ μ z ≤ (N : ℝ)⁻¹ ^ 3) ∧
  κ ≤ ∑ z, μ z ∧
  ∀ z, μ z ≠ 0 → η ≤ (lam z * response N f z (θ z)).re

/-- Strong universal-list version: the finite list precedes all original data. -/
def WeightedCapture : Prop :=
  ∀ κ η ε : ℝ, 0 < κ → κ ≤ 1 → 0 < η → η ≤ 1 → 0 < ε → ε ≤ η / 2 →
    ∃ c : ℝ, 0 < c ∧ ∃ L N₀ : ℕ, 1 ≤ L ∧ 1 ≤ N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∃ β : Fin L → Frequency,
        ∀ (f : ℤ × ℤ → ℂ) (θ : Base N → Frequency)
          (lam : Base N → ℂ) (μ : Base N → ℝ),
          Admissible N κ η f θ lam μ →
          ∃ A : Finset (Base N), ∃ j : Base N → Fin L,
            (∀ z ∈ A, μ z ≠ 0) ∧ c ≤ ∑ z ∈ A, μ z ∧
            ∀ z ∈ A, cubicDistance N (θ z) (β (j z)) ≤ ε

@[simp] theorem norm_cubicPhase {N : ℕ} (a : Frequency) (r : Fin N) :
    ‖cubicPhase a r‖ = 1 := by
  exact Circle.norm_coe _

@[simp] theorem card_base (N : ℕ) : Fintype.card (Base N) = N ^ 3 := by
  simp only [Base, Fintype.card_prod, Fintype.card_fin]
  simp [pow_succ, Nat.mul_comm]

end GMZP0
