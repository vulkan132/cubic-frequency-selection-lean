import GMZP0.Definitions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Estimates for the same original function, base point and complete label set. -/

noncomputable section
open scoped BigOperators
namespace GMZP0

/-- The quotient-based phase is exactly the manuscript's exp(2 pi i a r³). -/
theorem cubicPhase_coe_real {N : ℕ} (a : ℝ) (r : Fin N) :
    cubicPhase (a : Frequency) r =
      Complex.exp (((2 * Real.pi * a * (label r : ℝ) ^ 3 : ℝ) : ℂ) * Complex.I) := by
  rw [cubicPhase, ← AddCircle.coe_nsmul, AddCircle.toCircle_apply_mk, Circle.coe_exp]
  simp only [nsmul_eq_mul, div_one, Nat.cast_pow]
  congr 1
  push_cast
  ring

theorem cubicDistanceSq_nonneg (N : ℕ) (a b : Frequency) :
    0 ≤ cubicDistanceSq N a b := by
  exact div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Nat.cast_nonneg _)

theorem cubicDistance_nonneg (N : ℕ) (a b : Frequency) :
    0 ≤ cubicDistance N a b := Real.sqrt_nonneg _

theorem cubicDistance_sq (N : ℕ) (a b : Frequency) :
    cubicDistance N a b ^ 2 = cubicDistanceSq N a b :=
  Real.sq_sqrt (cubicDistanceSq_nonneg N a b)

/-- A complete average of a one-bounded original function is one-bounded. -/
theorem norm_response_le_one {N : ℕ} (hN : 0 < N) (f : ℤ × ℤ → ℂ)
    (hf : ∀ w, ‖f w‖ ≤ 1) (z : Base N) (a : Frequency) :
    ‖response N f z a‖ ≤ 1 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [response, norm_div, Complex.norm_natCast]
  apply (div_le_iff₀ hNr).2
  calc
    ‖∑ r : Fin N, f (endpoint z r) * cubicPhase a r‖ ≤
        ∑ r : Fin N, ‖f (endpoint z r) * cubicPhase a r‖ := norm_sum_le _ _
    _ ≤ ∑ _r : Fin N, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro r _
      simpa only [norm_mul, norm_cubicPhase, mul_one] using hf (endpoint z r)
    _ = 1 * (N : ℝ) := by simp

/-- Cauchy–Schwarz for a finite normalized first moment and second moment. -/
theorem mean_le_root_mean_square {N : ℕ} (hN : 0 < N) (v : Fin N → ℝ) :
    (∑ r, v r) / (N : ℝ) ≤ Real.sqrt ((∑ r, v r ^ 2) / (N : ℝ)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hcs : (∑ r, v r) ^ 2 ≤ (N : ℝ) * ∑ r, v r ^ 2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin N => (1 : ℝ)) v
  apply Real.le_sqrt_of_sq_le
  rw [div_pow]
  apply (div_le_iff₀ (sq_pos_of_pos hNr)).2
  calc
    (∑ r, v r) ^ 2 ≤ (N : ℝ) * ∑ r, v r ^ 2 := hcs
    _ = ((∑ r, v r ^ 2) / (N : ℝ)) * (N : ℝ) ^ 2 := by
      field_simp

/-- The full-label distance controls the two full responses of the SAME f. -/
theorem norm_response_sub_le {N : ℕ} (hN : 0 < N) (f : ℤ × ℤ → ℂ)
    (hf : ∀ w, ‖f w‖ ≤ 1) (z : Base N) (a b : Frequency) :
    ‖response N f z a - response N f z b‖ ≤ cubicDistance N a b := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have heq : response N f z a - response N f z b =
      (∑ r : Fin N, f (endpoint z r) * (cubicPhase a r - cubicPhase b r)) / (N : ℂ) := by
    simp only [response, mul_sub, Finset.sum_sub_distrib, sub_div]
  rw [heq, norm_div, Complex.norm_natCast]
  calc
    ‖∑ r : Fin N, f (endpoint z r) * (cubicPhase a r - cubicPhase b r)‖ / (N : ℝ) ≤
        (∑ r : Fin N, ‖cubicPhase a r - cubicPhase b r‖) / (N : ℝ) := by
      apply div_le_div_of_nonneg_right _ hNr.le
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro r _
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hf _)
    _ ≤ cubicDistance N a b := mean_le_root_mean_square hN _

/-- Original aligned response is transferred to a nearby frequency at the same point. -/
theorem aligned_response_transfer {N : ℕ} (hN : 0 < N) (f : ℤ × ℤ → ℂ)
    (hf : ∀ w, ‖f w‖ ≤ 1) (z : Base N) (a b : Frequency)
    (lam : ℂ) (hlam : ‖lam‖ = 1) (η ε : ℝ)
    (hresponse : η ≤ (lam * response N f z a).re)
    (hclose : cubicDistance N a b ≤ ε) :
    η - ε ≤ (lam * response N f z b).re := by
  have hnorm : ‖lam * (response N f z a - response N f z b)‖ ≤ ε := by
    rw [norm_mul, hlam, one_mul]
    exact (norm_response_sub_le hN f hf z a b).trans hclose
  have hre := Complex.re_le_norm (lam * (response N f z a - response N f z b))
  rw [mul_sub, Complex.sub_re] at hre
  rw [mul_sub] at hnorm
  linarith

theorem norm_response_transfer {N : ℕ} (hN : 0 < N) (f : ℤ × ℤ → ℂ)
    (hf : ∀ w, ‖f w‖ ≤ 1) (z : Base N) (a b : Frequency)
    (lam : ℂ) (hlam : ‖lam‖ = 1) (η ε : ℝ)
    (hresponse : η ≤ (lam * response N f z a).re)
    (hclose : cubicDistance N a b ≤ ε) :
    η - ε ≤ ‖response N f z b‖ := by
  have hre := (aligned_response_transfer hN f hf z a b lam hlam η ε hresponse hclose).trans
    (Complex.re_le_norm (lam * response N f z b))
  simpa only [norm_mul, hlam, one_mul] using hre

end GMZP0
