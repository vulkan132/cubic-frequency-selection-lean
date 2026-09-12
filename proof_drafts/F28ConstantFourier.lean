import GMZP0.FourierTranslation
import GMZP0.CyclicInput
import GMZP0.LinearWeyl
import GMZP0.AffineFreezing

/-! The exact degree-zero Fourier passage to the original finite response.
The horizontal estimates are explicit unproved core premises, not external axioms. -/
noncomputable section
open scoped BigOperators
namespace GMZP0

/-- Every cyclic character has the required circle frequency, for all natural powers at once. -/
theorem cyclic_character_frequency {q : ℕ} [NeZero q] (ψ : AddChar (ZMod q) ℂ) :
    ∃ ξ : Frequency, ∀ n : ℕ, ψ (n : ZMod q) = circleCharacter (n • ξ) := by
  let z : Circle := ⟨ψ 1, by simp [Submonoid.unitSphere]⟩
  obtain ⟨ξ, hξ⟩ := (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).surjective z
  have he : circleCharacter ξ = ψ 1 := by
    simpa only [AddCircle.homeomorphCircle_apply, circleCharacter, z] using
      congrArg (fun w : Circle => (w : ℂ)) hξ
  refine ⟨ξ, fun n => ?_⟩
  rw [circleCharacter_nsmul, he]
  simpa only [nsmul_eq_mul, mul_one] using ψ.map_nsmul_eq_pow n (1 : ZMod q)

def horizontalCubicResponse (N : ℕ) (φ : Fin N → Frequency) (ξ : Frequency)
    (u : Fin (2 * N) → ℂ) (x : Fin N) : ℂ :=
  (∑ r : Fin N, u (horizontalEndpointIndex x r) *
    circleCharacter (label r ^ 3 • φ x + label r ^ 2 • ξ)) / (N : ℂ)

def cyclicConstantResponse (N q : ℕ) (φ : Fin N → Frequency)
    (F : Fin (2 * N) → ZMod q → ℂ) (x : Fin N) (Y : ZMod q) : ℂ :=
  (∑ r : Fin N, F (horizontalEndpointIndex x r)
    (Y + ((label r ^ 2 : ℕ) : ZMod q)) * cubicPhase (φ x) r) / (N : ℂ)

theorem cyclicConstantResponse_as_translation {N q : ℕ} (φ : Fin N → Frequency)
    (m : Fin N → ℂ) (F : Fin (2 * N) → ZMod q → ℂ) (x : Fin N) (Y : ZMod q) :
    verticalTranslationSum (fun x r => m x * cubicPhase (φ x) r / (N : ℂ))
      horizontalEndpointIndex (fun r => ((label r ^ 2 : ℕ) : ZMod q)) F x Y =
      m x * cyclicConstantResponse N q φ F x Y := by
  simp only [verticalTranslationSum, cyclicConstantResponse, div_eq_mul_inv,
    Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r _
  ring

/-- The quadratic Fourier phase is retained along with the cubic observation. -/
theorem horizontalCubicResponse_as_fiber {N q : ℕ} (φ : Fin N → Frequency)
    (m : Fin N → ℂ) (ψ : AddChar (ZMod q) ℂ) (ξ : Frequency)
    (hξ : ∀ n : ℕ, ψ (n : ZMod q) = circleCharacter (n • ξ))
    (u : Fin (2 * N) → ℂ) (x : Fin N) :
    verticalFourierFiber (fun x r => m x * cubicPhase (φ x) r / (N : ℂ))
      horizontalEndpointIndex (fun r => ((label r ^ 2 : ℕ) : ZMod q)) ψ u x =
      m x * horizontalCubicResponse N φ ξ u x := by
  simp only [verticalFourierFiber, horizontalCubicResponse, hξ,
    cubicPhase, circleCharacter, AddCircle.toCircle_add, Circle.coe_mul,
    div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r _
  ring

/-- The full cyclic estimate follows from every horizontal Fourier parameter, uniformly. -/
theorem cyclicConstantResponse_energy {N q : ℕ} [NeZero q]
    (φ : Fin N → Frequency) (m : Fin N → ℂ) (B : ℝ)
    (hbound : ∀ (ξ : Frequency) (u : Fin (2 * N) → ℂ),
      (∑ x, ‖m x * horizontalCubicResponse N φ ξ u x‖ ^ 2) ≤ B * ∑ t, ‖u t‖ ^ 2)
    (F : Fin (2 * N) → ZMod q → ℂ) :
    (∑ x, ∑ Y, ‖m x * cyclicConstantResponse N q φ F x Y‖ ^ 2) ≤
      B * ∑ t, ∑ Y, ‖F t Y‖ ^ 2 := by
  have hf (ψ : AddChar (ZMod q) ℂ) (u : Fin (2 * N) → ℂ) :
      (∑ x, ‖verticalFourierFiber (fun x r => m x * cubicPhase (φ x) r / (N : ℂ))
        horizontalEndpointIndex (fun r => ((label r ^ 2 : ℕ) : ZMod q)) ψ u x‖ ^ 2) ≤
        B * ∑ t, ‖u t‖ ^ 2 := by
    obtain ⟨ξ, hξ⟩ := cyclic_character_frequency ψ
    simpa only [horizontalCubicResponse_as_fiber φ m ψ ξ hξ] using hbound ξ u
  simpa only [cyclicConstantResponse_as_translation] using
    verticalTranslationSum_energy (fun x r => m x * cubicPhase (φ x) r / (N : ℂ))
      horizontalEndpointIndex (fun r => ((label r ^ 2 : ℕ) : ZMod q)) B hf F

/-- The complete original response is exactly the cyclic response on the zero extension. -/
theorem cyclicConstantResponse_original {N q : ℕ} (hq : 2 * N ^ 2 ≤ q)
    (φ : Fin N → Frequency) (g : InputBox N → ℂ) (z : Base N) :
    cyclicConstantResponse N q φ (cyclicInput N q g) z.1 (finiteCyclicIndex (N ^ 2) q z.2) =
      finiteResponse N (fun z : Base N => φ z.1) g z := by
  simp only [cyclicConstantResponse, finiteResponse, cyclicInput_endpoint hq]

/-- Restriction follows the full cyclic bound; only horizontal masks were Fourier-diagonalized. -/
theorem original_constant_energy_of_horizontal {N q : ℕ} [NeZero q] (hq : 2 * N ^ 2 ≤ q)
    (φ : Fin N → Frequency) (m : Fin N → ℂ) (B : ℝ)
    (hbound : ∀ (ξ : Frequency) (u : Fin (2 * N) → ℂ),
      (∑ x, ‖m x * horizontalCubicResponse N φ ξ u x‖ ^ 2) ≤ B * ∑ t, ‖u t‖ ^ 2)
    (g : InputBox N → ℂ) :
    (∑ z : Base N, ‖m z.1 * finiteResponse N (fun z : Base N => φ z.1) g z‖ ^ 2) ≤
      B * ∑ t, ‖g t‖ ^ 2 := by
  have hout : N ^ 2 ≤ q := by omega
  calc
    _ = ∑ x, ∑ y : Fin (N ^ 2), ‖m x * cyclicConstantResponse N q φ
        (cyclicInput N q g) x (finiteCyclicIndex (N ^ 2) q y)‖ ^ 2 := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      rw [cyclicConstantResponse_original hq φ g (x, y)]
    _ ≤ ∑ x, ∑ Y : ZMod q, ‖m x * cyclicConstantResponse N q φ (cyclicInput N q g) x Y‖ ^ 2 :=
      Finset.sum_le_sum (fun x _ => finiteCyclicIndex_energy_le hout
        (fun Y => m x * cyclicConstantResponse N q φ (cyclicInput N q g) x Y))
    _ ≤ B * ∑ t, ∑ Y, ‖cyclicInput N q g t Y‖ ^ 2 :=
      cyclicConstantResponse_energy φ m B hbound (cyclicInput N q g)
    _ = _ := by rw [cyclicInput_energy hq]

def horizontalMinorMask {N : ℕ} (Q : ℕ) (φ : Fin N → Frequency) (x : Fin N) : ℂ := by
  classical
  exact if MajorArc Q N (φ x) then 0 else 1

/-- A uniform-in-xi horizontal minor estimate suffices for the exact original finite estimate. -/
theorem finiteMinorEstimate_of_horizontal {N : ℕ} (Q : ℕ) (s : ℝ) (φ : Fin N → Frequency)
    (hbound : ∀ (ξ : Frequency) (u : Fin (2 * N) → ℂ),
      (∑ x, ‖horizontalMinorMask Q φ x * horizontalCubicResponse N φ ξ u x‖ ^ 2) ≤
        s ^ 2 * ∑ t, ‖u t‖ ^ 2) :
    FiniteMinorEstimate Q N s (fun z : Base N => φ z.1) := by
  classical
  intro g
  have h := original_constant_energy_of_horizontal (q := 2 * N ^ 2 + 1) (by omega)
    φ (horizontalMinorMask Q φ) (s ^ 2) hbound g
  have he (z : Base N) :
      ‖horizontalMinorMask Q φ z.1 * finiteResponse N (fun z : Base N => φ z.1) g z‖ ^ 2 =
        if MajorArc Q N (φ z.1) then 0 else
          ‖finiteResponse N (fun z : Base N => φ z.1) g z‖ ^ 2 := by
    unfold horizontalMinorMask
    split_ifs <;> simp
  simpa only [he] using h

/-- Remaining horizontal core target. No estimate is asserted by this definition. -/
def UniformHorizontalConstantFreezing : Prop :=
  ∀ s : ℝ, 0 < s → s ≤ 1 → ∃ Q N₀ : ℕ, 0 < Q ∧ 0 < N₀ ∧
    ∀ N : ℕ, N₀ ≤ N → ∀ (φ : Fin N → Frequency) (ξ : Frequency) (u : Fin (2 * N) → ℂ),
      (∑ x, ‖horizontalMinorMask Q φ x * horizontalCubicResponse N φ ξ u x‖ ^ 2) ≤
        s ^ 2 * ∑ t, ‖u t‖ ^ 2

/-- Quantifier-preserving reduction: no new cutoff or scale depends on Fourier or original data. -/
theorem uniform_constant_freezing_of_horizontal
    (h : UniformHorizontalConstantFreezing) : UniformConstantFreezing := by
  intro s hs hs1
  obtain ⟨Q, N₀, hQ, hN₀, hbound⟩ := h s hs hs1
  exact ⟨Q, N₀, hQ, hN₀, fun N hN φ => finiteMinorEstimate_of_horizontal Q s φ (hbound N hN φ)⟩

end GMZP0
