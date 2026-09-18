/-
Lower bound on primes in (x, 2x], following Price:
`π(2x) - π(x) ≥ x / (2 log x)` for all sufficiently large `x`.
Derived from `pi_alt` in PrimeNumberTheoremAnd (sorry-free path).
-/

/-
Lean formalization author: @PskProduction (Nikita)
Mathematics: Liam Price and GPT-5.4 Pro (JSP-001007 / Green 44)
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Tactic
import PrimeNumberTheoremAnd.Consequences

open Filter Real Nat Asymptotics
open scoped Topology

namespace Green44Asymp

private lemma envelope_algebra {x L L2 : ℝ}
    (hx : 0 < x) (hL : 0 < L) (hL2 : 0 < L2)
    (hinv : (13 : ℝ) / 14 / L ≤ 1 / L2) :
    (7 / 8 : ℝ) * (2 * x) / L2 - (9 / 8) * x / L ≥ x / (2 * L) := by
  -- Reduce to: (7/4)/L2 - (9/8)/L ≥ 1/(2L)
  have hmul : (7 / 4 : ℝ) / L2 ≥ (7 / 4) * ((13 : ℝ) / 14 / L) := by
    have := mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 7 / 4)
    simpa [div_eq_mul_inv, mul_assoc] using this
  have hid : (7 / 4 : ℝ) * ((13 : ℝ) / 14 / L) - (9 / 8) / L = 1 / (2 * L) := by
    field_simp [hL.ne']
    ring
  have hcore : (7 / 4 : ℝ) / L2 - (9 / 8) / L ≥ 1 / (2 * L) := by linarith [hmul, hid]
  have := mul_le_mul_of_nonneg_left hcore hx.le
  -- Expand x * ((7/4)/L2 - (9/8)/L) and x*(1/(2L))
  have lhs :
      x * ((7 / 4 : ℝ) / L2 - (9 / 8) / L) = (7 / 8 : ℝ) * (2 * x) / L2 - (9 / 8) * x / L := by
    field_simp [hL.ne', hL2.ne']
    ring
  have rhs : x * (1 / (2 * L)) = x / (2 * L) := by ring
  linarith [this, lhs, rhs]

/--
Price's prime input: for all large real `x > 1`,
`π(⌊2x⌋) - π(⌊x⌋) ≥ x / (2 log x)`.
-/
theorem pi_two_minus_pi_ge :
    ∃ X : ℝ, 1 < X ∧ ∀ x ≥ X,
      ((primeCounting ⌊(2 : ℝ) * x⌋₊ : ℝ) - (primeCounting ⌊x⌋₊ : ℝ))
        ≥ x / (2 * Real.log x) := by
  obtain ⟨c, hc, hπ⟩ := pi_alt
  have hcε := (isLittleO_iff.mp hc) (by norm_num : (0 : ℝ) < 1 / 8)
  simp only [norm_eq_abs, eventually_atTop] at hcε
  obtain ⟨A, hA⟩ := hcε
  let X : ℝ := max A 16384
  refine ⟨X, lt_of_lt_of_le (by norm_num : (1 : ℝ) < 16384) (le_max_right _ _), ?_⟩
  intro x hx
  have hxA : A ≤ x := le_trans (le_max_left _ _) hx
  have hx16k : (16384 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have hx2 : (2 : ℝ) ≤ x := le_trans (by norm_num) hx16k
  have hx1 : (1 : ℝ) < x := lt_of_lt_of_le (by norm_num) hx2
  have Lpos : 0 < Real.log x := (log_pos_iff (by linarith)).2 hx1
  have L2pos : 0 < Real.log (2 * x) :=
    (log_pos_iff (by positivity)).2 (by nlinarith : (1 : ℝ) < 2 * x)
  have cx := abs_le.mp (hA x hxA)
  have c2x := abs_le.mp (hA (2 * x) (by nlinarith [hxA]))
  have pi2_ge : (primeCounting ⌊(2 : ℝ) * x⌋₊ : ℝ)
      ≥ (7 / 8 : ℝ) * (2 * x) / Real.log (2 * x) := by
    have hone : (7 : ℝ) / 8 ≤ 1 + c (2 * x) := by linarith [c2x.1]
    have hmul : (7 / 8 : ℝ) * (2 * x) ≤ (1 + c (2 * x)) * (2 * x) := by
      nlinarith [hone, show (0 : ℝ) ≤ 2 * x by positivity]
    simpa [hπ (2 * x)] using div_le_div_of_nonneg_right hmul L2pos.le
  have pix_le : (primeCounting ⌊x⌋₊ : ℝ) ≤ (9 / 8 : ℝ) * x / Real.log x := by
    have hone : 1 + c x ≤ (9 : ℝ) / 8 := by linarith [cx.2]
    have hmul : (1 + c x) * x ≤ (9 / 8 : ℝ) * x := by
      nlinarith [hone, show (0 : ℝ) ≤ x by linarith]
    simpa [hπ x] using div_le_div_of_nonneg_right hmul Lpos.le
  have h14 : (14 : ℝ) * Real.log 2 ≤ Real.log x := by
    have hpow : (2 : ℝ) ^ (14 : ℕ) ≤ x := by
      have : (2 : ℝ) ^ (14 : ℕ) = 16384 := by norm_num
      rw [this]; exact hx16k
    have hlog : Real.log ((2 : ℝ) ^ (14 : ℕ)) ≤ Real.log x :=
      (log_le_log_iff (by positivity) (by linarith)).2 hpow
    simpa [Real.log_pow] using hlog
  have log2x_eq : Real.log (2 * x) = Real.log 2 + Real.log x :=
    Real.log_mul (by norm_num) (by linarith)
  have inv_bound : (13 : ℝ) / 14 / Real.log x ≤ 1 / Real.log (2 * x) := by
    have : (13 : ℝ) / 14 * Real.log (2 * x) ≤ Real.log x := by
      rw [log2x_eq]; linarith [h14]
    rw [div_le_div_iff₀ Lpos L2pos]; linarith
  have env :=
    envelope_algebra (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hx2) Lpos L2pos inv_bound
  linarith [pi2_ge, pix_le, env]

theorem many_primes_in_doubling :
    ∃ N0 : ℕ, ∀ n ≥ N0,
      (n : ℝ) / (2 * Real.log (n : ℝ))
        ≤ (primeCounting (2 * n) : ℝ) - (primeCounting n : ℝ) := by
  obtain ⟨X, _, hX⟩ := pi_two_minus_pi_ge
  refine ⟨max ⌈X⌉₊ 2, ?_⟩
  intro n hn
  have hnX : X ≤ (n : ℝ) :=
    (Nat.le_ceil X).trans (Nat.cast_le.mpr (le_trans (le_max_left _ _) hn))
  have hx := hX (n : ℝ) hnX
  have h2 : ⌊(2 : ℝ) * n⌋₊ = 2 * n := by
    refine (Nat.floor_eq_iff (by positivity)).2 ⟨by push_cast; linarith, by push_cast; linarith⟩
  simpa [h2, Nat.floor_natCast] using hx

end Green44Asymp
