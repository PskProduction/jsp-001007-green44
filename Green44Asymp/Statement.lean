/-
Copyright (c) 2026. Formalization of Price's counterexample to Green Problem 44 /
JSP-001007 (half-residue sieve bound with 1000 primes < N^(9/10)).
-/

/-
Lean formalization author: @PskProduction (Nikita)
Mathematics: Liam Price and GPT-5.4 Pro (JSP-001007 / Green 44)
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Interval.Finset.Nat

namespace Green44Asymp

/--
The universal claim formalized in `formal-conjectures` Green 44 (fixed `Fin 1000`):
for every `N`, every strictly monotone tuple of 1000 primes with
`(p 999)^10 < N^9`, and every forbidden half of residue classes, the sifted set
in `[1,N]` has size at most `N/10`.

Price's Theorem 1 shows this fails for every sufficiently large `N`.
-/
def UniversalBound : Prop :=
  ∀ (N : ℕ) (p : Fin 1000 → ℕ) (A : (i : Fin 1000) → Finset (ZMod (p i))),
    let remaining := (Finset.Icc 1 N).filter (fun x => ∀ i, (x : ZMod (p i)) ∉ A i)
    (∀ i, (p i).Prime) →
    StrictMono p →
    (p 999) ^ 10 < N ^ 9 →
    (∀ i, (A i).card = (p i) / 2) →
    10 * remaining.card ≤ N

/-- Price, Theorem 1 (Green 44 form): for all large `N` there is a counterexample. -/
def PriceTheorem1 : Prop :=
  ∃ N0 : ℕ, ∀ N ≥ N0,
    ∃ (p : Fin 1000 → ℕ) (R : (i : Fin 1000) → Finset (ZMod (p i))),
      (∀ i, (p i).Prime) ∧
      StrictMono p ∧
      (p 999) ^ 10 < N ^ 9 ∧
      (∀ i, (R i).card = (p i) / 2) ∧
      let S := (Finset.Icc 1 N).filter (fun n => ∀ i, (n : ZMod (p i)) ∉ R i)
      N < 10 * S.card

theorem price_implies_not_universal (h : PriceTheorem1) : ¬ UniversalBound := by
  obtain ⟨N0, hN0⟩ := h
  intro hu
  -- take any N ≥ max N0 2 large enough that counterexamples exist
  let N := max N0 2
  obtain ⟨p, R, hp, hm, hb, hc, hS⟩ := hN0 N (le_max_left _ _)
  have := hu N p R hp hm hb hc
  exact (Nat.not_le_of_gt hS) this

end Green44Asymp
