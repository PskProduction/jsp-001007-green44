/-
Price Lemma 2 scaffolding + combinatorial packing (part 1).
-/

/-
Lean formalization author: @PskProduction (Nikita)
Mathematics: Liam Price and GPT-5.4 Pro (JSP-001007 / Green 44)
-/

import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic
import Green44Asymp.PrimeGaps
import Green44Asymp.Statement

open Nat Real Finset
open scoped Nat.Prime

namespace Green44Asymp

def intervalPrimes (n : ℕ) : Finset ℕ :=
  primesLE (2 * n) \ primesBelow n

lemma mem_intervalPrimes {n p : ℕ} :
    p ∈ intervalPrimes n ↔ p.Prime ∧ n ≤ p ∧ p ≤ 2 * n := by
  constructor
  · intro hp
    obtain ⟨hLE, hnot⟩ := mem_sdiff.mp hp
    obtain ⟨hle, hP⟩ := mem_primesLE.mp hLE
    refine ⟨hP, ?_, hle⟩
    by_contra h
    exact hnot (mem_primesBelow.mpr ⟨Nat.lt_of_not_ge h, hP⟩)
  · intro ⟨hP, hlo, hhi⟩
    exact mem_sdiff.mpr ⟨mem_primesLE.mpr ⟨hhi, hP⟩,
      fun hB => (lt_of_mem_primesBelow hB).not_ge hlo⟩

lemma card_intervalPrimes (n : ℕ) :
    #(intervalPrimes n) = π (2 * n) - π' n := by
  classical
  unfold intervalPrimes
  have hsub : primesBelow n ⊆ primesLE (2 * n) := by
    intro p hp
    refine mem_primesLE.mpr ⟨?_, prime_of_mem_primesBelow hp⟩
    have := lt_of_mem_primesBelow hp
    omega
  rw [card_sdiff_of_subset hsub, primesLE_card_eq_primeCounting,
    primesBelow_card_eq_primeCounting']

lemma card_intervalPrimes_ge_pi_diff (n : ℕ) :
    π (2 * n) - π n ≤ #(intervalPrimes n) := by
  rw [card_intervalPrimes]
  have : π' n ≤ π n := by
    cases n with
    | zero => simp
    | succ k =>
      rw [← primeCounting_sub_one]
      exact monotone_primeCounting k.le_succ
  omega

noncomputable def doublingPrimes (n : ℕ) : List ℕ := (intervalPrimes n).sort

lemma doublingPrimes_length (n : ℕ) :
    (doublingPrimes n).length = #(intervalPrimes n) := by
  simp [doublingPrimes]

lemma doublingPrimes_strictMono (n : ℕ) :
    StrictMono fun i : Fin (doublingPrimes n).length => (doublingPrimes n).get i :=
  (sortedLT_sort (intervalPrimes n)).strictMono_get

lemma doublingPrimes_get_mem {n : ℕ} (i : Fin (doublingPrimes n).length) :
    (doublingPrimes n).get i ∈ intervalPrimes n := by
  have him : (doublingPrimes n).get i ∈ doublingPrimes n := List.get_mem _ _
  simp only [doublingPrimes] at him
  exact (mem_sort (r := (· ≤ ·))).1 him

lemma doublingPrimes_get_prime {n : ℕ} (i : Fin (doublingPrimes n).length) :
    ((doublingPrimes n).get i).Prime :=
  (mem_intervalPrimes.mp (doublingPrimes_get_mem i)).1

lemma doublingPrimes_get_lo {n : ℕ} (i : Fin (doublingPrimes n).length) :
    n ≤ (doublingPrimes n).get i :=
  (mem_intervalPrimes.mp (doublingPrimes_get_mem i)).2.1

lemma doublingPrimes_get_hi {n : ℕ} (i : Fin (doublingPrimes n).length) :
    (doublingPrimes n).get i ≤ 2 * n :=
  (mem_intervalPrimes.mp (doublingPrimes_get_mem i)).2.2

lemma doublingPrimes_mono (n : ℕ) :
    Monotone fun i : Fin (doublingPrimes n).length => (doublingPrimes n).get i :=
  (doublingPrimes_strictMono n).monotone

noncomputable def sp (n i : ℕ) : ℕ :=
  if h : i < (doublingPrimes n).length then (doublingPrimes n).get ⟨i, h⟩ else 0

lemma sp_eq_get {n i : ℕ} (hi : i < (doublingPrimes n).length) :
    sp n i = (doublingPrimes n).get ⟨i, hi⟩ := dif_pos hi

lemma sp_mono {n i j : ℕ} (hi : i < (doublingPrimes n).length)
    (hj : j < (doublingPrimes n).length) (hij : i ≤ j) :
    sp n i ≤ sp n j := by
  rw [sp_eq_get hi, sp_eq_get hj]
  exact doublingPrimes_mono n ((Fin.le_def).2 hij)

lemma sp_span_le_n (n : ℕ) (hm : 0 < (doublingPrimes n).length) :
    sp n ((doublingPrimes n).length - 1) - sp n 0 ≤ n := by
  have hlo : n ≤ sp n 0 := by
    rw [sp_eq_get hm]; exact doublingPrimes_get_lo _
  have hhi : sp n ((doublingPrimes n).length - 1) ≤ 2 * n := by
    rw [sp_eq_get (Nat.sub_lt hm Nat.zero_lt_one)]; exact doublingPrimes_get_hi _
  have hle : sp n 0 ≤ sp n ((doublingPrimes n).length - 1) :=
    sp_mono hm (Nat.sub_lt hm Nat.zero_lt_one) (Nat.zero_le _)
  omega

noncomputable def blockDiam (n b : ℕ) : ℕ :=
  sp n (1000 * b + 999) - sp n (1000 * b)

lemma sum_blockDiam_le_span (n q : ℕ)
    (hq : 1000 * q ≤ (doublingPrimes n).length) :
    ∑ b ∈ range q, blockDiam n b ≤ sp n (1000 * q - 1) - sp n 0 := by
  induction q with
  | zero => simp
  | succ q ih =>
    have hq' : 1000 * q ≤ (doublingPrimes n).length := by omega
    rw [Finset.sum_range_succ]
    have ih' := ih hq'
    have hstep :
        (sp n (1000 * q - 1) - sp n 0) + blockDiam n q ≤
          sp n (1000 * (q + 1) - 1) - sp n 0 := by
      simp only [blockDiam]
      have hidx : 1000 * (q + 1) - 1 = 1000 * q + 999 := by omega
      have a0 : sp n 0 ≤ sp n (1000 * q - 1) := by
        by_cases hq0 : q = 0
        · subst hq0; simp
        · exact sp_mono (by omega) (by omega) (by omega)
      have a1 : sp n (1000 * q - 1) ≤ sp n (1000 * q) := by
        by_cases hq0 : q = 0
        · subst hq0; simp
        · exact sp_mono (by omega) (by omega) (by omega)
      have a2 : sp n (1000 * q) ≤ sp n (1000 * q + 999) :=
        sp_mono (by omega) (by omega) (by omega)
      simp_rw [hidx]
      omega
    linarith

lemma exists_small_block (n q B : ℕ) (hq0 : 0 < q)
    (hq : 1000 * q ≤ (doublingPrimes n).length)
    (hspan : sp n (1000 * q - 1) - sp n 0 ≤ q * B) :
    ∃ b < q, blockDiam n b ≤ B := by
  classical
  have hne : (range q).Nonempty := by
    rw [nonempty_range_iff]
    exact Nat.pos_iff_ne_zero.mp hq0
  obtain ⟨b, hb, hbmin⟩ := exists_min_image (range q) (blockDiam n) hne
  refine ⟨b, mem_range.mp hb, ?_⟩
  have hsum := (sum_blockDiam_le_span n q hq).trans hspan
  have hmul : #(range q) • blockDiam n b ≤ ∑ i ∈ range q, blockDiam n i :=
    card_nsmul_le_sum (range q) (blockDiam n) (blockDiam n b) fun i hi => hbmin i hi
  have hmul' : q * blockDiam n b ≤ ∑ i ∈ range q, blockDiam n i := by
    simpa [card_range, nsmul_eq_mul] using hmul
  exact Nat.le_of_mul_le_mul_left (hmul'.trans hsum) hq0

lemma extract_block {n b B : ℕ}
    (hb : 1000 * b + 999 < (doublingPrimes n).length)
    (hd : blockDiam n b ≤ B) :
    ∃ p : Fin 1000 → ℕ,
      (∀ i, (p i).Prime) ∧ StrictMono p ∧
      (∀ i, n ≤ p i ∧ p i ≤ 2 * n) ∧
      p (999 : Fin 1000) - p 0 ≤ B := by
  have hidx (i : Fin 1000) : 1000 * b + i.val < (doublingPrimes n).length := by omega
  let p : Fin 1000 → ℕ := fun i => sp n (1000 * b + i.val)
  have hp_eq (i : Fin 1000) :
      p i = (doublingPrimes n).get ⟨1000 * b + i.val, hidx i⟩ := by
    simp [p, sp_eq_get (hidx i)]
  refine ⟨p, fun i => ?_, ?_, fun i => ?_, ?_⟩
  · rw [hp_eq]; exact doublingPrimes_get_prime _
  · intro i j hij
    rw [hp_eq i, hp_eq j]
    refine (doublingPrimes_strictMono n) ?_
    simp only [Fin.lt_def]
    have : (i.val : ℕ) < j.val := by exact_mod_cast hij
    omega
  · rw [hp_eq]
    exact ⟨doublingPrimes_get_lo _, doublingPrimes_get_hi _⟩
  · simpa [p, blockDiam] using hd

lemma short_block (n : ℕ) (hcard : 1000 ≤ #(intervalPrimes n)) :
    ∃ p : Fin 1000 → ℕ,
      (∀ i, (p i).Prime) ∧ StrictMono p ∧
      (∀ i, n ≤ p i ∧ p i ≤ 2 * n) ∧
      p (999 : Fin 1000) - p 0 ≤ n / (#(intervalPrimes n) / 1000) + 1 := by
  set q := #(intervalPrimes n) / 1000
  have hq0 : 0 < q := Nat.div_pos hcard (by norm_num)
  have hqlen : 1000 * q ≤ (doublingPrimes n).length := by
    rw [doublingPrimes_length]; exact Nat.mul_div_le _ _
  have hlenpos : 0 < (doublingPrimes n).length := by
    rw [doublingPrimes_length]; omega
  have hspan_all := sp_span_le_n n hlenpos
  have hspan : sp n (1000 * q - 1) - sp n 0 ≤ n := by
    have hi : 1000 * q - 1 < (doublingPrimes n).length := by
      have : 0 < 1000 * q := by omega
      omega
    have hj : (doublingPrimes n).length - 1 < (doublingPrimes n).length :=
      Nat.sub_lt hlenpos Nat.zero_lt_one
    have hij : 1000 * q - 1 ≤ (doublingPrimes n).length - 1 := by omega
    exact (Nat.sub_le_sub_right (sp_mono hi hj hij) _).trans hspan_all
  set B := n / q + 1
  have hB : sp n (1000 * q - 1) - sp n 0 ≤ q * B := by
    have hnB : n ≤ q * B := by
      dsimp [B]
      have h := (Nat.div_add_mod n q).symm
      have hm : n % q < q := Nat.mod_lt n hq0
      calc
        n = q * (n / q) + n % q := h
        _ ≤ q * (n / q) + q := Nat.add_le_add_left (Nat.le_of_lt hm) _
        _ = q * (n / q + 1) := by ring
    exact hspan.trans hnB
  obtain ⟨b, hbq, hd⟩ := exists_small_block n q B hq0 hqlen hB
  have hb : 1000 * b + 999 < (doublingPrimes n).length := by
    have : 1000 * b + 999 < 1000 * q := by omega
    exact lt_of_lt_of_le this hqlen
  simpa [q, B] using extract_block hb hd

lemma log_le_two_sqrt {n : ℕ} (hn : 1 ≤ n) :
    Real.log (n : ℝ) ≤ 2 * Real.sqrt (n : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hn)
  have hs : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.2 hn0
  have hmul : Real.sqrt n * Real.sqrt n = (n : ℝ) := Real.mul_self_sqrt hn0.le
  have : Real.log (n : ℝ) = 2 * Real.log (Real.sqrt n) := by
    calc
      Real.log n = Real.log (Real.sqrt n * Real.sqrt n) := by rw [hmul]
      _ = Real.log (Real.sqrt n) + Real.log (Real.sqrt n) :=
        Real.log_mul hs.ne' hs.ne'
      _ = 2 * Real.log (Real.sqrt n) := by ring
  have : Real.log (Real.sqrt n) ≤ Real.sqrt n := Real.log_le_self hs.le
  linarith

lemma log_mul_2000_le {n : ℕ} (hn : 16000000 ≤ n) :
    2000 * Real.log (n : ℝ) ≤ (n : ℝ) := by
  have hlog := log_le_two_sqrt (by omega : 1 ≤ n)
  have hsqrt : (4000 : ℝ) ≤ Real.sqrt n := by
    rw [Real.le_sqrt' (by norm_num)]
    exact_mod_cast (show (4000 : ℕ) ^ 2 ≤ n by norm_num; exact hn)
  have h1 : 2000 * Real.log n ≤ 2000 * (2 * Real.sqrt n) := by gcongr
  have h2 : 2000 * (2 * Real.sqrt n) = 4000 * Real.sqrt n := by ring
  have h3 : 4000 * Real.sqrt n ≤ Real.sqrt n * Real.sqrt n := by
    nlinarith [show (0 : ℝ) ≤ Real.sqrt n by positivity]
  have h4 : Real.sqrt n * Real.sqrt n = (n : ℝ) :=
    Real.mul_self_sqrt (by positivity)
  linarith

theorem price_refutes_universal (h : PriceTheorem1) : ¬ UniversalBound :=
  price_implies_not_universal h

lemma card_ge_half_log {n : ℕ}
    (hdiff : (n : ℝ) / (2 * Real.log (n : ℝ)) ≤ (π (2 * n) : ℝ) - π n) :
    (n : ℝ) / (2 * Real.log (n : ℝ)) ≤ (#(intervalPrimes n) : ℝ) := by
  have hπmono : π n ≤ π (2 * n) := monotone_primeCounting (by omega)
  have h2 : (π (2 * n) : ℝ) - π n = ((π (2 * n) - π n : ℕ) : ℝ) := by
    rw [Nat.cast_sub hπmono]
  exact (hdiff.trans_eq h2).trans (Nat.cast_le.mpr (card_intervalPrimes_ge_pi_diff n))

lemma card_sub_le_mul_q (card : ℕ) :
    card - 999 ≤ 1000 * (card / 1000) := by
  have hmod : card % 1000 ≤ 999 :=
    Nat.lt_succ_iff.mp (Nat.mod_lt card (by norm_num))
  have := Nat.div_add_mod card 1000
  omega

lemma diam_le_2501_log {n : ℕ} (hn : 1000000000 ≤ n)
    (hcard_r : (n : ℝ) / (2 * Real.log (n : ℝ)) ≤ (#(intervalPrimes n) : ℝ))
    (hcard : 1000 ≤ #(intervalPrimes n)) :
    ((n / (#(intervalPrimes n) / 1000) + 1 : ℕ) : ℝ) ≤ 2501 * Real.log (n : ℝ) := by
  set card := #(intervalPrimes n)
  set q := card / 1000
  have hq0 : 0 < q := Nat.div_pos hcard (by norm_num)
  have Lpos : 0 < Real.log (n : ℝ) :=
    (log_pos_iff (by positivity)).2
      (by exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 1000000000) hn))
  have hmul := card_sub_le_mul_q card
  have hcard999 : 999 < card := lt_of_lt_of_le (by norm_num) hcard
  have hq0r : (0 : ℝ) < q := by exact_mod_cast hq0
  have hden0 : (0 : ℝ) < (card - 999 : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hcard999
  have hn_div : (n : ℝ) / q ≤ 1000 * n / ((card - 999 : ℕ) : ℝ) := by
    have hq_ge : ((card - 999 : ℕ) : ℝ) ≤ 1000 * (q : ℝ) := by exact_mod_cast hmul
    have h1000 : (1000 : ℝ) ≠ 0 := by norm_num
    have : (n : ℝ) / q = (1000 * n) / (1000 * q) :=
      (mul_div_mul_left (n : ℝ) (q : ℝ) h1000).symm
    rw [this]
    exact div_le_div_of_nonneg_left (by positivity) hden0 hq_ge
  have hsqrt : (30000 : ℝ) ≤ Real.sqrt n := by
    rw [Real.le_sqrt' (by norm_num)]
    have hsq : (30000 : ℕ) ^ 2 = 900000000 := by norm_num
    exact_mod_cast (hsq ▸ le_trans (by norm_num : 900000000 ≤ 1000000000) hn)
  have h999 : (999 : ℝ) ≤ n / (10 * Real.log n) := by
    have hlog_le := log_le_two_sqrt (by omega : 1 ≤ n)
    have h1 : 9990 * Real.log n ≤ 9990 * (2 * Real.sqrt n) := by gcongr
    have h2 : 9990 * (2 * Real.sqrt n) = 19980 * Real.sqrt n := by ring
    have hs0 : (0 : ℝ) ≤ Real.sqrt n := by positivity
    have h3 : 19980 * Real.sqrt n ≤ 30000 * Real.sqrt n := by
      exact mul_le_mul_of_nonneg_right (by norm_num) hs0
    have h4 : 30000 * Real.sqrt n ≤ Real.sqrt n * Real.sqrt n := by
      exact mul_le_mul_of_nonneg_right hsqrt hs0
    have h5 : Real.sqrt n * Real.sqrt n = (n : ℝ) := Real.mul_self_sqrt (by positivity)
    have : 9990 * Real.log n ≤ n := by linarith [h1, h2, h3, h4, h5]
    rw [le_div_iff₀ (by positivity)]; linarith
  have hcard_cast : ((card - 999 : ℕ) : ℝ) = (card : ℝ) - 999 :=
    Nat.cast_sub (Nat.le_of_lt hcard999)
  have hsplit :
      (n : ℝ) / (2 * Real.log n) - (n : ℝ) / (10 * Real.log n) =
        (2 * (n : ℝ)) / (5 * Real.log n) := by
    set L := Real.log (n : ℝ)
    have h5 : (5 : ℝ) ≠ 0 := by norm_num
    have h2 : (2 : ℝ) ≠ 0 := by norm_num
    have hstep1 :
        (n : ℝ) / (2 * L) = (5 * (n : ℝ)) / (10 * L) := by
      have : (10 : ℝ) * L = 5 * (2 * L) := by ring
      rw [this, ← mul_div_mul_left (n : ℝ) (2 * L) h5]
    have hstep2 :
        (5 * (n : ℝ)) / (10 * L) - (n : ℝ) / (10 * L) =
          (4 * (n : ℝ)) / (10 * L) := by
      rw [← sub_div]; ring
    have hstep3 :
        (4 * (n : ℝ)) / (10 * L) = (2 * (n : ℝ)) / (5 * L) := by
      have : (10 : ℝ) * L = 2 * (5 * L) := by ring
      have : (4 * (n : ℝ)) / (10 * L) = (2 * (2 * (n : ℝ))) / (2 * (5 * L)) := by
        rw [this]; ring
      rw [this, mul_div_mul_left (2 * (n : ℝ)) (5 * L) h2]
    calc
      (n : ℝ) / (2 * L) - (n : ℝ) / (10 * L)
          = (5 * (n : ℝ)) / (10 * L) - (n : ℝ) / (10 * L) := by rw [hstep1]
      _ = (4 * (n : ℝ)) / (10 * L) := hstep2
      _ = (2 * (n : ℝ)) / (5 * L) := hstep3
  have hden : (2 : ℝ) * n / (5 * Real.log n) ≤ ((card - 999 : ℕ) : ℝ) := by
    have h1 : (n : ℝ) / (2 * Real.log n) - 999 ≤ (card : ℝ) - 999 := by
      linarith [hcard_r]
    have h1' : (n : ℝ) / (2 * Real.log n) - 999 ≤ ((card - 999 : ℕ) : ℝ) := by
      rwa [hcard_cast]
    have hcmp : (n : ℝ) / (2 * Real.log n) - (n : ℝ) / (10 * Real.log n) ≤
        (n : ℝ) / (2 * Real.log n) - 999 := by linarith [h999]
    have : (2 : ℝ) * n / (5 * Real.log n) ≤
        (n : ℝ) / (2 * Real.log n) - 999 := by
      rwa [← hsplit]
    exact this.trans h1'
  have hmain : 1000 * n / ((card - 999 : ℕ) : ℝ) ≤ 2500 * Real.log n := by
    have hpos : (0 : ℝ) < 2 * (n : ℝ) / (5 * Real.log n) :=
      div_pos (by positivity) (by positivity)
    have hle : 1000 * n / ((card - 999 : ℕ) : ℝ) ≤
        1000 * n / (2 * n / (5 * Real.log n)) :=
      div_le_div_of_nonneg_left (by positivity) hpos hden
    have heq : 1000 * (n : ℝ) / (2 * (n : ℝ) / (5 * Real.log n)) =
        2500 * Real.log n := by
      have hn0 : (n : ℝ) ≠ 0 := by
        have : (0 : ℕ) < n := lt_of_lt_of_le (by norm_num) hn
        exact Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp this)
      set L := Real.log (n : ℝ)
      calc
        1000 * (n : ℝ) / (2 * (n : ℝ) / (5 * L))
            = 1000 * (n : ℝ) * (5 * L) / (2 * (n : ℝ)) := by rw [div_div_eq_mul_div]
        _ = 1000 * (5 * L) * ((n : ℝ) / (n : ℝ)) / 2 := by ring
        _ = 1000 * (5 * L) * 1 / 2 := by rw [div_self hn0]
        _ = 2500 * L := by ring
    linarith [hle, heq]
  have hcast : ((n / q + 1 : ℕ) : ℝ) ≤ (n : ℝ) / q + 1 := by
    have h := Nat.cast_div_le (α := ℝ) (m := n) (n := q)
    rw [Nat.cast_add, Nat.cast_one]
    linarith
  have hone : (1 : ℝ) ≤ Real.log n := by
    have : Real.exp 1 ≤ (n : ℝ) := by
      have : Real.exp 1 ≤ 3 := (Real.exp_one_lt_d9).le.trans (by norm_num)
      exact this.trans (by exact_mod_cast (le_trans (by norm_num : 3 ≤ 1000000000) hn))
    have := log_le_log (Real.exp_pos _) this
    simpa [Real.log_exp] using this
  calc
    ((n / q + 1 : ℕ) : ℝ) ≤ (n : ℝ) / q + 1 := hcast
    _ ≤ 2500 * Real.log n + 1 := by linarith [hn_div, hmain]
    _ ≤ 2500 * Real.log n + Real.log n := by linarith [hone]
    _ = 2501 * Real.log n := by ring

lemma log_ceil_le {x : ℝ} (hx : 1 ≤ x) :
    Real.log (⌈x⌉₊ : ℝ) ≤ Real.log x + 1 := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (by norm_num) hx
  have hn_le : (⌈x⌉₊ : ℝ) ≤ x + 1 := by
    have h1 : (⌈x⌉₊ : ℝ) ≤ ⌊x⌋₊ + 1 := by exact_mod_cast Nat.ceil_le_floor_add_one x
    have h2 : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0.le
    linarith
  have hnpos : (0 : ℝ) < ⌈x⌉₊ := by
    have : (0 : ℕ) < ⌈x⌉₊ := Nat.ceil_pos.mpr hx0
    exact_mod_cast this
  have hlog : Real.log (⌈x⌉₊ : ℝ) ≤ Real.log (x + 1) :=
    log_le_log hnpos (by linarith [hn_le])
  have hxp1 : Real.log (x + 1) ≤ Real.log x + 1 := by
    have hx0ne : x ≠ 0 := hx0.ne'
    rw [show x + 1 = x * (1 + x⁻¹) by field_simp [hx0ne]]
    rw [Real.log_mul hx0ne (by positivity)]
    have : Real.log (1 + x⁻¹) ≤ x⁻¹ := by
      have := Real.log_le_sub_one_of_pos (x := 1 + x⁻¹) (by positivity)
      linarith
    have : x⁻¹ ≤ 1 := (inv_le_one_iff₀).2 (Or.inr hx)
    linarith
  linarith

theorem clustered_thousand_primes :
    ∃ X0 : ℝ, ∀ x ≥ X0,
      ∃ p : Fin 1000 → ℕ,
        (∀ i, (p i).Prime) ∧
        StrictMono p ∧
        (∀ i, ⌈x⌉₊ ≤ p i ∧ p i ≤ 2 * ⌈x⌉₊) ∧
        ((p (999 : Fin 1000) : ℝ) - (p 0 : ℝ) ≤ 3000 * Real.log x) := by
  obtain ⟨Nπ, hπ⟩ := many_primes_in_doubling
  let N0n : ℕ := max Nπ 1000000000
  refine ⟨(N0n : ℝ), ?_⟩
  intro x hx
  set n := ⌈x⌉₊
  have hnN : N0n ≤ n := by
    have : (N0n : ℝ) ≤ n := hx.trans (Nat.le_ceil x)
    exact_mod_cast this
  have hnπ : Nπ ≤ n := le_trans (le_max_left _ _) hnN
  have hnbig : (1000000000 : ℕ) ≤ n := le_trans (le_max_right _ _) hnN
  have hn16 : (16000000 : ℕ) ≤ n := le_trans (by norm_num) hnbig
  have hcard_r := card_ge_half_log (hπ n hnπ)
  have Lpos : 0 < Real.log (n : ℝ) :=
    (log_pos_iff (by positivity)).2
      (by exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 1000000000) hnbig))
  have h1000 : 1000 ≤ #(intervalPrimes n) := by
    have : (1000 : ℝ) ≤ n / (2 * Real.log n) := by
      rw [le_div_iff₀ (by positivity)]; linarith [log_mul_2000_le hn16]
    exact_mod_cast (this.trans hcard_r)
  obtain ⟨p, hp, hm, hI, hdiam⟩ := short_block n h1000
  refine ⟨p, hp, hm, hI, ?_⟩
  have hdiam_r : ((p (999 : Fin 1000) - p 0 : ℕ) : ℝ) ≤ 2501 * Real.log n :=
    (Nat.cast_le.mpr hdiam).trans (diam_le_2501_log hnbig hcard_r h1000)
  have hx1 : (1 : ℝ) ≤ x := by
    have : (1 : ℝ) ≤ N0n := by
      exact_mod_cast (le_trans (by norm_num : 1 ≤ 1000000000) (le_max_right Nπ _))
    exact this.trans hx
  have hlogn' : Real.log (n : ℝ) ≤ Real.log x + 1 := by
    simpa [n] using log_ceil_le hx1
  have hlogx6 : (6 : ℝ) ≤ Real.log x := by
    have he : Real.exp 1 ≤ 3 := (Real.exp_one_lt_d9).le.trans (by norm_num)
    have hexp : Real.exp 6 ≤ (1000000000 : ℝ) := by
      have hpow : Real.exp 6 = (Real.exp 1) ^ (6 : ℕ) := by
        rw [← Real.exp_nat_mul]; norm_num
      calc
        Real.exp 6 = (Real.exp 1) ^ (6 : ℕ) := hpow
        _ ≤ (3 : ℝ) ^ 6 := by gcongr
        _ ≤ 1000000000 := by norm_num
    have : Real.log (Real.exp 6) ≤ Real.log x :=
      log_le_log (Real.exp_pos _)
        (le_trans hexp (le_trans (by exact_mod_cast (le_max_right Nπ 1000000000)) hx))
    simpa [Real.log_exp] using this
  have hfinal : 2501 * Real.log n ≤ 3000 * Real.log x := by
    have h1 : 2501 * Real.log n ≤ 2501 * (Real.log x + 1) := by gcongr
    have h2 : 2501 * (Real.log x + 1) ≤ 3000 * Real.log x := by
      have : 2501 ≤ 499 * Real.log x := by nlinarith [hlogx6]
      linarith
    exact h1.trans h2
  have hsub : p 0 ≤ p (999 : Fin 1000) :=
    StrictMono.monotone hm (Fin.zero_le _)
  have hpnat : (p (999 : Fin 1000) : ℝ) - (p 0 : ℝ) = ((p 999 - p 0 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hsub]
  rw [hpnat]
  linarith [hdiam_r, hfinal]

end Green44Asymp
