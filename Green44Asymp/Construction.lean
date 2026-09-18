/-
Price Theorem 1 construction: clustered primes + block set T ⊆ S.
-/

/-
Lean formalization author: @PskProduction (Nikita)
Mathematics: Liam Price and GPT-5.4 Pro (JSP-001007 / Green 44)
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Green44Asymp.Cluster

open Nat Real Finset Filter Asymptotics
open scoped Topology Nat.Prime

namespace Green44Asymp

noncomputable section

def allowedResidues (p KD : ℕ) [NeZero p] : Finset (ZMod p) :=
  (Icc 1 ((p + 1) / 2)).image fun (r : ℕ) => (r : ZMod p) - (KD : ZMod p)

def forbiddenResidues (p KD : ℕ) [NeZero p] : Finset (ZMod p) :=
  univ \ allowedResidues p KD

def blockSet (M K L : ℕ) : Finset ℕ :=
  ((range K).product (Icc 1 L)).image fun p => p.1 * M + p.2

lemma card_Icc_one_half (p : ℕ) : #(Icc 1 ((p + 1) / 2)) = (p + 1) / 2 := by
  rw [Nat.card_Icc]; omega

lemma allowedResidues_card {p KD : ℕ} [NeZero p] (hp : 3 ≤ p) :
    #(allowedResidues p KD) = (p + 1) / 2 := by
  classical
  refine (Finset.card_image_of_injOn ?_).trans (card_Icc_one_half p)
  intro a ha b hb h
  have hab : (a : ZMod p) = (b : ZMod p) := by
    simpa using congrArg (fun z : ZMod p => z + (KD : ZMod p)) h
  have ha' : a ≤ (p + 1) / 2 := (mem_Icc.mp ha).2
  have hb' : b ≤ (p + 1) / 2 := (mem_Icc.mp hb).2
  have hbound : (p + 1) / 2 < p := by omega
  have := congrArg ZMod.val hab
  rwa [ZMod.val_cast_of_lt (lt_of_le_of_lt ha' hbound),
    ZMod.val_cast_of_lt (lt_of_le_of_lt hb' hbound)] at this

lemma forbiddenResidues_card {p KD : ℕ} [NeZero p] (hp : Odd p) (hp3 : 3 ≤ p) :
    #(forbiddenResidues p KD) = p / 2 := by
  classical
  have hA := allowedResidues_card (p := p) (KD := KD) hp3
  have huniv : #(univ : Finset (ZMod p)) = p := by simp [ZMod.card]
  rw [forbiddenResidues, card_sdiff_of_subset (subset_univ _), huniv, hA]
  obtain ⟨k, hk⟩ := hp
  omega

lemma mem_blockSet {M K L n : ℕ} :
    n ∈ blockSet M K L ↔ ∃ k < K, ∃ t, t ∈ Icc 1 L ∧ n = k * M + t := by
  classical
  constructor
  · intro hn
    rcases mem_image.mp hn with ⟨⟨k, t⟩, hkt, rfl⟩
    rcases mem_product.mp hkt with ⟨hk, ht⟩
    exact ⟨k, mem_range.mp hk, t, ht, rfl⟩
  · rintro ⟨k, hk, t, ht, rfl⟩
    exact mem_image.mpr ⟨⟨k, t⟩, mem_product.mpr ⟨mem_range.mpr hk, ht⟩, rfl⟩

lemma blockSet_card {M K L : ℕ} (hLM : L < M) :
    #(blockSet M K L) = K * L := by
  classical
  have hinj :
      Set.InjOn (fun p : ℕ × ℕ => p.1 * M + p.2)
        ↑((range K).product (Icc 1 L)) := by
    intro ⟨k₁, t₁⟩ h₁ ⟨k₂, t₂⟩ h₂ heq
    have ht1' := mem_Icc.mp (mem_product.mp (by exact_mod_cast h₁)).2
    have ht2' := mem_Icc.mp (mem_product.mp (by exact_mod_cast h₂)).2
    have hmod : t₁ % M = t₂ % M := by
      have := congrArg (fun n : ℕ => n % M) heq
      simpa [Nat.add_mul_mod_self_left] using this
    have ht_eq : t₁ = t₂ := by
      rwa [Nat.mod_eq_of_lt (lt_of_le_of_lt ht1'.2 hLM),
        Nat.mod_eq_of_lt (lt_of_le_of_lt ht2'.2 hLM)] at hmod
    subst ht_eq
    have hmul : k₁ * M = k₂ * M := Nat.add_right_cancel heq
    have hM0 : 0 < M := lt_of_le_of_lt (Nat.zero_le L) hLM
    have : k₁ = k₂ := Nat.eq_of_mul_eq_mul_right hM0 hmul
    subst this
    rfl
  unfold blockSet
  rw [Finset.card_image_of_injOn hinj]
  simp [card_product, card_range, Nat.card_Icc]

lemma blockSet_subset_Icc {M K L N : ℕ}
    (hK : K = N / M) (hL_lt : L < M) :
    blockSet M K L ⊆ Icc 1 N := by
  intro n hn
  rcases (mem_blockSet).1 hn with ⟨k, hk, t, ht, rfl⟩
  have ht' := mem_Icc.mp ht
  refine mem_Icc.mpr ⟨le_trans ht'.1 (Nat.le_add_left _ _), ?_⟩
  cases K with
  | zero => omega
  | succ K' =>
    have hk' : k ≤ K' := Nat.lt_succ_iff.mp hk
    have h1 : k * M + t ≤ K' * M + L := by
      exact Nat.add_le_add (Nat.mul_le_mul_right M hk') ht'.2
    have h2 : K' * M + L < (K' + 1) * M := by
      rw [Nat.succ_mul]
      exact Nat.add_lt_add_left hL_lt _
    have h3 : (K' + 1) * M ≤ N := by
      rw [hK, mul_comm]
      exact Nat.mul_div_le N M
    exact le_trans h1 (le_of_lt (lt_of_lt_of_le h2 h3))

private lemma mul_le_mul_KD {K k d D : ℕ} (hk : k < K) (hd : d ≤ D) :
    k * d ≤ K * D := by
  cases K with
  | zero => omega
  | succ K' =>
    have : k ≤ K' := Nat.lt_succ_iff.mp hk
    calc
      k * d ≤ K' * d := Nat.mul_le_mul_right d this
      _ ≤ K' * D := Nat.mul_le_mul_left K' hd
      _ ≤ (K' + 1) * D := Nat.mul_le_mul_right D (Nat.le_succ _)

lemma drift_rep_bounds {M D K L k t d : ℕ}
    (ht : t ∈ Icc 1 L) (hk : k < K) (hd : d ≤ D)
    (hL : L = (M + 1) / 2 - K * D) (hKD : K * D ≤ (M + 1) / 2) :
    1 ≤ t + K * D - k * d ∧ t + K * D - k * d ≤ (M + 1) / 2 := by
  have ht' := mem_Icc.mp ht
  have hkd := mul_le_mul_KD hk hd
  refine ⟨?_, ?_⟩
  · have : t ≤ t + K * D - k * d := by
      have h := Nat.le_add_right t (K * D - k * d)
      rwa [← Nat.add_sub_assoc hkd] at h
    exact le_trans ht'.1 this
  · have h1 : t + K * D - k * d ≤ t + K * D := Nat.sub_le _ _
    have h2 : t + K * D ≤ L + K * D := Nat.add_le_add_right ht'.2 _
    have h3 : L + K * D = (M + 1) / 2 := by
      rw [hL, Nat.sub_add_cancel hKD]
    omega

lemma block_mem_allowed {p M D K L k t : ℕ} [NeZero p]
    (hpM : M ≤ p)
    (ht : t ∈ Icc 1 L) (hk : k < K) (hd : p - M ≤ D)
    (hL : L = (M + 1) / 2 - K * D) (hKD : K * D ≤ (M + 1) / 2) :
    ((k * M + t : ℕ) : ZMod p) ∈ allowedResidues p (K * D) := by
  classical
  set d := p - M
  obtain ⟨hs1, hs2⟩ := drift_rep_bounds (M := M) (D := D) (K := K) (L := L)
    (k := k) (t := t) (d := d) ht hk hd hL hKD
  set s := t + K * D - k * d
  have hs2' : s ≤ (p + 1) / 2 := le_trans hs2 (by omega)
  refine mem_image.mpr ⟨s, mem_Icc.mpr ⟨hs1, hs2'⟩, ?_⟩
  have hkd := mul_le_mul_KD hk hd
  have hkd' : k * d ≤ t + K * D := le_trans hkd (Nat.le_add_left _ _)
  have hsum : k * M + t + K * D = k * p + s := by
    have : t + K * D = s + k * d := (Nat.sub_add_cancel hkd').symm
    have hp : p = M + d := (Nat.add_sub_of_le hpM).symm
    calc
      k * M + t + K * D = k * M + (t + K * D) := by ring
      _ = k * M + (s + k * d) := by rw [this]
      _ = k * (M + d) + s := by ring
      _ = k * p + s := by rw [← hp]
  have hadd : ((k * M + t + K * D : ℕ) : ZMod p) = (s : ZMod p) := by
    have := congrArg (fun m : ℕ => (m : ZMod p)) hsum
    simpa [ZMod.natCast_self] using this
  have hgoal :
      ((k * M + t : ℕ) : ZMod p) = (s : ZMod p) - ((K * D : ℕ) : ZMod p) := by
    have h1 : ((k * M + t : ℕ) : ZMod p) =
        ((k * M + t + K * D : ℕ) : ZMod p) - ((K * D : ℕ) : ZMod p) := by
      push_cast; ring
    rw [h1, hadd]
  exact hgoal.symm

lemma L_ge_M_div_three {M K D L : ℕ}
    (hL : L = (M + 1) / 2 - K * D) (hKD : K * D ≤ M / 6) (hM : 6 ≤ M) :
    M / 3 ≤ L := by omega

lemma KM_ge_N_sub_M {N M K : ℕ} (hK : K = N / M) (hM : 0 < M) :
    N - M ≤ K * M := by
  have hmod := Nat.mod_lt N hM
  have hsum : M * (N / M) + N % M = N := Nat.div_add_mod N M
  have hKM : K * M = N - N % M := by
    rw [hK, mul_comm]
    exact Nat.eq_sub_of_add_eq hsum
  rw [hKM]
  omega

lemma blockSet_card_gt_N_div_ten {N M K L D : ℕ}
    (hK : K = N / M) (hL : L = (M + 1) / 2 - K * D)
    (hKD : K * D ≤ M / 6) (hM : 6 ≤ M) (hL_lt : L < M)
    (hMN : M < N / 2) (hKsmall : 10 * K ≤ N) (hN : 30 ≤ N) :
    N < 10 * #(blockSet M K L) := by
  have hcard : #(blockSet M K L) = K * L := blockSet_card hL_lt
  have hLge : M / 3 ≤ L := L_ge_M_div_three hL hKD hM
  have hM0 : 0 < M := lt_of_lt_of_le (by norm_num) hM
  have hKM : N - M ≤ K * M := KM_ge_N_sub_M hK hM0
  have h3L : M - 2 ≤ 3 * L := by
    have : M - 2 ≤ 3 * (M / 3) := by omega
    exact le_trans this (Nat.mul_le_mul_left 3 hLge)
  have hKL : K * (M - 2) ≤ 3 * (K * L) := by
    calc
      K * (M - 2) ≤ K * (3 * L) := Nat.mul_le_mul_left K h3L
      _ = 3 * (K * L) := by ring
  have hA : N - M - 2 * K ≤ K * (M - 2) := by
    have hmul : K * (M - 2) = K * M - 2 * K := by
      rw [Nat.mul_sub]; omega
    have : 2 * K ≤ N - M := by omega
    omega
  have hA' : N - M - 2 * K ≤ 3 * (K * L) := le_trans hA hKL
  have hB : 3 * N < 10 * (N - M - 2 * K) := by omega
  have : 3 * N < 10 * (3 * (K * L)) :=
    lt_of_lt_of_le hB (Nat.mul_le_mul_left 10 hA')
  have : N < 10 * (K * L) := by omega
  rwa [hcard]

lemma price_counterexample_of_cluster {N : ℕ} {p : Fin 1000 → ℕ}
    (hp : ∀ i, (p i).Prime) (hm : StrictMono p)
    (_hpow : (p (999 : Fin 1000)) ^ 10 < N ^ 9)
    (hM6 : 6 ≤ p 0)
    (hN : 30 ≤ N)
    (hMN : p 0 < N / 2)
    (_hKpos : 0 < N / p 0)
    (hKD : (N / p 0) * (p (999 : Fin 1000) - p 0) ≤ p 0 / 6)
    (hKsmall : 10 * (N / p 0) ≤ N) :
    ∃ (R : (i : Fin 1000) → Finset (ZMod (p i))),
      (∀ i, (R i).card = (p i) / 2) ∧
      let S := (Icc 1 N).filter (fun n => ∀ i, (n : ZMod (p i)) ∉ R i)
      N < 10 * S.card := by
  classical
  set M := p 0
  set D := p (999 : Fin 1000) - M
  set K := N / M
  set L := (M + 1) / 2 - K * D
  have hK : K = N / M := rfl
  have hL : L = (M + 1) / 2 - K * D := rfl
  have hKD' : K * D ≤ M / 6 := by simpa [M, D, K] using hKD
  have hKD_half : K * D ≤ (M + 1) / 2 := by omega
  have hL_lt : L < M := by
    have : L ≤ (M + 1) / 2 := Nat.sub_le _ _
    omega
  have hLge : M / 3 ≤ L := L_ge_M_div_three hL hKD' hM6
  have hLpos : 0 < L := lt_of_lt_of_le (by omega : 0 < M / 3) hLge
  let R : (i : Fin 1000) → Finset (ZMod (p i)) := fun i =>
    haveI : NeZero (p i) := ⟨(hp i).ne_zero⟩
    forbiddenResidues (p i) (K * D)
  have hRcard : ∀ i, (R i).card = (p i) / 2 := by
    intro i
    haveI : NeZero (p i) := ⟨(hp i).ne_zero⟩
    have hodd : Odd (p i) := (hp i).odd_of_ne_two (by
      have : 3 ≤ p i := by
        have : M ≤ p i := hm.monotone (Fin.zero_le i)
        omega
      omega)
    have hp3 : 3 ≤ p i := by
      have : M ≤ p i := hm.monotone (Fin.zero_le i)
      omega
    simpa [R] using forbiddenResidues_card (p := p i) (KD := K * D) hodd hp3
  let T := blockSet M K L
  have hTsub : T ⊆ Icc 1 N := blockSet_subset_Icc hK hL_lt
  have hT_in_S :
      T ⊆ (Icc 1 N).filter (fun n => ∀ i, (n : ZMod (p i)) ∉ R i) := by
    intro n hn
    have hnI : n ∈ Icc 1 N := hTsub hn
    refine mem_filter.mpr ⟨hnI, ?_⟩
    intro i
    haveI : NeZero (p i) := ⟨(hp i).ne_zero⟩
    rcases (mem_blockSet).1 hn with ⟨k, hk, t, ht, rfl⟩
    have hpM : M ≤ p i := hm.monotone (Fin.zero_le i)
    have hd : p i - M ≤ D := by
      have hhi : p i ≤ p (999 : Fin 1000) := hm.monotone (by exact Fin.le_last i)
      omega
    have hmem := block_mem_allowed (p := p i) (M := M) (D := D) (K := K) (L := L)
      (k := k) (t := t) hpM ht hk hd hL hKD_half
    intro hR
    have hR' : ((k * M + t : ℕ) : ZMod (p i)) ∈
        univ \ allowedResidues (p i) (K * D) := by
      simpa [R, forbiddenResidues] using hR
    exact (mem_sdiff.mp hR').2 hmem
  have hTcard : N < 10 * #T :=
    blockSet_card_gt_N_div_ten hK hL hKD' hM6 hL_lt hMN hKsmall hN
  refine ⟨R, hRcard, ?_⟩
  change N < 10 * #((Icc 1 N).filter (fun n => ∀ i, (n : ZMod (p i)) ∉ R i))
  exact lt_of_lt_of_le hTcard (Nat.mul_le_mul_left 10 (card_le_card hT_in_S))

lemma tendsto_nat_rpow_atTop (r : ℝ) (hr : 0 < r) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ r) atTop atTop :=
  (tendsto_rpow_atTop hr).comp tendsto_natCast_atTop_atTop

private def priceX (N : ℕ) : ℝ := (1 / 4) * (N : ℝ) ^ ((9 : ℝ) / 10)

private lemma tendsto_priceX : Tendsto priceX atTop atTop :=
  (tendsto_nat_rpow_atTop _ (by norm_num)).const_mul_atTop (by norm_num)

private lemma priceX_nonneg (N : ℕ) : 0 ≤ priceX N := by
  simp only [priceX]
  positivity

private lemma priceX_le_N {N : ℕ} (hN : 1 ≤ N) : priceX N ≤ (N : ℝ) := by
  simp only [priceX]
  have hone : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hpow : (N : ℝ) ^ ((9 : ℝ) / 10) ≤ N := by
    calc
      (N : ℝ) ^ ((9 : ℝ) / 10) ≤ (N : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hone (by norm_num)
      _ = N := Real.rpow_one N
  linarith [hpow]

private lemma nine_tenths_div_N_tendsto_zero :
    Tendsto (fun N : ℕ => (N : ℝ) ^ ((9 : ℝ) / 10) / N) atTop (nhds 0) := by
  have ht : Tendsto (fun x : ℝ => x ^ (-((1 : ℝ) / 10))) atTop (nhds 0) :=
    tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < (1 : ℝ) / 10)
  refine ht.comp tendsto_natCast_atTop_atTop |>.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (Nat.lt_of_lt_of_le (by norm_num) hN)
  calc
    (N : ℝ) ^ (-((1 : ℝ) / 10)) = (N : ℝ) ^ ((9 : ℝ) / 10) / (N : ℝ) ^ (1 : ℝ) := by
      rw [← Real.rpow_sub hN0]; ring_nf
    _ = (N : ℝ) ^ ((9 : ℝ) / 10) / N := by rw [Real.rpow_one]

private lemma log_priceX_div_rpow_tendsto_zero :
    Tendsto (fun N : ℕ => Real.log (priceX N) / (N : ℝ) ^ ((4 : ℝ) / 5)) atTop (nhds 0) := by
  have hlogN :=
    (isLittleO_log_rpow_atTop (r := (4 : ℝ) / 5) (by norm_num)).comp_tendsto
      tendsto_natCast_atTop_atTop |>.tendsto_div_nhds_zero
  refine squeeze_zero' ?_ ?_ hlogN
  · filter_upwards [eventually_ge_atTop 1, tendsto_priceX.eventually_gt_atTop 1] with N hN hxpos
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (Nat.lt_of_lt_of_le (by norm_num) hN)
    have hden : (0 : ℝ) ≤ (N : ℝ) ^ ((4 : ℝ) / 5) := Real.rpow_nonneg hN0.le _
    exact div_nonneg (log_nonneg (le_of_lt hxpos)) hden
  · filter_upwards [eventually_ge_atTop 1, tendsto_priceX.eventually_gt_atTop 1] with N hN hxpos
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (Nat.lt_of_lt_of_le (by norm_num) hN)
    have hden : (0 : ℝ) < (N : ℝ) ^ ((4 : ℝ) / 5) := Real.rpow_pos_of_pos hN0 _
    exact div_le_div_of_nonneg_right
      (log_le_log (lt_trans (by norm_num) hxpos) (priceX_le_N hN)) hden.le

private lemma N_div_priceX {N : ℕ} (hN : 0 < N) :
    (N : ℝ) / priceX N = 4 * (N : ℝ) ^ ((1 : ℝ) / 10) := by
  simp only [priceX]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  field_simp
  rw [← Real.rpow_add hN0]
  norm_num

private lemma ceil_priceX_le (N : ℕ) :
    (⌈priceX N⌉₊ : ℝ) ≤ priceX N + 1 := by
  have h1 : (⌈priceX N⌉₊ : ℝ) ≤ ⌊priceX N⌋₊ + 1 := by
    exact_mod_cast Nat.ceil_le_floor_add_one (priceX N)
  have h2 : (⌊priceX N⌋₊ : ℝ) ≤ priceX N := Nat.floor_le (priceX_nonneg N)
  linarith

private lemma KD_identity (N : ℕ) (hN : 0 < N) :
    (12000 : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 10) * Real.log (priceX N) =
      (288000 * (Real.log (priceX N) / (N : ℝ) ^ ((4 : ℝ) / 5))) * (priceX N / 6) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hden : (N : ℝ) ^ ((4 : ℝ) / 5) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hN0 _)
  simp only [priceX]
  ring_nf
  field_simp [hden, show (4 : ℝ) ≠ 0 from by norm_num, show (6 : ℝ) ≠ 0 from by norm_num,
    show (288000 : ℝ) ≠ 0 from by norm_num]
  have hrpow : (N : ℝ) ^ ((1 : ℝ) / 10) * (N : ℝ) ^ ((4 : ℝ) / 5) = (N : ℝ) ^ ((9 : ℝ) / 10) := by
    rw [← Real.rpow_add hN0]; norm_num
  rw [← hrpow, mul_assoc]
  ring

lemma eventually_price_thresholds (X0 : ℝ) :
    ∃ N0 : ℕ, ∀ N ≥ N0,
      let x := priceX N
      X0 ≤ x ∧
      (5 : ℝ) < x ∧
      (2 * ⌈x⌉₊ : ℕ) ^ 10 < N ^ 9 ∧
      2 * ⌈x⌉₊ < N / 2 ∧
      (12000 : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 10) * Real.log x + 1 ≤ x / 6 ∧
      (40 : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 10) ≤ (N : ℝ) ∧
      (30 : ℕ) ≤ N := by
  have hX := tendsto_priceX.eventually_ge_atTop X0
  have h5 := tendsto_priceX.eventually_gt_atTop (5 : ℝ)
  have h30 := eventually_ge_atTop (30 : ℕ)
  have h40 : ∀ᶠ N : ℕ in atTop,
      (40 : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 10) ≤ (N : ℝ) := by
    have h := (tendsto_nat_rpow_atTop ((9 : ℝ) / 10) (by norm_num)).eventually_ge_atTop 40
    filter_upwards [h] with N hN
    have hNpos : (0 : ℕ) < N := by
      by_cases hN0 : N = 0
      · simp [hN0, Real.rpow_zero] at hN; norm_num at hN
      · exact Nat.pos_of_ne_zero hN0
    have hN40 : (40 : ℕ) ≤ N := by
      have hone : (1 : ℝ) ≤ N := by exact_mod_cast (Nat.succ_le_iff.mp hNpos)
      have : (40 : ℝ) ≤ N := le_trans hN (by
        calc
          (N : ℝ) ^ ((9 : ℝ) / 10) ≤ (N : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hone (by norm_num)
          _ = N := Real.rpow_one N)
      exact_mod_cast this
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (Nat.lt_of_lt_of_le (by norm_num) hN40)
    have hmul : (N : ℝ) ^ ((9 : ℝ) / 10) * (N : ℝ) ^ ((1 : ℝ) / 10) = N := by
      rw [← Real.rpow_add hN0]; norm_num
    have hle : (40 : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 10) ≤
        (N : ℝ) ^ ((9 : ℝ) / 10) * (N : ℝ) ^ ((1 : ℝ) / 10) := by gcongr
    linarith [hle, hmul]
  have hhalf : ∀ᶠ N : ℕ in atTop, 2 * ⌈priceX N⌉₊ < N / 2 := by
    have hsmall := nine_tenths_div_N_tendsto_zero.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8))
    filter_upwards [h5, hsmall, eventually_ge_atTop 64] with N hx5 hratio h64
    have hceil := ceil_priceX_le N
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le (by norm_num) h64)
    have ha : (N : ℝ) ^ ((9 : ℝ) / 10) < N / 8 := by
      rw [show (N : ℝ) / 8 = (1 / 8) * N by ring]
      exact (div_lt_iff₀ hN0).mp hratio
    have hx2 : 2 * priceX N = (1 / 2) * (N : ℝ) ^ ((9 : ℝ) / 10) := by simp [priceX]; ring
    have h2le : (2 : ℝ) ≤ N / 4 := by
      have : (8 : ℝ) ≤ N := by exact_mod_cast (le_trans (by norm_num : (8 : ℕ) ≤ 64) h64)
      linarith
    have hmargin : 2 * priceX N + 3 < N / 2 := by linarith [hx2, ha, h2le]
    have hNat : 4 * ⌈priceX N⌉₊ + 2 < N := by
      have hR : (4 * ⌈priceX N⌉₊ + 2 : ℝ) < N := by linarith [hceil, hmargin]
      exact_mod_cast hR
    have hmul : 2 * ⌈priceX N⌉₊ * 2 < N - 1 := by omega
    exact (Nat.lt_div_iff_mul_lt (show 0 < 2 by norm_num)).mpr hmul
  have hpow : ∀ᶠ N : ℕ in atTop,
      (2 * ⌈priceX N⌉₊ : ℕ) ^ 10 < N ^ 9 := by
    filter_upwards [h5] with N hx5
    set x := priceX N
    set a := (N : ℝ) ^ ((9 : ℝ) / 10)
    have hceil := ceil_priceX_le N
    have h2ceil : ((2 * ⌈x⌉₊ : ℕ) : ℝ) ≤ a / 2 + 2 := by
      have : (2 : ℝ) * ⌈x⌉₊ ≤ 2 * x + 2 := by linarith [hceil]
      have : 2 * x = a / 2 := by simp [x, a, priceX]; ring
      push_cast at *; linarith
    have hlt : a / 2 + 2 < a := by
      have : (20 : ℝ) < a := by
        have : (20 : ℝ) < 4 * x := by linarith [hx5]
        simpa [x, a, priceX] using this
      linarith
    have hbase : ((2 * ⌈x⌉₊ : ℕ) : ℝ) < a := lt_of_le_of_lt h2ceil hlt
    have hpowR : ((2 * ⌈x⌉₊ : ℕ) : ℝ) ^ (10 : ℕ) < a ^ (10 : ℕ) :=
      pow_lt_pow_left₀ hbase (by positivity) (by norm_num)
    have ha10 : a ^ (10 : ℕ) = (N : ℝ) ^ (9 : ℕ) := by
      have hN0 : (0 : ℝ) ≤ N := by positivity
      calc
        a ^ (10 : ℕ) = a ^ (10 : ℝ) := (rpow_natCast _ _).symm
        _ = ((N : ℝ) ^ ((9 : ℝ) / 10)) ^ (10 : ℝ) := rfl
        _ = (N : ℝ) ^ (((9 : ℝ) / 10) * 10) := by rw [← rpow_mul hN0]
        _ = (N : ℝ) ^ (9 : ℝ) := by ring_nf
        _ = (N : ℝ) ^ (9 : ℕ) := rpow_natCast _ _
    have : ((2 * ⌈x⌉₊ : ℕ) ^ 10 : ℝ) < (N ^ 9 : ℝ) := by
      simpa [Nat.cast_pow, ha10] using hpowR
    exact_mod_cast this
  have hKD' : ∀ᶠ N : ℕ in atTop,
      (12000 : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 10) * Real.log (priceX N) + 1 ≤
        priceX N / 6 := by
    have hrat :=
      Metric.tendsto_nhds.mp
        (log_priceX_div_rpow_tendsto_zero.const_mul (288000 : ℝ)).norm (1 / 2) (by norm_num)
    filter_upwards [hrat, h5, tendsto_priceX.eventually_ge_atTop 12,
      eventually_gt_atTop 0] with N hrat hx5 hx12 hNpos
    have hnonneg :
        (0 : ℝ) ≤ 288000 * (Real.log (priceX N) / (N : ℝ) ^ ((4 : ℝ) / 5)) := by
      have hx : (0 : ℝ) < priceX N := lt_trans (by norm_num) hx5
      have hN0r : (0 : ℝ) < N := by exact_mod_cast hNpos
      have hone : (1 : ℝ) < priceX N := lt_trans (by norm_num) hx5
      exact mul_nonneg (by norm_num) (div_nonneg (log_pos hone).le (Real.rpow_nonneg hN0r.le _))
    have hlt :
        288000 * (Real.log (priceX N) / (N : ℝ) ^ ((4 : ℝ) / 5)) < 1 / 2 := by
      simpa [dist_eq_norm_sub, norm_mul, norm_of_nonneg hnonneg, norm_zero, sub_zero] using hrat
    have hxpos : (0 : ℝ) < priceX N / 6 := by
      have hx : (0 : ℝ) < priceX N := lt_trans (by norm_num) hx5
      exact div_pos hx (by norm_num : (0 : ℝ) < 6)
    have hbound : (12000 : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 10) * Real.log (priceX N) <
        (1 / 2) * (priceX N / 6) := by
      rw [KD_identity N hNpos]
      exact mul_lt_mul_of_pos_right hlt hxpos
    have h1 : (1 : ℝ) ≤ priceX N / 12 := by linarith [hx12]
    linarith [hbound, h1]
  have hall := hX.and <| h5.and <| hpow.and <| hhalf.and <| hKD'.and <| h40.and h30
  rw [eventually_atTop] at hall
  obtain ⟨N0, hN0⟩ := hall
  refine ⟨N0, fun N hN => hN0 N hN⟩

theorem priceTheorem1 : PriceTheorem1 := by
  obtain ⟨X0, hcluster⟩ := clustered_thousand_primes
  obtain ⟨N0, hth⟩ := eventually_price_thresholds X0
  refine ⟨N0, ?_⟩
  intro N hNge
  have hpack := hth N hNge
  set x := priceX N
  obtain ⟨hxX, hx5, hpowN, hhalf, hKDr, h40, h30⟩ := hpack
  obtain ⟨p, hp, hm, hI, hdiam⟩ := hcluster x hxX
  have hceil_le : ⌈x⌉₊ ≤ p 0 := (hI 0).1
  have hp_le : p (999 : Fin 1000) ≤ 2 * ⌈x⌉₊ := (hI (999 : Fin 1000)).2
  have hpow : (p (999 : Fin 1000)) ^ 10 < N ^ 9 :=
    lt_of_le_of_lt (Nat.pow_le_pow_left hp_le 10) hpowN
  have hM6 : 6 ≤ p 0 := by
    have : (5 : ℝ) < ⌈x⌉₊ := by
      calc (5 : ℝ) < x := hx5
        _ ≤ ⌈x⌉₊ := Nat.le_ceil x
    have : (6 : ℕ) ≤ ⌈x⌉₊ := by exact_mod_cast Nat.succ_le_of_lt (by exact_mod_cast this)
    omega
  have hMN : p 0 < N / 2 :=
    lt_of_le_of_lt (hI 0).2 hhalf
  have hKpos : 0 < N / p 0 := by
    have hpN : p 0 ≤ N := by
      have hmul : p 0 * 2 < N - 1 := (Nat.lt_div_iff_mul_lt (show 0 < 2 by norm_num)).mp hMN
      omega
    exact Nat.div_pos (by omega) (lt_of_lt_of_le (by norm_num) hM6)
  have hxle_p0 : x ≤ (p 0 : ℝ) := le_trans (Nat.le_ceil x) (Nat.cast_le.mpr hceil_le)
  have hMge : (x : ℝ) ≤ p 0 := hxle_p0
  have hKsmall : 10 * (N / p 0) ≤ N := by
    have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) h30
    have hKle : ((N / p 0 : ℕ) : ℝ) ≤ (N : ℝ) / x := by
      have hxpos : (0 : ℝ) < x := lt_trans (by norm_num) hx5
      calc
        ((N / p 0 : ℕ) : ℝ) ≤ (N : ℝ) / p 0 := Nat.cast_div_le
        _ ≤ (N : ℝ) / x :=
          div_le_div_of_nonneg_left (by positivity) hxpos hxle_p0
    have : ((N / p 0 : ℕ) : ℝ) ≤ 4 * (N : ℝ) ^ ((1 : ℝ) / 10) := by
      linarith [hKle, N_div_priceX hNpos]
    have : (10 : ℝ) * ↑(N / p 0) ≤ (40 : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 10) := by
      push_cast; linarith
    have : (10 : ℝ) * ↑(N / p 0) ≤ N := le_trans this h40
    exact_mod_cast this
  have hKD : (N / p 0) * (p (999 : Fin 1000) - p 0) ≤ p 0 / 6 := by
    have hsub : p 0 ≤ p (999 : Fin 1000) := hm.monotone (Fin.zero_le _)
    have hD : ((p (999 : Fin 1000) - p 0 : ℕ) : ℝ) ≤ 3000 * Real.log x := by
      rwa [← Nat.cast_sub hsub] at hdiam
    have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) h30
    have hKle : ((N / p 0 : ℕ) : ℝ) ≤ 4 * (N : ℝ) ^ ((1 : ℝ) / 10) := by
      have hxpos : (0 : ℝ) < x := lt_trans (by norm_num) hx5
      calc
        ((N / p 0 : ℕ) : ℝ) ≤ (N : ℝ) / p 0 := Nat.cast_div_le
        _ ≤ (N : ℝ) / x :=
          div_le_div_of_nonneg_left (by positivity) hxpos hxle_p0
        _ = 4 * (N : ℝ) ^ ((1 : ℝ) / 10) := N_div_priceX hNpos
    have hprod :
        ((N / p 0 * (p (999 : Fin 1000) - p 0) : ℕ) : ℝ) ≤
          (12000 : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 10) * Real.log x := by
      push_cast
      calc _ ≤ (4 * (N : ℝ) ^ ((1 : ℝ) / 10)) * (3000 * Real.log x) := by gcongr <;> linarith [hKle, hD]
        _ = (12000 : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 10) * Real.log x := by ring
    have h6 : 6 * (N / p 0 * (p (999 : Fin 1000) - p 0)) ≤ p 0 := by
      have hstep : ((N / p 0 * (p (999 : Fin 1000) - p 0) : ℕ) : ℝ) + 1 ≤ x / 6 :=
        le_trans (by linarith [hprod]) hKDr
      have h6r : (6 : ℝ) * (↑(N / p 0 * (p (999 : Fin 1000) - p 0)) + 1) ≤ p 0 := by
        have : (x / 6 : ℝ) ≤ (p 0 : ℝ) / 6 := by linarith [hMge]
        linarith [hstep, this]
      have hcast : (6 : ℝ) * ↑(N / p 0 * (p (999 : Fin 1000) - p 0)) ≤ p 0 := by linarith [h6r]
      exact_mod_cast hcast
    exact (Nat.le_div_iff_mul_le (show 0 < 6 by norm_num)).2 (by rwa [Nat.mul_comm])
  obtain ⟨R, hRcard, hS⟩ :=
    price_counterexample_of_cluster hp hm hpow hM6 h30 hMN hKpos hKD hKsmall
  exact ⟨p, R, hp, hm, hpow, hRcard, hS⟩

theorem not_universalBound : ¬ UniversalBound :=
  price_implies_not_universal priceTheorem1

end

end Green44Asymp
