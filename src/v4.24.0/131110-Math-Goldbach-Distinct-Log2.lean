import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Size
open Nat
open Finset
open scoped BigOperators

/-!
Theory: Any integer n ≥ 7 can be expressed as a sum of distinct prime numbers
using at most (bitLength n - 2) primes.

The bit-length of n is k where 2^{k-1} ≤ n < 2^k.
The proof shows we need at most k-2 distinct primes to represent n ≥ 7.

Proof structure:
1. For n = 7 to 16, verify by enumeration.
2. For n ≥ 17, use induction with Ramanujan's theorem.
3. When we represent n using prime p and then represent n-p,
   the bit-length decreases by at least 1, so the total number
   of primes in the representation satisfies the bound.
-/

-- Ramanujan's theorem: for n ≥ 17, interval (n/2, n] contains at least three primes
axiom ramanujan_theorem (n : ℕ) (h : n ≥ 17) : 3 ≤ ((Ioc (n / 2) n).filter Nat.Prime).card

-- Helper: bit-length of n (number of bits in binary representation)
-- For n > 0, this is the smallest k such that n < 2^k
def bitLength (n : ℕ) : ℕ := Nat.size n

-- Theorem: For n ≥ 7, n can be represented as sum of distinct primes
-- using at most (bitLength n - 2) primes
theorem sum_of_distinct_primes_bounded (n : ℕ) (h : n ≥ 7) :
    ∃ (s : Finset ℕ), (∀ x ∈ s, Nat.Prime x) ∧ ∑ x ∈ s, x = n ∧ s.card ≤ bitLength n - 2 := by
  -- Base cases: n = 7 to 16 (verifiable by enumeration)
  have base_cases : ∀ n, 7 ≤ n → n ≤ 16 →
      ∃ (s : Finset ℕ), (∀ x ∈ s, Nat.Prime x) ∧ ∑ x ∈ s, x = n ∧ s.card ≤ bitLength n - 2 := by
    intro n hn_low hn_high
    have : n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨ n = 15 ∨ n = 16 := by
      omega
    rcases this with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    -- n = 7: bitLength = 3, need ≤ 1 prime
    · refine ⟨{7}, ?_, ?_, ?_⟩
      · intro x hx; simp at hx; subst x; decide
      · simp
      · simp only [bitLength, Finset.card_singleton]
        have h1 : 7 < 2^3 := by norm_num
        have h2 : 2^2 ≤ 7 := by norm_num
        have : Nat.size 7 = 3 := by
          apply le_antisymm
          · exact Nat.size_le.mpr h1
          · exact Nat.lt_size.mpr h2
        omega
    -- n = 8: bitLength = 4, need ≤ 2 primes
    · refine ⟨{3, 5}, ?_, ?_, ?_⟩
      · intro x hx; simp [Finset.mem_insert, Finset.mem_singleton] at hx;
        rcases hx with (rfl|rfl) <;> decide
      · norm_num
      · simp only [bitLength]
        have h1 : 8 < 2^4 := by norm_num
        have h2 : 2^3 ≤ 8 := by norm_num
        have : Nat.size 8 = 4 := by
          apply le_antisymm
          · exact Nat.size_le.mpr h1
          · exact Nat.lt_size.mpr h2
        rw [this]
        norm_num
    -- n = 9: bitLength = 4, need ≤ 2 primes
    · refine ⟨{2, 7}, ?_, ?_, ?_⟩
      · intro x hx; simp [Finset.mem_insert, Finset.mem_singleton] at hx;
        rcases hx with (rfl|rfl) <;> decide
      · norm_num
      · simp only [bitLength]
        have h1 : 9 < 2^4 := by norm_num
        have h2 : 2^3 ≤ 9 := by norm_num
        have : Nat.size 9 = 4 := by
          apply le_antisymm
          · exact Nat.size_le.mpr h1
          · exact Nat.lt_size.mpr h2
        rw [this]
        norm_num
    -- n = 10: bitLength = 4, need ≤ 2 primes
    · refine ⟨{3, 7}, ?_, ?_, ?_⟩
      · intro x hx; simp [Finset.mem_insert, Finset.mem_singleton] at hx;
        rcases hx with (rfl|rfl) <;> decide
      · norm_num
      · simp only [bitLength]
        have h1 : 10 < 2^4 := by norm_num
        have h2 : 2^3 ≤ 10 := by norm_num
        have : Nat.size 10 = 4 := by
          apply le_antisymm
          · exact Nat.size_le.mpr h1
          · exact Nat.lt_size.mpr h2
        rw [this]
        norm_num
    -- n = 11: bitLength = 4, need ≤ 2 primes
    · refine ⟨{11}, ?_, ?_, ?_⟩
      · intro x hx; simp at hx; subst x; decide
      · norm_num
      · simp only [bitLength, Finset.card_singleton]
        have h1 : 11 < 2^4 := by norm_num
        have h2 : 2^3 ≤ 11 := by norm_num
        have : Nat.size 11 = 4 := by
          apply le_antisymm
          · exact Nat.size_le.mpr h1
          · exact Nat.lt_size.mpr h2
        omega
    -- n = 12: bitLength = 4, need ≤ 2 primes
    · refine ⟨{5, 7}, ?_, ?_, ?_⟩
      · intro x hx; simp [Finset.mem_insert, Finset.mem_singleton] at hx;
        rcases hx with (rfl|rfl) <;> decide
      · norm_num
      · simp only [bitLength]
        have h1 : 12 < 2^4 := by norm_num
        have h2 : 2^3 ≤ 12 := by norm_num
        have : Nat.size 12 = 4 := by
          apply le_antisymm
          · exact Nat.size_le.mpr h1
          · exact Nat.lt_size.mpr h2
        rw [this]
        norm_num
    -- n = 13: bitLength = 4, need ≤ 2 primes
    · refine ⟨{13}, ?_, ?_, ?_⟩
      · intro x hx; simp at hx; subst x; decide
      · norm_num
      · simp only [bitLength, Finset.card_singleton]
        have h1 : 13 < 2^4 := by norm_num
        have h2 : 2^3 ≤ 13 := by norm_num
        have : Nat.size 13 = 4 := by
          apply le_antisymm
          · exact Nat.size_le.mpr h1
          · exact Nat.lt_size.mpr h2
        omega
    -- n = 14: bitLength = 4, need ≤ 2 primes
    · refine ⟨{3, 11}, ?_, ?_, ?_⟩
      · intro x hx; simp [Finset.mem_insert, Finset.mem_singleton] at hx;
        rcases hx with (rfl|rfl) <;> decide
      · norm_num
      · simp only [bitLength]
        have h1 : 14 < 2^4 := by norm_num
        have h2 : 2^3 ≤ 14 := by norm_num
        have : Nat.size 14 = 4 := by
          apply le_antisymm
          · exact Nat.size_le.mpr h1
          · exact Nat.lt_size.mpr h2
        rw [this]
        norm_num
    -- n = 15: bitLength = 4, need ≤ 2 primes
    · refine ⟨{2, 13}, ?_, ?_, ?_⟩
      · intro x hx; simp [Finset.mem_insert, Finset.mem_singleton] at hx;
        rcases hx with (rfl|rfl) <;> decide
      · norm_num
      · simp only [bitLength]
        have h1 : 15 < 2^4 := by norm_num
        have h2 : 2^3 ≤ 15 := by norm_num
        have : Nat.size 15 = 4 := by
          apply le_antisymm
          · exact Nat.size_le.mpr h1
          · exact Nat.lt_size.mpr h2
        rw [this]
        norm_num
    -- n = 16: bitLength = 5, need ≤ 3 primes
    · refine ⟨{3, 13}, ?_, ?_, ?_⟩
      · intro x hx; simp [Finset.mem_insert, Finset.mem_singleton] at hx;
        rcases hx with (rfl|rfl) <;> decide
      · norm_num
      · simp only [bitLength]
        have h1 : 16 < 2^5 := by norm_num
        have h2 : 2^4 ≤ 16 := by norm_num
        have : Nat.size 16 = 5 := by
          apply le_antisymm
          · exact Nat.size_le.mpr h1
          · exact Nat.lt_size.mpr h2
        rw [this]
        norm_num

  -- If n ≤ 16, use base cases
  by_cases h16 : n ≤ 16
  · exact base_cases n h h16

  -- For n ≥ 17, use strong induction
  have h17 : n ≥ 17 := by omega
  refine Nat.strong_induction_on n (λ m ih hm => ?_) h
  by_cases hm16 : m ≤ 16
  · exact base_cases m (by omega) hm16
  have h17m : m ≥ 17 := by omega

  -- Apply Ramanujan's theorem
  have hram : 3 ≤ ((Ioc (m / 2) m).filter Nat.Prime).card := ramanujan_theorem m h17m

  -- Check simple cases where m can be represented with 1 or 2 primes
  by_cases hm_prime : Nat.Prime m
  · -- Case 1: m itself is prime (1 prime)
    refine ⟨{m}, λ x hx => ?_, ?_, ?_⟩
    · simp at hx; subst x; exact hm_prime
    · simp
    · simp [bitLength, Finset.card_singleton]
      have h16_size : Nat.size 16 = 5 := by
        apply le_antisymm
        · exact Nat.size_le.mpr (by norm_num : 16 < 2^5)
        · exact Nat.lt_size.mpr (by norm_num : 2^4 ≤ 16)
      have : Nat.size m ≥ 5 := by
        calc Nat.size m ≥ Nat.size 16 := Nat.size_le_size (by omega : 16 ≤ m)
          _ = 5 := h16_size
      omega
  by_cases hm2 : Nat.Prime (m - 2)
  · -- Case 2: m-2 is prime, then m = (m-2) + 2 (2 primes)
    refine ⟨{m-2, 2}, ?_, ?_, ?_⟩
    · intro x hx
      simp [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with (rfl|rfl)
      · exact hm2
      · decide
    · have h : (m - 2 : ℕ) ≠ 2 := by omega
      have h2 : m - 2 ∉ ({2} : Finset ℕ) := by simp [h]
      rw [show ({m - 2, 2} : Finset ℕ) = insert (m - 2) {2} by rfl]
      rw [sum_insert h2, sum_singleton]
      omega
    · simp only [bitLength]
      have h_neq : m - 2 ≠ 2 := by omega
      have h_card : ({m-2, 2} : Finset ℕ).card = 2 := by
        rw [show ({m - 2, 2} : Finset ℕ) = insert (m - 2) {2} by rfl]
        rw [Finset.card_insert_of_notMem (by simp [h_neq])]
        norm_num
      rw [h_card]
      have h16_size : Nat.size 16 = 5 := by
        apply le_antisymm
        · exact Nat.size_le.mpr (by norm_num : 16 < 2^5)
        · exact Nat.lt_size.mpr (by norm_num : 2^4 ≤ 16)
      have : Nat.size m ≥ 5 := by
        calc Nat.size m ≥ Nat.size 16 := Nat.size_le_size (by omega : 16 ≤ m)
          _ = 5 := h16_size
      omega
  by_cases hm3 : Nat.Prime (m - 3)
  · -- Case 3: m-3 is prime, then m = (m-3) + 3 (2 primes)
    refine ⟨{m-3, 3}, ?_, ?_, ?_⟩
    · intro x hx
      simp [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with (rfl|rfl)
      · exact hm3
      · decide
    · have h : (m - 3 : ℕ) ≠ 3 := by omega
      have h2 : m - 3 ∉ ({3} : Finset ℕ) := by simp [h]
      rw [show ({m - 3, 3} : Finset ℕ) = insert (m - 3) {3} by rfl]
      rw [sum_insert h2, sum_singleton]
      omega
    · simp only [bitLength]
      have h_neq : m - 3 ≠ 3 := by omega
      have h_card : ({m-3, 3} : Finset ℕ).card = 2 := by
        rw [show ({m - 3, 3} : Finset ℕ) = insert (m - 3) {3} by rfl]
        rw [Finset.card_insert_of_notMem (by simp [h_neq])]
        norm_num
      rw [h_card]
      have h16_size : Nat.size 16 = 5 := by
        apply le_antisymm
        · exact Nat.size_le.mpr (by norm_num : 16 < 2^5)
        · exact Nat.lt_size.mpr (by norm_num : 2^4 ≤ 16)
      have : Nat.size m ≥ 5 := by
        calc Nat.size m ≥ Nat.size 16 := Nat.size_le_size (by omega : 16 ≤ m)
          _ = 5 := h16_size
      omega
  by_cases hm5 : Nat.Prime (m - 5)
  · -- Case 4: m-5 is prime, then m = (m-5) + 5 (2 primes)
    refine ⟨{m-5, 5}, ?_, ?_, ?_⟩
    · intro x hx
      simp [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with (rfl|rfl)
      · exact hm5
      · decide
    · have h : (m - 5 : ℕ) ≠ 5 := by omega
      have h2 : m - 5 ∉ ({5} : Finset ℕ) := by simp [h]
      rw [show ({m - 5, 5} : Finset ℕ) = insert (m - 5) {5} by rfl]
      rw [sum_insert h2, sum_singleton]
      omega
    · simp only [bitLength]
      have h_neq : m - 5 ≠ 5 := by omega
      have h_card : ({m-5, 5} : Finset ℕ).card = 2 := by
        rw [show ({m - 5, 5} : Finset ℕ) = insert (m - 5) {5} by rfl]
        rw [Finset.card_insert_of_notMem (by simp [h_neq])]
        norm_num
      rw [h_card]
      have h16_size : Nat.size 16 = 5 := by
        apply le_antisymm
        · exact Nat.size_le.mpr (by norm_num : 16 < 2^5)
        · exact Nat.lt_size.mpr (by norm_num : 2^4 ≤ 16)
      have : Nat.size m ≥ 5 := by
        calc Nat.size m ≥ Nat.size 16 := Nat.size_le_size (by omega : 16 ≤ m)
          _ = 5 := h16_size
      omega
  -- Main case: none of m, m-2, m-3, m-5 is prime
  let S := (Ioc (m / 2) m).filter Nat.Prime
  have hS_card : 3 ≤ S.card := hram

  -- The primes in S are all > m/2
  have hS_lower : ∀ p ∈ S, m / 2 < p := by
    intro p hp
    simp [S, Finset.mem_filter, Finset.mem_Ioc] at hp
    exact hp.1.1

  -- Consider the set T = {m-6, m-4, m-1} ∩ S
  -- Since |S| ≥ 3, if |T| ≤ 2, then there exists p ∈ S \ T
  let T : Finset ℕ := {m-6, m-4, m-1}
  have hT_card : T.card = 3 := by
    have h1 : m - 6 ≠ m - 4 := by omega
    have h2 : m - 6 ≠ m - 1 := by omega
    have h3 : m - 4 ≠ m - 1 := by omega
    rw [show T = insert (m-6) {m-4, m-1} by rfl]
    rw [Finset.card_insert_of_notMem (by simp [h1, h2])]
    rw [show ({m-4, m-1} : Finset ℕ) = insert (m-4) {m-1} by rfl]
    rw [Finset.card_insert_of_notMem (by simp [h3])]
    simp

  by_cases hT_full : S ⊆ T
  · -- If S ⊆ T, then |S| ≤ |T| = 3, but |S| ≥ 3, so |S| = 3 and S = T
      have hS_eq_T : S = T := by
        apply Finset.eq_of_subset_of_card_le hT_full
        rw [hT_card]
        omega
      -- But then m-1, m-4, m-6 are all prime
      have h1 : Nat.Prime (m - 1) := by
        have : m - 1 ∈ S := by
          rw [hS_eq_T]
          simp [T]
        simp [S, Finset.mem_filter] at this
        exact this.2
      have h4 : Nat.Prime (m - 4) := by
        have : m - 4 ∈ S := by
          rw [hS_eq_T]
          simp [T]
        simp [S, Finset.mem_filter] at this
        exact this.2
      have h6 : Nat.Prime (m - 6) := by
        have : m - 6 ∈ S := by
          rw [hS_eq_T]
          simp [T]
        simp [S, Finset.mem_filter] at this
        exact this.2
      -- Check if m-1 and m-4 can both be prime (they can't both be >2 and odd)
      have h1_ne2 : m - 1 ≠ 2 := by omega
      have h4_ne2 : m - 4 ≠ 2 := by omega
      have h1_odd : (m - 1) % 2 = 1 :=
        (Nat.Prime.eq_two_or_odd h1).resolve_left h1_ne2
      have h4_odd : (m - 4) % 2 = 1 :=
        (Nat.Prime.eq_two_or_odd h4).resolve_left h4_ne2
      -- m-1 odd ⇒ m even, but m-4 = m-4 should then be even, contradiction
      have : (m - 4) % 2 = 0 := by
        have : m % 2 = 0 := by omega
        omega
      omega

  · -- S ⊈ T, so there exists p ∈ S \ T
    rcases Finset.not_subset.mp hT_full with ⟨p, hpS, hpT⟩
    have hp_prime : Nat.Prime p := by
      simp [S, Finset.mem_filter] at hpS
      exact hpS.2
    have hp_bounds : m / 2 < p ∧ p ≤ m := by
      simp [S, Finset.mem_filter, Finset.mem_Ioc] at hpS
      exact ⟨hpS.1.1, hpS.1.2⟩

    -- p is not m-1, m-4, or m-6
    have hp_ne : p ∉ ({m-1, m-4, m-6} : Finset ℕ) := by
      intro h
      apply hpT
      simp [T] at h ⊢
      tauto

    -- Since p > m/2 and p ∉ {m-1, m-4, m-6}, we must have p ≤ m-7
    have hp_le : p ≤ m - 7 := by
      by_contra! H  -- Assume p > m-7
      have h_ge : p ≥ m - 6 := by omega
      have h_le : p ≤ m := hp_bounds.2
      -- Then p must be one of m-6, m-5, m-4, m-3, m-2, m-1
      have h_range : m - 6 ≤ p ∧ p ≤ m := ⟨h_ge, h_le⟩
      have : p = m-6 ∨ p = m-5 ∨ p = m-4 ∨ p = m-3 ∨ p = m-2 ∨ p = m-1 ∨ p = m := by
        have : m ≥ 17 := h17m
        omega
      rcases this with (rfl|rfl|rfl|rfl|rfl|rfl|rfl)
      · apply hpT; simp [T]
      · exact hm5 hp_prime
      · apply hpT; simp [T]
      · exact hm3 hp_prime
      · exact hm2 hp_prime
      · apply hpT; simp [T]
      · exact hm_prime hp_prime

    -- Now m-p ≥ 7 and m-p < m
    set k := m - p with hk_def
    have hk_ge7 : k ≥ 7 := by
      dsimp [k]
      omega
    have hk_lt_m : k < m := by
      dsimp [k]
      have : p > 0 := Nat.Prime.pos hp_prime
      omega

    -- Apply induction hypothesis to k
    rcases ih k hk_lt_m hk_ge7 with ⟨s, hs_prime, hs_sum, hs_card⟩

    -- Key lemma: bitLength k ≤ bitLength m - 1
    -- Since p > m/2, we have k = m - p < m/2
    have hk_half : k < m / 2 + 1 := by
      have : p > m / 2 := hp_bounds.1
      omega
    have h_bitlen : bitLength k ≤ bitLength m - 1 := by
      unfold bitLength
      -- Since k < m/2 + 1 and m ≥ 17, we have k ≤ m/2 < m
      -- For m ≥ 17: if m.size = s, then 2^(s-1) ≤ m < 2^s
      -- Since k < m/2 + 1 ≤ m/2 + 1 < 2^(s-1), we have k.size ≤ s-1
      have hm_ge : m ≥ 17 := h17m
      have : k < m / 2 + 1 := hk_half
      -- For m ≥ 17, m.size ≥ 5, so 2^4 ≤ m
      -- k < m/2 + 1 ≤ (m+1)/2 < m
      -- More directly: k ≤ m - 7 (from hp_le and k = m - p, p ≥ 7)
      have hk_bound : k ≤ m - 7 := by
        dsimp [k]
        omega
      -- Since k < m, we have k.size ≤ m.size. Since k = m - p and p ≥ 7, we have k ≤ m - 7
      -- For m ≥ 17, we can show k.size ≤ m.size - 1
      have : Nat.size k ≤ Nat.size m - 1 := by
        have hsize_k : Nat.size k ≤ Nat.size m := Nat.size_le_size (by omega : k ≤ m)
        -- If k.size = m.size, then they have the same bit-length, but k < m/2 + 1
        by_cases heq : Nat.size k = Nat.size m
        · -- If k and m have the same size, then 2^(s-1) ≤ k, m < 2^s
          -- But k < m/2 + 1, so 2^(s-1) ≤ k < m/2 + 1
          -- Also 2^(s-1) ≤ m < 2^s, which means m/2 < 2^(s-1)
          -- This gives 2^(s-1) < m/2 + 1, contradiction
          exfalso
          -- If k and m have the same size s, then 2^(s-1) ≤ k, m < 2^s
          -- From Nat.lt_size: m < s ↔ 2^m ≤ n, so s-1 < s gives 2^(s-1) ≤ k
          have hk_pow : 2^(Nat.size k - 1) ≤ k := by
            have : Nat.size k - 1 < Nat.size k := by
              have : k ≥ 7 := hk_ge7
              have : Nat.size k ≥ 3 := by
                have : Nat.size 7 ≤ Nat.size k := Nat.size_le_size (by omega : 7 ≤ k)
                have : Nat.size 7 = 3 := by
                  apply le_antisymm <;> [exact Nat.size_le.mpr (by norm_num : 7 < 2^3); exact Nat.lt_size.mpr (by norm_num : 2^2 ≤ 7)]
                omega
              omega
            exact Nat.lt_size.mp this
          have hm_pow : 2^(Nat.size m - 1) ≤ m := by
            have : Nat.size m - 1 < Nat.size m := by
              have : m ≥ 17 := h17m
              have : Nat.size m ≥ 5 := by
                have : Nat.size 16 = 5 := by
                  apply le_antisymm <;> [exact Nat.size_le.mpr (by norm_num : 16 < 2^5); exact Nat.lt_size.mpr (by norm_num : 2^4 ≤ 16)]
                calc Nat.size m ≥ Nat.size 16 := Nat.size_le_size (by omega : 16 ≤ m)
                  _ = 5 := this
              omega
            exact Nat.lt_size.mp this
          rw [heq] at hk_pow
          have : k < m / 2 + 1 := hk_half
          -- Now we have 2^(m.size - 1) ≤ k < m/2 + 1 and 2^(m.size - 1) ≤ m
          -- This means 2^(m.size - 1) < m/2 + 1
          -- But m < 2^(m.size), so m/2 < 2^(m.size - 1)
          -- Therefore 2^(m.size - 1) < m/2 + 1 < 2^(m.size - 1) + 1, contradiction
          have : m < 2^(Nat.size m) := Nat.lt_size_self m
          have : 2^(Nat.size m - 1) < m / 2 + 1 := by omega
          have : 2 * 2^(Nat.size m - 1) < m + 2 := by omega
          -- We have 2^(m.size-1) ≤ k and k < m/2 + 1, so 2^(m.size-1) < m/2 + 1
          -- This means 2^(m.size-1) ≤ m/2 (rounding down)
          -- But m < 2^(m.size) = 2 * 2^(m.size-1), so m/2 < 2^(m.size-1)
          -- Contradiction!
          have h1 : 2^(Nat.size m - 1) < m / 2 + 1 := by omega  -- from above
          have h2 : m < 2^(Nat.size m) := Nat.lt_size_self m
          -- For m.size ≥ 5, we have 2^(m.size) = 2 * 2^(m.size - 1)
          have h3 : m < 2 * 2^(Nat.size m - 1) := by
            have : Nat.size m ≥ 5 := by
              have : Nat.size 16 = 5 := by
                apply le_antisymm <;> [exact Nat.size_le.mpr (by norm_num : 16 < 2^5); exact Nat.lt_size.mpr (by norm_num : 2^4 ≤ 16)]
              calc Nat.size m ≥ Nat.size 16 := Nat.size_le_size (by omega : 16 ≤ m)
                _ = 5 := this
            calc m < 2^(Nat.size m) := h2
              _ = 2 * 2^(Nat.size m - 1) := by
                rw [← Nat.pow_succ']
                simp
                omega
          -- So m/2 < 2^(m.size - 1), but 2^(m.size - 1) < m/2 + 1
          have : m / 2 < 2^(Nat.size m - 1) := by omega
          have : 2^(Nat.size m - 1) ≤ m / 2 := by omega
          omega
        · omega
      omega

    -- p is not in s since all elements of s are ≤ k < p
    have hp_notin_s : p ∉ s := by
      intro h
      have : p ≤ ∑ x ∈ s, x := by
        calc p = ∑ y ∈ {p}, y := by simp
          _ ≤ ∑ y ∈ s, y := sum_le_sum_of_subset_of_nonneg (singleton_subset_iff.mpr h) (fun _ _ _ => Nat.zero_le _)
      rw [hs_sum] at this
      omega

    -- Construct representation for m
    refine ⟨insert p s, ?_, ?_, ?_⟩
    · intro x hx
      simp [Finset.mem_insert] at hx
      rcases hx with (rfl|hx)
      · exact hp_prime
      · exact hs_prime x hx
    · rw [sum_insert hp_notin_s, hs_sum]
      omega
    · rw [card_insert_of_notMem hp_notin_s]
      -- We need to show: s.card + 1 ≤ bitLength m - 2
      -- From hs_card: s.card ≤ bitLength k - 2
      -- From h_bitlen: bitLength k ≤ bitLength m - 1
      -- Therefore: s.card + 1 ≤ (bitLength k - 2) + 1 ≤ bitLength k - 1 ≤ (bitLength m - 1) - 1 = bitLength m - 2
      have hm_size : bitLength m ≥ 5 := by
        unfold bitLength
        have h16_size : Nat.size 16 = 5 := by
          apply le_antisymm
          · exact Nat.size_le.mpr (by norm_num : 16 < 2^5)
          · exact Nat.lt_size.mpr (by norm_num : 2^4 ≤ 16)
        calc Nat.size m ≥ Nat.size 16 := Nat.size_le_size (by omega : 16 ≤ m)
          _ = 5 := h16_size
      have hk_size : bitLength k ≥ 3 := by
        unfold bitLength
        have h4_size : Nat.size 4 = 3 := by
          apply le_antisymm
          · exact Nat.size_le.mpr (by norm_num : 4 < 2^3)
          · exact Nat.lt_size.mpr (by norm_num : 2^2 ≤ 4)
        calc Nat.size k ≥ Nat.size 4 := Nat.size_le_size (by omega : 4 ≤ k)
          _ = 3 := h4_size
      omega

#check sum_of_distinct_primes_bounded
