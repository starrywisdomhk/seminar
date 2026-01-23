-- Theorem.lean
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
open Nat
open Finset
open scoped BigOperators

/-!
The idea:
Any integer n >= 7 can be expressed as a sum of distinct prime numbers
(where a single prime by itself also counts as a valid representation).
The proof relies on Ramanujan's 1919 theorem: For any n >= 17,
there are at least three prime numbers in the interval (n/2, n].
For numbers 7 through 16, the result can be verified by enumeration. For n >= 17,
mathematical induction is used,
applying Ramanujan's theorem which guarantees at least three primes in (n/2, n].
If one of n, n-2, n-3, n-5 is prime, then n is already accounted for.
Otherwise, among n-1, n-4, n-6, there are at most two primes,
meaning there must exist a prime p <= n-7.
Mathematical induction can then be applied to n-p.

# WARNING: This following LEAN proof(the code) has NOT been carefully reviewed or verified.
The above English proof is from the seminar "discuss Goldbach with AI" 
and deepseek generated the lean proof based on the English proof.

This file contains a proof that every natural number n ≥ 7 can be expressed
as a sum of distinct primes. However, please note:

* This proof **relies entirely on `ramanujan_theorem` being true**, which is
  currently declared as an **AXIOM** (unproven assumption).
* The axiom states: for n ≥ 17, the interval (n/2, n] contains at least
  three primes.
* **If this axiom is false, the entire proof is unsound.**

* The code has NOT been thoroughly proofread or peer-reviewed
* Individual lemmas and proof steps may contain errors
* The base cases (n = 7 to 16) should be independently verified
* The inductive construction needs careful review

# To make this rigorous:
1. Replace the `axiom ramanujan_theorem` with an actual proof, OR
2. Find a reference to a verified proof of Ramanujan's theorem in Mathlib
3. Carefully review all proof steps for correctness
4. Verify all base cases are correct

**Do not treat this as established truth without independent verification!**
-/

-- Ramanujan's theorem: for n ≥ 17, interval (n/2, n] contains at least three primes
axiom ramanujan_theorem (n : ℕ) (h : n ≥ 17) : 3 ≤ ((Ioc (n / 2) n).filter Nat.Prime).card

-- Definition: "can be expressed as sum of distinct primes"
def SumOfDistinctPrimes (n : ℕ) : Prop :=
  ∃ (s : Finset ℕ), (∀ x ∈ s, Nat.Prime x) ∧ ∑ x ∈ s, x = n

-- Base case: n = 7 to 16
lemma base_case (n : ℕ) (hn : n ≥ 7) (hn' : n ≤ 16) : SumOfDistinctPrimes n := by
  have : n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨ n = 15 ∨ n = 16 := by
    omega
  rcases this with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · refine ⟨{7}, ?_, ?_⟩
    · intro x hx
      simp [Finset.mem_singleton] at hx
      rw [hx]
      exact by decide
    · simp
  · refine ⟨{3,5}, ?_, ?_⟩
    · intro x hx
      simp [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with (rfl|rfl)
      · exact by decide
      · exact by decide
    · simp
  · refine ⟨{2,7}, ?_, ?_⟩
    · intro x hx
      simp [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with (rfl|rfl)
      · exact by decide
      · exact by decide
    · simp
  · refine ⟨{2,3,5}, ?_, ?_⟩
    · intro x hx
      simp [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with (rfl|rfl|rfl)
      · exact by decide
      · exact by decide
      · exact by decide
    · simp
  · refine ⟨{11}, ?_, ?_⟩
    · intro x hx
      simp [Finset.mem_singleton] at hx
      rw [hx]
      exact by decide
    · simp
  · refine ⟨{5,7}, ?_, ?_⟩
    · intro x hx
      simp [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with (rfl|rfl)
      · exact by decide
      · exact by decide
    · simp
  · refine ⟨{13}, ?_, ?_⟩
    · intro x hx
      simp [Finset.mem_singleton] at hx
      rw [hx]
      exact by decide
    · simp
  · refine ⟨{2,5,7}, ?_, ?_⟩
    · intro x hx
      simp [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with (rfl|rfl|rfl)
      · exact by decide
      · exact by decide
      · exact by decide
    · simp
  · refine ⟨{2,13}, ?_, ?_⟩
    · intro x hx
      simp [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with (rfl|rfl)
      · exact by decide
      · exact by decide
    · simp
  · refine ⟨{3,13}, ?_, ?_⟩
    · intro x hx
      simp [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with (rfl|rfl)
      · exact by decide
      · exact by decide
    · simp

-- Main theorem
theorem sum_of_distinct_primes (n : ℕ) (h : n ≥ 7) : SumOfDistinctPrimes n := by
  refine Nat.strong_induction_on n ?_ h
  intro m ih hm
  by_cases hm' : m < 17
  · have : m ≤ 16 := by omega
    exact base_case m hm this
  · have h17 : m ≥ 17 := by omega
    have hram : 3 ≤ ((Ioc (m / 2) m).filter Nat.Prime).card := ramanujan_theorem m h17

    -- Check if m, m-2, m-3, or m-5 is prime
    by_cases hm1 : Nat.Prime m
    · refine ⟨{m}, ?_, ?_⟩
      · intro x hx
        simp at hx
        subst x
        exact hm1
      · simp
    by_cases hm2 : Nat.Prime (m - 2)
    · refine ⟨{m - 2, 2}, ?_, ?_⟩
      · intro x hx
        simp [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with (rfl|rfl)
        · exact hm2
        · exact by decide
      · have : ∑ x ∈ ({m - 2, 2} : Finset ℕ), x = m := by
          have h : (m - 2 : ℕ) ≠ 2 := by omega
          have h2 : m - 2 ∉ ({2} : Finset ℕ) := by simp [h]
          rw [show ({m - 2, 2} : Finset ℕ) = insert (m - 2) {2} by rfl]
          rw [sum_insert h2, sum_singleton]
          omega
        exact this
    by_cases hm3 : Nat.Prime (m - 3)
    · refine ⟨{m - 3, 3}, ?_, ?_⟩
      · intro x hx
        simp [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with (rfl|rfl)
        · exact hm3
        · exact by decide
      · have : ∑ x ∈ ({m - 3, 3} : Finset ℕ), x = m := by
          have h : (m - 3 : ℕ) ≠ 3 := by omega
          have h2 : m - 3 ∉ ({3} : Finset ℕ) := by simp [h]
          rw [show ({m - 3, 3} : Finset ℕ) = insert (m - 3) {3} by rfl]
          rw [sum_insert h2, sum_singleton]
          omega
        exact this
    by_cases hm5 : Nat.Prime (m - 5)
    · refine ⟨{m - 5, 5}, ?_, ?_⟩
      · intro x hx
        simp [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with (rfl|rfl)
        · exact hm5
        · exact by decide
      · have : ∑ x ∈ ({m - 5, 5} : Finset ℕ), x = m := by
          have h : (m - 5 : ℕ) ≠ 5 := by omega
          have h2 : m - 5 ∉ ({5} : Finset ℕ) := by simp [h]
          rw [show ({m - 5, 5} : Finset ℕ) = insert (m - 5) {5} by rfl]
          rw [sum_insert h2, sum_singleton]
          omega
        exact this

    -- Now m, m-2, m-3, m-5 are not prime
    have h_not_both : ¬ (Nat.Prime (m - 1) ∧ Nat.Prime (m - 4)) := by
      rintro ⟨hp1, hp4⟩
      -- Both m-1 and m-4 are odd (since m ≥ 17, neither can be 2)
      have h1_ne2 : m - 1 ≠ 2 := by omega
      have h4_ne2 : m - 4 ≠ 2 := by omega
      have h1 : (m - 1) % 2 = 1 := (Nat.Prime.eq_two_or_odd hp1).resolve_left h1_ne2
      have h4 : (m - 4) % 2 = 1 := (Nat.Prime.eq_two_or_odd hp4).resolve_left h4_ne2
      -- m-1 odd implies m even
      have h_even : m % 2 = 0 := by omega
      -- But m even and m-4 = m - 4 implies m-4 is even
      have : (m - 4) % 2 = 0 := by omega
      -- Contradiction with h4
      omega

    let S : Finset ℕ := Ioc (m / 2) m
    have hS : 3 ≤ (S.filter Nat.Prime).card := hram

    -- The set {m-6, m-4, m-1} is contained in S
    have hT : {m - 6, m - 4, m - 1} ⊆ S := by
      intro x hx
      simp [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with (rfl|rfl|rfl)
      · simp [S, Finset.mem_Ioc]; omega
      · simp [S, Finset.mem_Ioc]; omega
      · simp [S, Finset.mem_Ioc]; omega

    -- There exists prime p ∈ S such that p ∉ {m-6, m-4, m-1}
    have h_nonempty : ∃ p, p ∈ S.filter Nat.Prime ∧ p ∉ ({m - 6, m - 4, m - 1} : Finset ℕ) := by
      by_contra! H  -- H: ∀ p, p ∈ S.filter Nat.Prime → p ∈ {m-6, m-4, m-1}
      have : S.filter Nat.Prime ⊆ {m - 6, m - 4, m - 1} := H
      have card_le : (S.filter Nat.Prime).card ≤ ({m - 6, m - 4, m - 1} : Finset ℕ).card :=
        Finset.card_le_card this
      -- The set {m-6, m-4, m-1} has exactly 3 distinct elements since m ≥ 17
      have card_eq_3 : ({m - 6, m - 4, m - 1} : Finset ℕ).card = 3 := by
        have h1 : m - 6 ≠ m - 4 := by omega
        have h2 : m - 6 ≠ m - 1 := by omega
        have h3 : m - 4 ≠ m - 1 := by omega
        simp [h1, h2, h3]
      -- If all primes in S are from {m-6, m-4, m-1}, and we have ≥3 primes,
      -- then all three elements must be prime
      have card_S_eq_3 : (S.filter Nat.Prime).card = 3 := by
        rw [card_eq_3] at card_le
        omega
      -- Since S.filter ⊆ {m-6, m-4, m-1} and they have equal cardinality, they're equal
      have sets_eq : S.filter Nat.Prime = {m - 6, m - 4, m - 1} := by
        apply Finset.eq_of_subset_of_card_le this
        rw [card_S_eq_3, card_eq_3]
      -- This means m-1, m-4, and m-6 are all prime
      have all_prime : Nat.Prime (m - 1) ∧ Nat.Prime (m - 4) := by
        have : ∀ x ∈ ({m - 6, m - 4, m - 1} : Finset ℕ), Nat.Prime x := by
          intro x hx
          rw [← sets_eq] at hx
          simp [Finset.mem_filter] at hx
          exact hx.2
        simp at this
        exact ⟨this.2.2, this.2.1⟩
      exact h_not_both all_prime

    rcases h_nonempty with ⟨p, hp, hp'⟩
    have hp_prime : Nat.Prime p := by
      simp [Finset.mem_filter] at hp
      exact hp.2
    have hp_mem : p ∈ S := by
      simp [Finset.mem_filter] at hp
      exact hp.1
    rcases Finset.mem_Ioc.1 hp_mem with ⟨hp_left, hp_right⟩
    have p_lt_m : p < m := by
      by_contra! H  -- H: p ≥ m
      have : p = m := by omega
      subst this
      exact hm1 hp_prime

    -- p is not m-2, m-3, m-5, m-6
    have ne1 : p ≠ m - 2 := by
      intro H
      have : Nat.Prime (m - 2) := by rw [← H]; exact hp_prime
      exact hm2 this
    have ne2 : p ≠ m - 3 := by
      intro H
      have : Nat.Prime (m - 3) := by rw [← H]; exact hp_prime
      exact hm3 this
    have ne3 : p ≠ m - 5 := by
      intro H
      have : Nat.Prime (m - 5) := by rw [← H]; exact hp_prime
      exact hm5 this
    have p_ne_m6 : p ≠ m - 6 := by
      intro H
      have : p ∈ ({m - 6, m - 4, m - 1} : Finset ℕ) := by
        simp [H]
      exact hp' this

    -- p ≤ m-6
    have p_le_m6 : p ≤ m - 6 := by
      by_contra! H  -- H: p > m-6
      have : p ≥ m - 5 := by omega
      have : p = m - 5 ∨ p = m - 4 ∨ p = m - 3 ∨ p = m - 2 ∨ p = m - 1 := by omega
      rcases this with (rfl|rfl|rfl|rfl|rfl)
      · exact ne3 rfl
      · have : m - 4 ∈ ({m - 6, m - 4, m - 1} : Finset ℕ) := by
          simp [Finset.mem_insert, Finset.mem_singleton]
        exact hp' this
      · exact ne2 rfl
      · exact ne1 rfl
      · have : m - 1 ∈ ({m - 6, m - 4, m - 1} : Finset ℕ) := by
          simp [Finset.mem_insert, Finset.mem_singleton]
        exact hp' this

    -- p ≤ m-7
    have p_le_m7 : p ≤ m - 7 := by
      by_contra! H  -- H: p > m-7
      have : p ≥ m - 6 := by omega
      have : p = m - 6 := by omega
      exact p_ne_m6 this

    set k := m - p with hk_def
    have hk_ge : k ≥ 7 := by
      dsimp [k]
      omega
    have hk_lt : k < m := by
      dsimp [k]
      have : p > 0 := Nat.Prime.pos hp_prime
      omega

    -- Apply induction hypothesis to k
    rcases ih k hk_lt hk_ge with ⟨s, h_prime, h_sum⟩
    have : ∀ x ∈ s, x < p := by
      intro x hx
      have : x ≤ k := by
        have sum_eq : ∑ y ∈ s, y = k := h_sum
        calc x = ∑ y ∈ {x}, y := by simp
          _ ≤ ∑ y ∈ s, y := sum_le_sum_of_subset_of_nonneg (singleton_subset_iff.mpr hx) (fun _ _ _ => Nat.zero_le _)
          _ = k := sum_eq
      have : k < p := by
        dsimp [k]
        omega
      omega
    have hp_notin_s : p ∉ s := by
      intro H
      have := this p H
      linarith

    -- Construct representation for m: p plus primes in s
    refine ⟨insert p s, ?_, ?_⟩
    · intro x hx
      simp [Finset.mem_insert] at hx
      rcases hx with (rfl|hx)
      · exact hp_prime
      · exact h_prime x hx
    · rw [sum_insert hp_notin_s, h_sum]
      omega

#check sum_of_distinct_primes
