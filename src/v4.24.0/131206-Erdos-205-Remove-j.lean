/-
This is a Lean formalization of a solution to Erdős Problem 205.
https://www.erdosproblems.com/forum/thread/205

This file implements the SIMPLIFIED proof using prime powers p_k^E.

The simplified construction uses:
- Moduli: 2^E, 3, and p_k^E for k = 0, ..., E-1
- Remainders: 0, 0, and 2^k for k = 0, ..., E-1

Where p_k is the (k+3)-th prime (so p_0 = 5, p_1 = 7, etc.)

The proof is verified by Lean. The following version numbers were used:
Lean Toolchain version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7 (v4.24.0)
-/

import Mathlib

open Real Filter Asymptotics

/-! ## Section 1: Basic Definitions -/

/-
We assume we have the Prime Number Theorem in the (asymptotic) form
  nth_prime n ~ n * log n  as n → ∞.
-/
noncomputable abbrev nth_prime (n : ℕ) : ℕ := Nat.nth Nat.Prime n

axiom nth_prime_asymp :
    (fun n ↦ ((nth_prime n) : ℝ)) ~[atTop] (fun n ↦ (n : ℝ) * Real.log (n : ℝ))

/-
Let Omega(m) be the number of prime factors of m counted with multiplicity.
-/
def Omega (n : ℕ) : ℕ := n.primeFactorsList.length

/-
A "PNT-scale" rate:  sqrt( (log n) / (log log n) ).
(Defined for all `n` using Mathlib's total `Real.log`, `Real.sqrt`.)
-/
noncomputable def pntRate (n : ℕ) : ℝ :=
  Real.sqrt (Real.log (n : ℝ) / Real.log (Real.log (n : ℝ)))

/-
Select E distinct odd primes, none equal to 3; for definiteness, take the first E odd primes >= 5
and label them as p_k. The (k+3)-th prime gives us p_0 = 5, p_1 = 7, p_2 = 11, etc.
-/
noncomputable def p_k (E k : ℕ) : ℕ := Nat.nth Nat.Prime (k + 2)

/-
Define Q_k as p_k^E (the E-th power of p_k).
-/
noncomputable def Q_k (E k : ℕ) : ℕ := (p_k E k)^E

/-
Define M := 2^E * 3 * ∏_{k=0}^{E-1} Q_k.
-/
noncomputable def M (E : ℕ) : ℕ := 2^E * 3 * ∏ k ∈ Finset.range E, Q_k E k

/-
n is a solution if n ≡ 0 (mod 2^E), n ≡ 0 (mod 3), and n ≡ 2^k (mod Q_k) for all k < E.
-/
def is_solution (E n : ℕ) : Prop :=
  n ≡ 0 [MOD 2^E] ∧
  n ≡ 0 [MOD 3] ∧
  ∀ k < E, n ≡ 2^k [MOD Q_k E k]

/-
Define the modulus and remainder maps for the CRT system.
Index 0 corresponds to modulus 2^E and remainder 0.
Index 1 corresponds to modulus 3 and remainder 0.
Index k+2 corresponds to modulus Q_k and remainder 2^k.
-/
noncomputable def modulus_map (E : ℕ) (i : ℕ) : ℕ :=
  if i = 0 then 2^E
  else if i = 1 then 3
  else Q_k E (i - 2)

def remainder_map (i : ℕ) : ℕ :=
  if i = 0 then 0
  else if i = 1 then 0
  else 2^(i - 2)

def indices (E : ℕ) : List ℕ := List.range (E + 2)

/-! ## Section 2: Prime Properties -/

/-
p_k is always >= 5 for all valid indices.
-/
theorem p_k_ge_5 (E k : ℕ) : p_k E k ≥ 5 := by
  refine' le_trans _ ( Nat.nth_monotone _ <| Nat.le_add_left _ _ );
  · bound;
  · exact Nat.infinite_setOf_prime

/-
p_k is always prime.
-/
theorem p_k_prime (E k : ℕ) : Nat.Prime (p_k E k) := by
  exact Nat.prime_nth_prime _

/-
The primes p_k are distinct for distinct indices k.
-/
theorem p_k_injective (E : ℕ) :
  ∀ k1 < E, ∀ k2 < E,
  p_k E k1 = p_k E k2 → k1 = k2 := by
    intros k1 hk1 k2 hk2 h_eq;
    have h_inj : k1 + 2 = k2 + 2 := by
      apply Nat.nth_injective ( Nat.infinite_setOf_prime ) h_eq;
    omega

/-! ## Section 3: Coprimality for CRT -/

/-
Omega(Q_k) = E since Q_k = p_k^E.
-/
theorem Q_k_omega (E k : ℕ) : Omega (Q_k E k) = E := by
  -- Omega(p^E) = E for any prime p
  unfold Omega Q_k
  have h_prime : Nat.Prime (p_k E k) := p_k_prime E k
  rw [Nat.Prime.primeFactorsList_pow h_prime]
  simp

/-
The moduli Q_k are coprime to 2, 3, and each other.
-/
theorem moduli_properties (E : ℕ) :
  (∀ k < E, Nat.Coprime (Q_k E k) 2) ∧
  (∀ k < E, Nat.Coprime (Q_k E k) 3) ∧
  (∀ k1 < E, ∀ k2 < E, k1 ≠ k2 → Nat.Coprime (Q_k E k1) (Q_k E k2)) := by
    refine' ⟨ _, _, _ ⟩;
    · intro k hk
      -- p_k is odd (since p_k ≥ 5), so Q_k = p_k^E is odd
      have h_odd : Odd (p_k E k) := by
        exact Nat.Prime.odd_of_ne_two (p_k_prime E k) (by linarith [p_k_ge_5 E k])
      exact Nat.Coprime.pow_left _ (Nat.Coprime.symm (Nat.prime_two.coprime_iff_not_dvd.mpr (by simpa [← even_iff_two_dvd] using h_odd)))
    · intro k hk;
      refine' Nat.Coprime.pow_left _ _;
      -- Since p_k ≥ 5 and 3 is prime, they are coprime
      have h_ge_5 : p_k E k ≥ 5 := p_k_ge_5 E k
      exact (p_k_prime E k).coprime_iff_not_dvd.mpr fun h => by have := Nat.le_of_dvd (by decide) h; linarith;
    · intro k1 hk1 k2 hk2 hne;
      -- Since p_k1 and p_k2 are distinct primes, their powers are coprime
      have h_distinct : p_k E k1 ≠ p_k E k2 := by
        intro h_eq
        have := p_k_injective E k1 hk1 k2 hk2 h_eq
        contradiction
      have h_coprime_base : Nat.Coprime (p_k E k1) (p_k E k2) := by
        exact (Nat.coprime_primes (p_k_prime E k1) (p_k_prime E k2)).mpr h_distinct
      exact Nat.Coprime.pow_left E (Nat.Coprime.pow_right E h_coprime_base)

/-
The list of moduli consists of pairwise coprime integers.
-/
noncomputable def moduli_list (E : ℕ) : List ℕ := (indices E).map (modulus_map E)

def remainders_list (E : ℕ) : List ℕ := (indices E).map (remainder_map)

theorem moduli_pairwise_coprime (E : ℕ) (hE : E ≥ 10) :
  (moduli_list E).Pairwise Nat.Coprime := by
    simp [moduli_list];
    unfold indices modulus_map;
    have h_coprime : Nat.Coprime (2^E) 3 ∧ ∀ k < E, Nat.Coprime (2^E) (Q_k E k) ∧ Nat.Coprime 3 (Q_k E k) ∧ ∀ k1 < E, ∀ k2 < E, k1 ≠ k2 → Nat.Coprime (Q_k E k1) (Q_k E k2) := by
      have := moduli_properties E;
      exact ⟨ by exact Nat.Coprime.pow_left _ ( by decide ), fun k hk => ⟨ Nat.Coprime.pow_left _ ( this.1 k hk |> Nat.Coprime.symm ), this.2.1 k hk |> Nat.Coprime.symm, this.2.2 ⟩ ⟩;
    rw [ List.pairwise_iff_get ];
    grind

/-! ## Section 4: n_E Construction -/

/-
n_E satisfies the system of congruences.
-/
noncomputable def n_E (E : ℕ) (hE : E ≥ 10) : ℕ :=
  (Nat.chineseRemainderOfList (remainder_map) (modulus_map E) (indices E) (by
    have h := moduli_pairwise_coprime E hE
    rw [moduli_list] at h
    rw [List.pairwise_map] at h
    exact h
  )).val

theorem n_E_is_solution (E : ℕ) (hE : E ≥ 10) : is_solution E (n_E E hE) := by
  have h_cong : ∀ i ∈ indices E, n_E E hE ≡ remainder_map i [MOD modulus_map E i] := by
    unfold n_E;
    grind;
  refine' ⟨ _, _, _ ⟩;
  · exact h_cong 0 ( by simp +decide [ indices ] );
  · convert h_cong 1 _ using 1 ; norm_num [ indices ];
  · intro k hk;
    convert h_cong ( k + 2 ) _ using 1;
    exact List.mem_range.mpr ( by linarith )

/-! ## Section 5: Omega Properties and Lower Bounds -/

/-
If a divides b and b is not zero, then Omega(a) <= Omega(b).
-/
theorem Omega_dvd_le {a b : ℕ} (h_dvd : a ∣ b) (hb : b ≠ 0) : Omega a ≤ Omega b := by
  obtain ⟨ c, rfl ⟩ := h_dvd;
  have h_prime_factors (p : ℕ) (hp : Nat.Prime p) (a c : ℕ) (ha : a ≠ 0) (hc : c ≠ 0) : (Nat.factorization a p) + (Nat.factorization c p) = (Nat.factorization (a * c) p) := by
    rw [ Nat.factorization_mul ] <;> aesop;
  have h_omega_def : Omega a = ∑ p ∈ Nat.primeFactors a, Nat.factorization a p ∧ Omega (a * c) = ∑ p ∈ Nat.primeFactors (a * c), Nat.factorization (a * c) p := by
    have h_omega_def : ∀ n : ℕ, n ≠ 0 → (Nat.primeFactorsList n).length = ∑ p ∈ Nat.primeFactors n, Nat.factorization n p := by
      intro n hn; rw [ ← Multiset.coe_card ] ; rw [ ← Multiset.toFinset_sum_count_eq ] ; aesop;
    exact ⟨ h_omega_def a ( by aesop ), h_omega_def ( a * c ) hb ⟩;
  rw [ h_omega_def.1, h_omega_def.2 ];
  exact Finset.sum_le_sum_of_subset ( Nat.primeFactors_mono ( dvd_mul_right _ _ ) ( by aesop ) ) |> le_trans ( Finset.sum_le_sum fun p hp => h_prime_factors p ( Nat.prime_of_mem_primeFactors hp ) a c ( by aesop ) ( by aesop ) ▸ Nat.le_add_right _ _ )

/-
Omega(2^E) = E.
-/
theorem Omega_pow_two (E : ℕ) : Omega (2^E) = E := by
  have h_prime_power : ∀ p k : ℕ, Nat.Prime p → Omega (p ^ k) = k := by
    intros p k hp
    have h_prime_factors : (p ^ k).primeFactorsList = List.replicate k p := by
      exact Nat.Prime.primeFactorsList_pow hp k;
    unfold Omega; aesop;
  exact h_prime_power 2 E Nat.prime_two

/-
n_E is not a power of 2.
-/
theorem n_E_not_pow_two (E : ℕ) (hE : E ≥ 10) : ∀ k, n_E E hE ≠ 2^k := by
  have h_mod_3 : n_E E hE ≡ 0 [MOD 3] := by
    exact n_E_is_solution E hE |>.2.1;
  exact fun k hk => by have := Nat.dvd_of_mod_eq_zero h_mod_3; norm_num [ hk, Nat.Prime.dvd_iff_one_le_factorization ] at this;

/-
If k < E, then Omega(n(E) - 2^k) >= E.
-/
theorem Omega_lower_bound_case1 (E : ℕ) (hE : E ≥ 10) (k : ℕ) (hk : k < E) (h_le : 2^k ≤ n_E E hE) :
  Omega (n_E E hE - 2^k) ≥ E := by
    -- Since Q_k divides n_E - 2^k and Omega(Q_k) = E, we have Omega(n_E - 2^k) >= E
    have h_Qk_div : Q_k E k ∣ n_E E hE - 2 ^ k := by
      have h_mod : n_E E hE ≡ 2^k [MOD Q_k E k] := by
        convert n_E_is_solution E hE |>.2.2 k hk;
      rw [ ← Nat.modEq_zero_iff_dvd ];
      cases le_iff_exists_add'.mp h_le ; simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ];
    by_cases h : n_E E hE - 2 ^ k = 0;
    · rw [ Nat.sub_eq_iff_eq_add ] at h;
      · have := n_E_not_pow_two E hE k; aesop;
      · exact h_le;
    · have h_omega : Omega (Q_k E k) = E := Q_k_omega E k
      exact le_trans ( by rw [h_omega] ) ( Omega_dvd_le h_Qk_div h )

/-
If k >= E, then Omega(n(E) - 2^k) >= E.
-/
theorem Omega_lower_bound_case2 (E : ℕ) (hE : E ≥ 10) (k : ℕ) (hk : k ≥ E) (h_le : 2^k ≤ n_E E hE) :
  Omega (n_E E hE - 2^k) ≥ E := by
    have h_div : 2^E ∣ (n_E E (by linarith) - 2^k) := by
      have h_n_E_sol : n_E E hE ≡ 0 [MOD 2^E] := by
        exact n_E_is_solution E hE |>.1;
      exact Nat.dvd_sub ( Nat.dvd_of_mod_eq_zero h_n_E_sol ) ( pow_dvd_pow _ hk );
    by_cases h : n_E E ( by linarith ) - 2 ^ k = 0 <;> simp_all +decide [ Nat.dvd_iff_mod_eq_zero ];
    · rw [ Nat.sub_eq_iff_eq_add ] at h <;> try linarith;
      exact absurd ( n_E_not_pow_two E ( by linarith ) k ) ( by aesop );
    · have h_omega_ge_E : Omega (2^E) ≤ Omega (n_E E hE - 2^k) := by
        exact Omega_dvd_le ( Nat.dvd_of_mod_eq_zero h_div ) h;
      exact le_trans ( by rw [ Omega_pow_two ] ) h_omega_ge_E

/-
Omega(n(E) - 2^k) >= E for all valid k.
-/
theorem Omega_lower_bound (E : ℕ) (hE : E ≥ 10) (k : ℕ) (h_le : 2^k ≤ n_E E hE) :
  Omega (n_E E hE - 2^k) ≥ E := by
    by_cases hk : k < E;
    · exact Omega_lower_bound_case1 E hE k hk h_le;
    · exact Omega_lower_bound_case2 E hE k ( le_of_not_gt hk ) h_le

/-! ## Section 6: PNT Axiom and Size Bounds -/

/-
From `nth_prime_asymp` one can extract a Big-O / "exists a constant" upper bound for the
n-th prime:  ∃ C > 0, ∀ᶠ n, nth_prime(n) ≤ C * n * log n.
-/
theorem nth_prime_le_const_mul_log_eventually :
    ∃ C : ℝ, 0 < C ∧
      (∀ᶠ n in atTop, ((nth_prime n) : ℝ) ≤ C * (n : ℝ) * Real.log (n : ℝ)) := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n ≥ N, (nth_prime n : ℝ) / (n * Real.log n) < 2 := by
    have h_ratio : Filter.Tendsto (fun n : ℕ => (nth_prime n : ℝ) / (n * Real.log n)) Filter.atTop (nhds 1) := by
      have := nth_prime_asymp;
      rw [ Asymptotics.IsEquivalent ] at this;
      rw [ Asymptotics.isLittleO_iff_tendsto' ] at this;
      · simpa using this.add_const 1 |> Filter.Tendsto.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ Pi.sub_apply, sub_div, div_self <| ne_of_gt <| mul_pos ( Nat.cast_pos.mpr <| pos_of_gt hx ) <| Real.log_pos <| Nat.one_lt_cast.mpr hx ] ; ring );
      · filter_upwards [ Filter.eventually_gt_atTop 1 ] with n hn h using absurd h <| ne_of_gt <| mul_pos ( Nat.cast_pos.mpr <| pos_of_gt hn ) <| Real.log_pos <| Nat.one_lt_cast.mpr hn;
    simpa using h_ratio.eventually ( gt_mem_nhds one_lt_two );
  refine' ⟨ 2, zero_lt_two, _ ⟩;
  filter_upwards [ Filter.eventually_ge_atTop N, Filter.eventually_gt_atTop 1 ] with n hn hn' using by have := hN n hn; rw [ div_lt_iff₀ ( mul_pos ( Nat.cast_pos.mpr <| pos_of_gt hn' ) <| Real.log_pos <| Nat.one_lt_cast.mpr hn' ) ] at this; linarith;

/-
A PNT-quality bound for p_k, stated in the "∃ constant, for all sufficiently large E" form.
For each k < E, we have p_k ≤ C * E * log E eventually.
-/
theorem p_k_bound_eventually :
    ∃ C : ℝ, 0 < C ∧
      (∀ᶠ E in atTop,
        ∀ k < E,
          ((p_k E k) : ℝ) ≤ C * (E : ℝ) * Real.log (E : ℝ)) := by
  obtain ⟨C, hC_pos, hC_eventually⟩ := nth_prime_le_const_mul_log_eventually
  -- For all sufficiently large n, nth_prime n ≤ C * n * log n
  -- Strategy: for k < E, p_k = nth_prime(k+2) ≤ nth_prime(E+1) ≤ C*(E+1)*log(E+1) ≤ 4C*E*log E
  use 4 * C
  constructor
  · positivity
  · -- Get N such that for all n ≥ N, nth_prime n ≤ C * n * log n
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hC_eventually
    filter_upwards [Filter.eventually_ge_atTop (max N 3)] with E hE_ge
    intro k hk
    have hE_ge_N : E ≥ N := le_of_max_le_left hE_ge
    have hE_ge_3 : E ≥ 3 := le_of_max_le_right hE_ge
    -- p_k E k = nth_prime (k + 2) ≤ nth_prime (E + 1) by monotonicity
    have hk2_le : k + 2 ≤ E + 1 := by omega
    have h_mono : p_k E k ≤ nth_prime (E + 1) := by
      unfold p_k nth_prime
      exact Nat.nth_monotone Nat.infinite_setOf_prime hk2_le
    -- E + 1 ≥ N, so nth_prime (E + 1) ≤ C * (E + 1) * log (E + 1)
    have hE1_ge_N : N ≤ E + 1 := by omega
    have h_bound := hN (E + 1) hE1_ge_N
    -- Now bound (E + 1) * log (E + 1) ≤ 4 * E * log E for E ≥ 3
    -- This is a straightforward nonlinear bound
    calc (p_k E k : ℝ) ≤ nth_prime (E + 1) := Nat.cast_le.mpr h_mono
      _ ≤ C * ((E + 1 : ℕ) : ℝ) * Real.log ((E + 1 : ℕ) : ℝ) := h_bound
      _ ≤ 4 * C * E * Real.log E := by
        -- For E ≥ 3: (E+1) ≤ 2E and log(E+1) ≤ 2*log E
        -- So C * (E+1) * log(E+1) ≤ C * 2E * 2*log E = 4 * C * E * log E
        simp only [Nat.cast_add, Nat.cast_one]
        have hE_ge_3_real : (E : ℝ) ≥ 3 := by exact_mod_cast hE_ge_3
        have hE_pos : (E : ℝ) > 0 := by linarith
        have hlogE_pos : Real.log E > 0 := Real.log_pos (by linarith)
        -- (E + 1) ≤ 2 * E for E ≥ 1
        have h1 : (E : ℝ) + 1 ≤ 2 * E := by linarith
        -- log(E + 1) ≤ 2 * log(E) for E ≥ 3 (since E + 1 ≤ E² for E ≥ 2)
        have h2 : Real.log ((E : ℝ) + 1) ≤ 2 * Real.log E := by
          have h_sq : (E : ℝ) + 1 ≤ E ^ 2 := by nlinarith
          calc Real.log ((E : ℝ) + 1) ≤ Real.log (E ^ 2) := Real.log_le_log (by linarith) h_sq
            _ = 2 * Real.log E := Real.log_pow E 2
        -- Combine using explicit multiplication bounds
        have hlog1_pos : Real.log ((E : ℝ) + 1) > 0 := Real.log_pos (by linarith)
        have hC_nonneg : C ≥ 0 := le_of_lt hC_pos
        calc C * ((E : ℝ) + 1) * Real.log ((E : ℝ) + 1)
          ≤ C * (2 * E) * Real.log ((E : ℝ) + 1) := by gcongr
          _ ≤ C * (2 * E) * (2 * Real.log E) := by gcongr
          _ = 4 * C * E * Real.log E := by ring

/-
A corresponding PNT-quality bound for log Q_k:
  log Q_k = E * log p_k ≤ C * E * log E  (eventually in E).
-/
theorem log_Q_k_bound_eventually :
    ∃ C : ℝ, 0 < C ∧
      (∀ᶠ E in atTop,
        ∀ k < E,
          Real.log ((Q_k E k : ℕ) : ℝ) ≤ C * (E : ℝ) * Real.log (E : ℝ)) := by
  obtain ⟨C₀, hC₀_pos, hC₀_eventually⟩ := p_k_bound_eventually
  -- p_k E k ≤ C₀ * E * log E
  -- log p_k ≤ log(C₀ * E * log E) = log C₀ + log E + log log E ≤ 3 log E (for large E)
  -- So E * log p_k ≤ 3 * E * log E
  use 3
  constructor
  · norm_num
  · -- Filter until E is large enough that log C₀ ≤ log E (i.e., C₀ ≤ E)
    have h_C_le_E_eventually : ∀ᶠ (E : ℕ) in atTop, C₀ ≤ (E : ℝ) := by
      filter_upwards [Filter.eventually_ge_atTop (Nat.ceil C₀)] with E (hE : Nat.ceil C₀ ≤ E)
      calc C₀ ≤ ↑(Nat.ceil C₀) := Nat.le_ceil C₀
        _ ≤ (E : ℝ) := Nat.cast_le.mpr hE
    filter_upwards [hC₀_eventually, Filter.eventually_ge_atTop 10, h_C_le_E_eventually]
      with E hE hE_ge hC_le_E
    intro k hk
    unfold Q_k
    rw [Nat.cast_pow, Real.log_pow]
    have hp_bound : (p_k E k : ℝ) ≤ C₀ * E * Real.log E := hE k hk
    have hE_pos : (E : ℝ) > 0 := by positivity
    have hlogE_pos : Real.log E > 0 := Real.log_pos (by norm_cast; omega : (E : ℝ) > 1)
    have hp_pos : (p_k E k : ℝ) > 0 := by
      have : p_k E k ≥ 5 := p_k_ge_5 E k
      positivity
    -- log p_k ≤ log(C₀ * E * log E)
    have h_log_pk : Real.log (p_k E k) ≤ Real.log (C₀ * E * Real.log E) := by
      apply Real.log_le_log hp_pos hp_bound
    -- log(C₀ * E * log E) = log C₀ + log E + log log E
    have h_expand : Real.log (C₀ * E * Real.log E) = Real.log C₀ + Real.log E + Real.log (Real.log E) := by
      rw [Real.log_mul (by positivity) (by positivity)]
      rw [Real.log_mul (by positivity) (by positivity)]
    -- For E ≥ 10: log log E ≤ log E
    have hE_ge_real : (E : ℝ) ≥ 10 := Nat.cast_le.mpr hE_ge
    have h_loglogE : Real.log (Real.log E) ≤ Real.log E := by
      apply Real.log_le_log hlogE_pos
      -- log E ≤ E - 1 < E for E > 0
      have h := Real.log_le_sub_one_of_pos hE_pos
      linarith
    -- log C₀ ≤ log E since C₀ ≤ E
    have h_logC : Real.log C₀ ≤ Real.log E := by
      apply Real.log_le_log hC₀_pos hC_le_E
    calc E * Real.log (p_k E k) ≤ E * Real.log (C₀ * E * Real.log E) := by gcongr
    _ = E * (Real.log C₀ + Real.log E + Real.log (Real.log E)) := by rw [h_expand]
    _ ≤ E * (Real.log E + Real.log E + Real.log E) := by gcongr
    _ = 3 * E * Real.log E := by ring

/-
A PNT-quality bound for M(E), again at the log level:
  log M(E) ≤ C * E^2 * log E  (eventually in E).
-/
theorem log_M_bound_eventually :
    ∃ C : ℝ, 0 < C ∧
      (∀ᶠ E in atTop,
        Real.log ((M E : ℕ) : ℝ) ≤ C * (E : ℝ)^2 * Real.log (E : ℝ)) := by
  obtain ⟨C, hC_pos, hC_bound⟩ := log_Q_k_bound_eventually;
  use (C + 4 : ℝ);
  constructor;
  · linarith;
  · have hM_log : ∀ E ≥ 10, Real.log (M E) ≤ Real.log (2^E) + Real.log 3 + ∑ k ∈ Finset.range E, Real.log (Q_k E k) := by
      intro E hE
      -- M E = 2^E * 3 * ∏ k, Q_k E k
      have hM_eq : (M E : ℝ) = (2^E : ℝ) * 3 * ∏ k ∈ Finset.range E, (Q_k E k : ℝ) := by
        simp only [M, Nat.cast_mul, Nat.cast_pow, Nat.cast_prod]
        norm_cast
      rw [hM_eq]
      have h2E_pos : (2^E : ℝ) > 0 := by positivity
      have h3_pos : (3 : ℝ) > 0 := by norm_num
      have hprod_pos : ∏ k ∈ Finset.range E, (Q_k E k : ℝ) > 0 := by
        apply Finset.prod_pos
        intros k _
        exact Nat.cast_pos.mpr (pow_pos (Nat.Prime.pos (p_k_prime E k)) E)
      rw [Real.log_mul (by linarith : (2^E : ℝ) * 3 ≠ 0) hprod_pos.ne']
      rw [Real.log_mul h2E_pos.ne' h3_pos.ne']
      gcongr
      rw [Real.log_prod (s := Finset.range E) (f := fun k => (Q_k E k : ℝ))]
      · intros k _
        exact Nat.cast_ne_zero.mpr (pow_ne_zero E (Nat.Prime.ne_zero (p_k_prime E k)))
    have h_sum_bound : ∀ᶠ E in Filter.atTop, ∑ k ∈ Finset.range E, Real.log (Q_k E k) ≤ C * E^2 * Real.log E := by
      filter_upwards [hC_bound, Filter.eventually_ge_atTop 10] with E hE hE'
      calc ∑ k ∈ Finset.range E, Real.log (Q_k E k)
        ≤ ∑ k ∈ Finset.range E, C * E * Real.log E := Finset.sum_le_sum fun k hk => hE k (Finset.mem_range.mp hk)
        _ = C * E^2 * Real.log E := by simp; ring
    filter_upwards [h_sum_bound, Filter.eventually_ge_atTop 10] with b hb hb'
    have hb'' : (b : ℝ) ≥ 10 := Nat.cast_le.mpr hb'
    have hlog : Real.log b ≥ 1 := by
      have hb_pos : (b : ℝ) > 0 := by linarith
      have hb_ge_e : (b : ℝ) ≥ Real.exp 1 := by
        have h1 : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans_le (by norm_num : (2.7182818286 : ℝ) ≤ 3)
        linarith
      exact (Real.le_log_iff_exp_le hb_pos).mpr hb_ge_e
    calc Real.log (M b) ≤ Real.log (2^b) + Real.log 3 + ∑ k ∈ Finset.range b, Real.log (Q_k b k) := hM_log b hb'
      _ = b * Real.log 2 + Real.log 3 + ∑ k ∈ Finset.range b, Real.log (Q_k b k) := by rw [Real.log_pow]
      _ ≤ b * Real.log 2 + Real.log 3 + C * b^2 * Real.log b := by linarith [hb]
      _ ≤ (C + 4) * b^2 * Real.log b := by
        -- b * log 2 + log 3 ≤ 4 * b^2 * log b for b ≥ 10
        -- LHS < b + 2, RHS ≥ 4 * b^2 * 1 = 4 * b^2
        -- Since b ≥ 10: b + 2 ≤ 2b ≤ b^2 ≤ 4 * b^2
        have h_log2 : Real.log 2 < 1 := by
          have h_exp1 : Real.exp 1 > 2 := by
            have := Real.exp_one_gt_d9; linarith
          have : Real.log 2 < Real.log (Real.exp 1) := Real.log_lt_log (by norm_num) h_exp1
          simp at this; exact this
        have h_log3 : Real.log 3 < 2 := by
          have h3_lt_exp2 : (3 : ℝ) < Real.exp 2 := by
            have h1 := Real.exp_one_gt_d9
            have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; ring_nf
            nlinarith
          have : Real.log 3 < Real.log (Real.exp 2) := Real.log_lt_log (by norm_num) h3_lt_exp2
          simp at this; exact this
        have h_lhs : b * Real.log 2 + Real.log 3 < b + 2 := by nlinarith
        -- b + 2 ≤ 4 * b^2 for b ≥ 10: since b ≥ 10, b + 2 ≤ 2b ≤ b^2 ≤ 4*b^2
        have h_b2 : (b : ℝ) + 2 ≤ 4 * b^2 := by
          have hb10 : (b : ℝ) ≥ 10 := hb''
          have h1 : (b : ℝ) + 2 ≤ 2 * b := by linarith
          have h2 : 2 * (b : ℝ) ≤ b^2 := by nlinarith
          have h3 : (b : ℝ)^2 ≤ 4 * b^2 := by nlinarith
          linarith
        have h_4b2 : 4 * (b : ℝ)^2 ≤ 4 * b^2 * Real.log b := by
          have : 1 ≤ Real.log b := hlog
          nlinarith
        nlinarith [hC_pos]

/-
n_E < M(E).
-/
theorem n_E_lt_M (E : ℕ) (hE : E ≥ 10) : n_E E hE < M E := by
  have h_n_E_lt_M : n_E E hE < Finset.prod (Finset.range (E + 2)) (fun i => modulus_map E i) := by
    apply Nat.chineseRemainderOfList_lt_prod; norm_num [ indices ];
    intros i hi
    simp [modulus_map];
    split_ifs <;> norm_num [ Nat.Prime.ne_zero ];
    exact pow_ne_zero E <| Nat.Prime.ne_zero <| p_k_prime E _;
  convert h_n_E_lt_M using 1;
  unfold modulus_map M Q_k; simp +decide [ Finset.prod_range_succ' ] ;
  ring

/-
The "inversion step" expressed in the most natural way:
From the PNT-quality upper bound log n_E ≤ C E^2 log E, one gets
  pntRate(n_E) ≤ C' * E
eventually in E, and thus
  E ≥ c * pntRate(n_E)
-/
theorem pntRate_n_E_le_const_mul_E_eventually :
    ∃ C : ℝ, 0 < C ∧
      (∀ᶠ E in atTop,
        ∀ hE : E ≥ 10,
          pntRate (n_E E hE) ≤ C * (E : ℝ)) := by
  obtain ⟨C, hC_pos, hC_bound⟩ : ∃ C : ℝ, 0 < C ∧ ∀ᶠ E in Filter.atTop, ∀ (hE : E ≥ 10), Real.log (n_E E hE) ≤ C * (E : ℝ)^2 * Real.log (E : ℝ) := by
    obtain ⟨ C, hC₀, hC ⟩ := log_M_bound_eventually;
    exact ⟨ C, hC₀, hC.mono fun E hE hE' => le_trans ( Real.log_le_log ( Nat.cast_pos.mpr <| Nat.pos_of_ne_zero <| by
      intro h; have := n_E_is_solution E hE'; rw [h] at this;
      have this_k := this.2.2 0 ( by linarith ) ;
      unfold Q_k at this_k; norm_num at this_k;
      -- Now this_k says 0 ≡ 1 (mod p_k E 0 ^ E)
      rw [Nat.ModEq] at this_k
      -- This means 0 % (p_k E 0 ^ E) = 1 % (p_k E 0 ^ E)
      have : p_k E 0 ≥ 5 := p_k_ge_5 E 0
      have hpow : p_k E 0 ^ E ≥ 2 := by
        calc p_k E 0 ^ E ≥ 5 ^ E := Nat.pow_le_pow_left this E
        _ ≥ 5 ^ 1 := Nat.pow_le_pow_right (by omega) (by omega : 1 ≤ E)
        _ = 5 := by norm_num
        _ ≥ 2 := by norm_num
      norm_num [Nat.mod_eq_of_lt (by omega : 1 < p_k E 0 ^ E)] at this_k) <| Nat.cast_le.mpr <| n_E_lt_M E hE' |> le_of_lt ) hE ⟩;
  -- Use constant 2*C + 1 to account for the log E / 2 bound and ensure sqrt ≤ linear
  use 2 * C + 1
  constructor
  · positivity
  · filter_upwards [hC_bound, Filter.eventually_ge_atTop 10] with E hE hE_ge
    intro hE_ge10
    unfold pntRate
    have h_log_upper : Real.log (n_E E hE_ge10) ≤ C * E^2 * Real.log E := hE hE_ge10
    have h_nE_ge : n_E E hE_ge10 ≥ 2^E := by
      have h_div := Nat.dvd_of_mod_eq_zero (n_E_is_solution E hE_ge10).1
      have h_nE_pos : n_E E hE_ge10 > 0 := Nat.pos_of_ne_zero (by
        intro h
        have := (n_E_is_solution E hE_ge10).2.2 0 (by omega)
        rw [h, Nat.ModEq] at this
        unfold Q_k at this
        norm_num at this
        have hp : p_k E 0 ≥ 5 := p_k_ge_5 E 0
        have hE_ne : E ≠ 0 := by omega
        have hpow : p_k E 0 ^ E > 1 := Nat.one_lt_pow hE_ne (by omega : 1 < p_k E 0)
        omega)
      exact Nat.le_of_dvd h_nE_pos h_div
    have h_logE_pos : Real.log E > 0 := Real.log_pos (by norm_cast; omega)
    have h_num_pos : Real.log (n_E E hE_ge10) > 0 := by
      have h_log2_pos : Real.log 2 > 0 := Real.log_pos (by norm_num : (2 : ℝ) > 1)
      calc Real.log (n_E E hE_ge10) ≥ Real.log (2^E : ℕ) :=
        Real.log_le_log (by positivity) (Nat.cast_le.mpr h_nE_ge)
      _ = E * Real.log 2 := by rw [Nat.cast_pow]; exact Real.log_pow 2 E
      _ > 0 := by positivity
    -- We show log(log(n_E)) ≥ log E / 2, which gives us the bound
    -- Key: E * log 2 ≥ sqrt(E) for E ≥ 10, so log(E * log 2) ≥ log(sqrt E) = log E / 2
    have h_loglog_lower : Real.log (Real.log (n_E E hE_ge10)) ≥ Real.log E / 2 := by
      have h_log_lower : Real.log (n_E E hE_ge10) ≥ E * Real.log 2 := by
        calc Real.log (n_E E hE_ge10) ≥ Real.log (2^E : ℕ) :=
          Real.log_le_log (by positivity) (Nat.cast_le.mpr h_nE_ge)
        _ = E * Real.log 2 := by rw [Nat.cast_pow]; exact Real.log_pow 2 E
      have h_E_large : (E : ℝ) ≥ 10 := by exact_mod_cast hE_ge10
      have h_log2_pos : Real.log 2 > 0 := Real.log_pos (by norm_num : (2 : ℝ) > 1)
      have h_Elog2_pos : (E : ℝ) * Real.log 2 > 0 := by positivity
      -- E * log 2 ≥ sqrt(E) for E ≥ 10
      -- Using Real.log_two_gt_d9: log 2 > 0.6931471803
      have h_Elog2_ge_sqrtE : (E : ℝ) * Real.log 2 ≥ Real.sqrt E := by
        -- For E ≥ 10: (E * log 2)^2 ≥ E when E * (log 2)^2 ≥ 1
        -- Since log 2 > 0.69, (log 2)^2 > 0.47, so E * (log 2)^2 > 4.7 > 1 for E ≥ 10
        have h_log2 := Real.log_two_gt_d9  -- log 2 > 0.6931471803
        have h_log2_sq : Real.log 2 ^ 2 > 0.4 := by nlinarith
        have h_Elog2_sq_ge_E : (E : ℝ) * Real.log 2 ^ 2 ≥ 1 := by
          calc (E : ℝ) * Real.log 2 ^ 2 ≥ 10 * 0.4 := by nlinarith
          _ = 4 := by norm_num
          _ ≥ 1 := by norm_num
        -- (E * log 2)^2 = E^2 * (log 2)^2 = E * (E * (log 2)^2) ≥ E * 1 = E when E * (log 2)^2 ≥ 1
        have h_sq_ineq : ((E : ℝ) * Real.log 2)^2 ≥ E := by
          calc ((E : ℝ) * Real.log 2)^2 = E^2 * Real.log 2 ^ 2 := by ring
          _ = E * (E * Real.log 2 ^ 2) := by ring
          _ ≥ E * 1 := by gcongr
          _ = E := by ring
        -- sqrt((E * log 2)^2) ≥ sqrt(E), i.e., E * log 2 ≥ sqrt(E)
        have h_Elog2_pos : (E : ℝ) * Real.log 2 > 0 := by positivity
        calc Real.sqrt E ≤ Real.sqrt ((E * Real.log 2)^2) := by gcongr
        _ = E * Real.log 2 := Real.sqrt_sq h_Elog2_pos.le
      calc Real.log (Real.log (n_E E hE_ge10))
        ≥ Real.log (E * Real.log 2) := Real.log_le_log h_Elog2_pos h_log_lower
      _ ≥ Real.log (Real.sqrt E) := Real.log_le_log (Real.sqrt_pos.mpr (by positivity)) h_Elog2_ge_sqrtE
      _ = Real.log E / 2 := Real.log_sqrt (by positivity)
    have h_loglog_pos : Real.log (Real.log (n_E E hE_ge10)) > 0 := by linarith [h_loglog_lower, h_logE_pos]
    -- Main calc: pntRate ≤ sqrt(log n / (log E / 2)) ≤ sqrt(2C) * E ≤ 2C * E
    calc Real.sqrt (Real.log (n_E E hE_ge10) / Real.log (Real.log (n_E E hE_ge10)))
      ≤ Real.sqrt (Real.log (n_E E hE_ge10) / (Real.log E / 2)) := Real.sqrt_le_sqrt (by
        have hc : Real.log E / 2 > 0 := by linarith
        exact div_le_div_of_nonneg_left h_num_pos.le hc h_loglog_lower)
      _ = Real.sqrt (2 * Real.log (n_E E hE_ge10) / Real.log E) := by
        congr 1; field_simp
      _ ≤ Real.sqrt (2 * (C * E^2 * Real.log E) / Real.log E) := by gcongr
      _ = Real.sqrt (2 * C * E^2) := by
        congr 1
        have : Real.log E ≠ 0 := by linarith [h_logE_pos]
        field_simp
      _ = Real.sqrt (2 * C) * E := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
      _ ≤ (2 * C + 1) * E := by
        -- √x ≤ x + 1 for all x ≥ 0 (since √x ≤ 1 + x/2 ≤ 1 + x)
        have h_twoCpos : 2 * C ≥ 0 := by positivity
        have h1 : Real.sqrt (2 * C) ≤ 2 * C + 1 := by
          cases' le_or_gt (2 * C) 1 with h h
          · -- If 2C ≤ 1, then √(2C) ≤ 1 ≤ 2C + 1 (since 2C ≥ 0)
            calc Real.sqrt (2 * C) ≤ Real.sqrt 1 := by gcongr
            _ = 1 := Real.sqrt_one
            _ ≤ 2 * C + 1 := by linarith
          · -- If 2C > 1, then √(2C) < 2C ≤ 2C + 1
            -- √x < x for x > 1: equivalent to x < x² when x > 0
            have h2C_pos : 0 < 2 * C := by linarith
            have hsq : Real.sqrt (2 * C) < 2 * C := by
              have h_sq_lt : 2 * C < (2 * C)^2 := by nlinarith
              calc Real.sqrt (2 * C) < Real.sqrt ((2 * C)^2) := Real.sqrt_lt_sqrt h2C_pos.le h_sq_lt
              _ = 2 * C := Real.sqrt_sq (le_of_lt h2C_pos)
            linarith
        gcongr


/-! ## Section 7: Main Result -/

/-
Main inequality in the "sqrt(log n / log log n) with a constant" form:
There exists an absolute constant c > 0 such that for all sufficiently large E,
for every k with 2^k ≤ n_E, we have
  Omega(n_E - 2^k) ≥ c * sqrt(log n_E / log log n_E).
-/
theorem main_inequality_eventually :
    ∃ c : ℝ, 0 < c ∧
      (∀ᶠ E in atTop,
        ∀ hE : E ≥ 10,
          ∀ k, 2^k ≤ n_E E hE →
            (Omega (n_E E hE - 2^k) : ℝ) ≥ c * pntRate (n_E E hE)) := by
  -- Get the constant C from pntRate bound: pntRate(n_E) ≤ C * E
  obtain ⟨C, hC_pos, hC_bound⟩ := pntRate_n_E_le_const_mul_E_eventually
  -- Use c = 1/C as our constant
  use 1 / C
  constructor
  · positivity
  · filter_upwards [hC_bound, Filter.eventually_ge_atTop 10] with E hE_pntRate hE_ge10
    intro hE k h_le
    -- From Omega_lower_bound: Omega(n_E - 2^k) ≥ E
    have h_omega : Omega (n_E E hE - 2^k) ≥ E := Omega_lower_bound E hE k h_le
    -- From pntRate bound: pntRate(n_E) ≤ C * E, so E ≥ (1/C) * pntRate(n_E)
    have h_pnt : pntRate (n_E E hE) ≤ C * E := hE_pntRate hE
    -- Therefore: Omega(n_E - 2^k) ≥ E ≥ (1/C) * pntRate(n_E)
    calc (Omega (n_E E hE - 2^k) : ℝ)
      ≥ E := by exact_mod_cast h_omega
    _ ≥ (1 / C) * pntRate (n_E E hE) := by
        have h_nonneg : pntRate (n_E E hE) ≥ 0 := by unfold pntRate; positivity
        rw [div_mul_eq_mul_div, one_mul, ge_iff_le]
        rw [div_le_iff₀ hC_pos]
        calc pntRate (n_E E hE) ≤ C * E := h_pnt
        _ = E * C := by ring

/-
The counterexample property, parameterized by the constant `c`.
-/
def is_counterexample (c : ℝ) (n : ℕ) : Prop :=
  ∀ k, 2^k ≤ n → (Omega (n - 2^k) : ℝ) ≥ c * pntRate n

/-
Infinitely many counterexamples, in the PNT-scale form:
∃ c > 0, there are infinitely many n such that
  ∀ k with 2^k ≤ n, Omega(n - 2^k) ≥ c * sqrt(log n / log log n).
-/
theorem infinitely_many_counterexamples :
    ∃ c : ℝ, 0 < c ∧ {n : ℕ | is_counterexample c n}.Infinite := by
  -- Get c from main_inequality_eventually
  obtain ⟨c, hc_pos, hc⟩ := main_inequality_eventually
  use c, hc_pos
  rw [Filter.eventually_atTop] at hc
  obtain ⟨a, ha⟩ := hc
  -- Show infinitude: for any n, there exists a counterexample > n
  refine Set.infinite_of_forall_exists_gt ?_
  intro n
  -- Use n_E (max a (max 10 (n + 1))) as the counterexample
  use n_E (max a (max 10 (n + 1))) (by omega)
  constructor
  · -- It's a counterexample
    exact ha _ (le_max_left _ _) (by omega)
  · -- It's > n
    -- n_E ≥ 2^E ≥ 2^(n+1) > n
    have h_sol := n_E_is_solution (max a (max 10 (n + 1))) (by omega)
    have h_div : 2^(max a (max 10 (n + 1))) ∣ n_E (max a (max 10 (n + 1))) (by omega) :=
      Nat.dvd_of_mod_eq_zero h_sol.1
    have h_pos : n_E (max a (max 10 (n + 1))) (by omega) > 0 := by
      apply Nat.pos_of_ne_zero
      intro H
      have := h_sol.2.2 0 (by omega)
      rw [H, Nat.ModEq] at this
      unfold Q_k at this
      norm_num at this
      have hp := p_k_ge_5 (max a (max 10 (n + 1))) 0
      have hpow : p_k (max a (max 10 (n + 1))) 0 ^ (max a (max 10 (n + 1))) > 1 :=
        Nat.one_lt_pow (by omega) (by omega : 1 < p_k (max a (max 10 (n + 1))) 0)
      omega
    calc n < n + 1 := Nat.lt_succ_self n
    _ ≤ max 10 (n + 1) := le_max_right _ _
    _ ≤ max a (max 10 (n + 1)) := le_max_right _ _
    _ < 2^(max a (max 10 (n + 1))) := by
        have : max a (max 10 (n + 1)) ≥ 10 := le_max_of_le_right (le_max_left _ _)
        have h2 : ∀ k ≥ 10, k < 2^k := fun k hk => by
          induction k with
          | zero => omega
          | succ k ih =>
            cases' Nat.lt_or_ge k 10 with h h
            · interval_cases k <;> norm_num
            · calc k + 1 < 2^k + 1 := by linarith [ih h]
              _ ≤ 2^k + 2^k := by linarith [Nat.one_le_pow k 2 (by omega)]
              _ = 2^(k + 1) := by ring
        exact h2 _ this
    _ ≤ n_E (max a (max 10 (n + 1))) (by omega) := Nat.le_of_dvd h_pos h_div

#check Omega_lower_bound
#check infinitely_many_counterexamples
#print axioms infinitely_many_counterexamples
