import Mathlib
lemma two_rpow_ge_add_one (x : ℝ) (hx : x ≥ 1) : 2 ^ x ≥ x + 1 := by
  have h : 1 + x * 1 ≤ (1 + 1) ^ x :=
    one_add_mul_self_le_rpow_one_add (by norm_num : (-1 : ℝ) ≤ 1) hx
  rw [mul_one] at h
  norm_num at h
  rw [add_comm] at h
  exact h
theorem two_rpow_ge_half_add_one (x : ℝ) (hx : x ≥ 0) : 2 ^ x ≥ x / 2 + 1 := by
  -- We use the fact that 2^x = exp(log 2 * x) for base 2 > 0
  have h_rpow_def : 2 ^ x = Real.exp (Real.log 2 * x) :=
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < (2 : ℝ)) x

  -- We need log 2 >= 1/2
  -- We know log 2 > 0.6931471803 and 0.6931471803 > 1/2
  have h_log_two_ge_half : Real.log 2 ≥ 1 / 2 := by linarith [Real.log_two_gt_d9]
  have h_log_two_minus_half_nonneg : Real.log 2 - 1 / 2 ≥ 0 :=
    sub_nonneg.mpr h_log_two_ge_half
  -- We need to show x * log 2 >= x / 2
  have h_mul_nonneg : x * (Real.log 2 - 1 / 2) ≥ 0 :=
    mul_nonneg hx h_log_two_minus_half_nonneg
  have h_expand_mul : x * Real.log 2 - x * (1 / 2) ≥ 0 := by rwa [mul_sub] at h_mul_nonneg
  have h_div_rewrite : x * Real.log 2 - x / 2 ≥ 0 := by rwa [mul_one_div] at h_expand_mul
  have h_rearrange : x * Real.log 2 ≥ x / 2 := by linarith [h_div_rewrite]
  -- Now combine the inequalities using calc
  calc
    2 ^ x
    _ = Real.exp (Real.log 2 * x) := h_rpow_def
    _ ≥ Real.log 2 * x + 1 := Real.add_one_le_exp (Real.log 2 * x)
    _ = 1 + Real.log 2 * x := by ring
    _ ≥ 1 + x / 2 := by linarith [h_rearrange]
    _ = x / 2 + 1 := by ring
theorem fundamental_theorem_of_arithmetic : UniqueFactorizationMonoid ℕ := by
  exact Nat.instUniqueFactorizationMonoid
-- Definition [Divisor function]
def tau (n : ℕ) : ℕ := n.divisors.card
lemma tau_eq_prod_factorization_add_one (n : ℕ) (hn : n ≠ 0) : tau n = n.primeFactors.prod (λ p => n.factorization p + 1) := by
  exact Nat.card_divisors hn
lemma tau_n_div_n_rpow_eps_eq_prod (n : ℕ) (hn : n ≠ 0) (ε : ℝ) : (tau n : ℝ) / ((n : ℝ) ^ ε) = n.primeFactors.prod (fun p => (((n.factorization p) + 1 : ℝ) / ((p : ℝ) ^ ((n.factorization p : ℝ) * ε)))) := by
  simp only [tau]
  rw [Nat.card_divisors hn]
  rw [Nat.cast_prod]
  -- Express n as product of prime factors
  have h_n_eq : (n : ℝ) = ∏ p ∈ n.primeFactors, (p : ℝ) ^ (n.factorization p) := by
    conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hn]
    rw [← Nat.prod_factorization_eq_prod_primeFactors]
    rw [Nat.cast_finsupp_prod]
    simp only [Nat.cast_pow]
  rw [h_n_eq]
  -- Now handle the rpow of the product
  have h_prod_rpow : (∏ p ∈ n.primeFactors, (p : ℝ) ^ (n.factorization p)) ^ ε =
                      ∏ p ∈ n.primeFactors, (p : ℝ) ^ ((n.factorization p : ℝ) * ε) := by
    rw [← Real.finset_prod_rpow]
    · congr 1
      ext p
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul (Nat.cast_nonneg _)]
    · intros p hp
      apply pow_nonneg
      exact Nat.cast_nonneg _
  rw [h_prod_rpow]
  rw [← Finset.prod_div_distrib]
  congr 1
  ext p
  rw [Nat.cast_add, Nat.cast_one]
lemma lemma7 (p a : ℕ) (ε : ℝ) (hp : p ≥ 2) (ha : a ≥ 1) (hε : ε > 0) (hε_small : ε < 1/100)  (h_cond : (p : ℝ) ^ ε ≥ 2) : (a + 1 : ℝ) / ((p : ℝ) ^ ((a : ℝ) * ε)) ≤ (a + 1 : ℝ) / ((2 : ℝ) ^ (a : ℝ)) ∧ (a + 1 : ℝ) / ((2 : ℝ) ^ (a : ℝ)) ≤ 1 := by
  constructor
  · -- First inequality: (a + 1 : ℝ) / ((p : ℝ) ^ ((a : ℝ) * ε)) ≤ (a + 1 : ℝ) / ((2 : ℝ) ^ (a : ℝ))
    apply div_le_div_of_nonneg_left
    · -- 0 ≤ (a + 1 : ℝ)
      linarith
    · -- 0 < (2 : ℝ) ^ (a : ℝ)
      apply Real.rpow_pos_of_pos
      norm_num
    · -- (2 : ℝ) ^ (a : ℝ) ≤ (p : ℝ) ^ ((a : ℝ) * ε)
      have h1 : (p : ℝ) ^ ((a : ℝ) * ε) = ((p : ℝ) ^ ε) ^ (a : ℝ) := by
        rw [← Real.rpow_mul]
        · rw [mul_comm]
        · exact Nat.cast_nonneg p
      rw [h1]
      have h2 : (2 : ℝ) ≤ (p : ℝ) ^ ε := h_cond
      have h3 : 0 ≤ (2 : ℝ) := by norm_num
      have h4 : 0 ≤ (a : ℝ) := Nat.cast_nonneg a
      exact Real.rpow_le_rpow h3 h2 h4
  · -- Second inequality: (a + 1 : ℝ) / ((2 : ℝ) ^ (a : ℝ)) ≤ 1
    rw [div_le_one]
    · exact two_rpow_ge_add_one (a : ℝ) (Nat.one_le_cast.mpr ha)
    · apply Real.rpow_pos_of_pos
      norm_num
lemma lemma8 (p a : ℕ) (ε : ℝ) (hp : p ≥ 2) (ha : a ≥ 1) (hε : ε > 0) (hε_small : ε < 1/100)  (hpε : (p : ℝ) ^ ε < 2) : (a + 1 : ℝ) / ((p : ℝ) ^ ((a : ℝ) * ε)) ≤ 2 / ε := by
  -- Use the fundamental constraint: since p^ε < 2 and p ≥ 2, ε must be very constrained
  -- We'll prove this using basic exponential properties

  -- First, establish that both denominators are positive
  have h_eps_pos : (0 : ℝ) < ε := hε
  have h_pow_pos : (0 : ℝ) < (p : ℝ) ^ ((a : ℝ) * ε) := by
    apply Real.rpow_pos_of_pos
    exact Nat.cast_pos.mpr (Nat.zero_lt_of_lt hp)

  -- Convert to multiplication: (a + 1) * ε ≤ 2 * p^(a * ε)
  rw [div_le_div_iff₀ h_pow_pos h_eps_pos]

  -- Since p ≥ 2, we have p^(a*ε) ≥ 1
  have h_pow_ge_one : (1 : ℝ) ≤ (p : ℝ) ^ ((a : ℝ) * ε) := by
    rw [← Real.rpow_zero (p : ℝ)]
    apply Real.rpow_le_rpow_of_exponent_le
    · have : (1 : ℝ) ≤ (2 : ℝ) := by norm_num
      have : (2 : ℝ) ≤ (p : ℝ) := Nat.cast_le.mpr hp
      exact le_trans ‹(1 : ℝ) ≤ (2 : ℝ)› ‹(2 : ℝ) ≤ (p : ℝ)›
    · exact mul_nonneg (Nat.cast_nonneg a) (le_of_lt hε)

  -- The key insight: we can bound (a + 1) * ε by using exponential growth
  -- Since p^(a*ε) grows exponentially, it will dominate (a + 1) * ε for reasonable values

  -- Use that p^(a*ε) ≥ 2^(a*ε) ≥ (a*ε)/2 + 1
  have h_ae_nonneg : (0 : ℝ) ≤ (a : ℝ) * ε := mul_nonneg (Nat.cast_nonneg a) (le_of_lt hε)

  have h_growth : ((a : ℝ) * ε) / 2 + 1 ≤ (p : ℝ) ^ ((a : ℝ) * ε) := by
    have h1 : ((a : ℝ) * ε) / 2 + 1 ≤ (2 : ℝ) ^ ((a : ℝ) * ε) :=
      two_rpow_ge_half_add_one ((a : ℝ) * ε) h_ae_nonneg
    have h2 : (2 : ℝ) ^ ((a : ℝ) * ε) ≤ (p : ℝ) ^ ((a : ℝ) * ε) := by
      apply Real.rpow_le_rpow (by norm_num) (Nat.cast_le.mpr hp) h_ae_nonneg
    exact le_trans h1 h2

  -- Show that (a + 1) * ε is not too large
  -- We use that (a + 1) * ε ≤ 2 * ((a * ε) / 2 + 1) when ε is bounded
  have h_final : (a + 1 : ℝ) * ε ≤ 2 * (((a : ℝ) * ε) / 2 + 1) := by
    -- Expand the right side: 2 * ((a * ε) / 2 + 1) = a * ε + 2
    -- So we need (a + 1) * ε ≤ a * ε + 2, which gives ε ≤ 2
    have h_rhs : 2 * (((a : ℝ) * ε) / 2 + 1) = (a : ℝ) * ε + 2 := by ring
    rw [h_rhs]
    -- We need (a + 1) * ε ≤ a * ε + 2, i.e., ε ≤ 2
    have h_eps_bound : ε ≤ 2 := by
      -- Since p^ε < 2 and p ≥ 2 ≥ 1, we have ε < 2
      -- (If ε ≥ 2, then p^ε ≥ p^2 ≥ 4, contradicting p^ε < 2)
      by_contra h_not
      push_neg at h_not
      have h_p_ge_one : (1 : ℝ) ≤ (p : ℝ) := by
        have : (1 : ℝ) ≤ (2 : ℝ) := by norm_num
        exact le_trans this (Nat.cast_le.mpr hp)
      have h_large : (4 : ℝ) ≤ (p : ℝ) ^ ε := by
        calc (4 : ℝ)
          _ = (2 : ℝ) ^ (2 : ℝ) := by norm_num
          _ ≤ (p : ℝ) ^ (2 : ℝ) := by
            apply Real.rpow_le_rpow (by norm_num) (Nat.cast_le.mpr hp) (by norm_num)
          _ ≤ (p : ℝ) ^ ε := by
            apply Real.rpow_le_rpow_of_exponent_le h_p_ge_one (le_of_lt h_not)
      linarith [h_large, hpε]
    calc (a + 1 : ℝ) * ε
      _ = (a : ℝ) * ε + ε := by ring
      _ ≤ (a : ℝ) * ε + 2 := by linarith [h_eps_bound]

  exact le_trans h_final (mul_le_mul_of_nonneg_left h_growth (by norm_num))
lemma lemma9 (s : Finset ℕ) (a : ℕ → ℕ) (ε : ℝ) (hε : ε > 0) (hε_small : ε < 1/100)  (hs_prime : ∀ p ∈ s, p.Prime) (ha_ge_one : ∀ p ∈ s, a p ≥ 1) :
  (∏ p ∈ s, ((a p + 1 : ℝ) / ((p : ℝ) ^ ((a p : ℝ) * ε)))) =
  (∏ p ∈ s.filter (fun (p : ℕ) => (p : ℝ) ^ ε ≥ 2), ((a p + 1 : ℝ) / ((p : ℝ) ^ ((a p : ℝ) * ε)))) *
  (∏ p ∈ s.filter (fun (p : ℕ) => (p : ℝ) ^ ε < 2), ((a p + 1 : ℝ) / ((p : ℝ) ^ ((a p : ℝ) * ε)))) := by
  symm
  rw [← Finset.prod_filter_mul_prod_filter_not s (fun (p : ℕ) => (p : ℝ) ^ ε ≥ 2)]
  congr 2
  ext p
  simp only [Finset.mem_filter, not_le]
lemma lemma10 (s : Finset ℕ) (a : ℕ → ℕ) (ε : ℝ) (hε : ε > 0) (hε_small : ε < 1/100)  (hs_prime : ∀ p ∈ s, p.Prime) (ha_ge_one : ∀ p ∈ s, a p ≥ 1) : ∏ p ∈ s.filter (fun (p : ℕ) => (p : ℝ) ^ ε ≥ 2), ((a p + 1 : ℝ) / ((p : ℝ) ^ ((a p : ℝ) * ε))) ≤ 1 := by
  apply Finset.prod_le_one
  · intro p hp
    rw [Finset.mem_filter] at hp
    rcases hp with ⟨hp_mem, hp_ge⟩
    have hp_prime := hs_prime p hp_mem
    have ha_p := ha_ge_one p hp_mem
    have hp_ge_one : p ≥ 1 := Nat.Prime.one_le hp_prime
    apply div_nonneg
    · exact add_nonneg (Nat.cast_nonneg _) (zero_le_one)
    · apply Real.rpow_nonneg
      exact Nat.cast_nonneg _
  · intro p hp
    rw [Finset.mem_filter] at hp
    rcases hp with ⟨hp_mem, hp_ge⟩
    have hp_prime := hs_prime p hp_mem
    have ha_p := ha_ge_one p hp_mem
    have hp_ge_one : p ≥ 2 := Nat.Prime.two_le hp_prime
    have h := lemma7 p (a p) ε hp_ge_one ha_p hε hε_small hp_ge
    calc (a p + 1 : ℝ) / (p : ℝ) ^ ((a p : ℝ) * ε)
        ≤ (a p + 1 : ℝ) / (2 : ℝ) ^ (a p : ℝ) := h.1
      _ ≤ 1 := h.2
lemma lemma11 (s : Finset ℕ) (a : ℕ → ℕ) (ε : ℝ) (hε : ε > 0) (hε_small : ε < 1/100)  (hs_prime : ∀ p ∈ s, p.Prime) (ha_ge_one : ∀ p ∈ s, a p ≥ 1) :
  (∏ p ∈ s.filter (fun (p : ℕ) => (p : ℝ) ^ ε < 2), ((a p + 1 : ℝ) / ((p : ℝ) ^ ((a p : ℝ) * ε)))) ≤
  (∏ p ∈ s.filter (fun (p : ℕ) => (p : ℝ) ^ ε < 2), (2 / ε : ℝ)) := by
  apply Finset.prod_le_prod
  · intro p hp
    have hp_mem : p ∈ s := by
      rw [Finset.mem_filter] at hp
      exact hp.1
    have ha_pos : a p ≥ 1 := ha_ge_one p hp_mem
    have hp_prime : p.Prime := hs_prime p hp_mem
    have hp_pos : p ≥ 1 := Nat.Prime.one_le hp_prime
    have hp_real_pos : (p : ℝ) > 0 := by
      apply Nat.cast_pos.mpr
      exact Nat.lt_of_succ_le hp_pos
    have ha_real_nonneg : (a p : ℝ) ≥ 0 := Nat.cast_nonneg _
    have hpow_pos : (p : ℝ) ^ ((a p : ℝ) * ε) > 0 := by
      apply Real.rpow_pos_of_pos hp_real_pos
    apply div_nonneg
    · have : (a p + 1 : ℝ) = ↑(a p) + 1 := by norm_cast
      rw [this]
      apply add_nonneg ha_real_nonneg
      exact zero_le_one
    · exact le_of_lt hpow_pos
  · intro p hp
    have hp_mem : p ∈ s := by
      rw [Finset.mem_filter] at hp
      exact hp.1
    have hp_cond : (p : ℝ) ^ ε < 2 := by
      rw [Finset.mem_filter] at hp
      exact hp.2
    have ha_pos : a p ≥ 1 := ha_ge_one p hp_mem
    have hp_prime : p.Prime := hs_prime p hp_mem
    have hp_pos : p ≥ 2 := Nat.Prime.two_le hp_prime
    exact lemma8 p (a p) ε hp_pos ha_pos hε hε_small hp_cond
lemma card_Icc_eq_sub_add_one (m M : ℕ) (h_le : m ≤ M) :
    (Finset.Icc m M).card = M - m + 1 := by
    have : M - m + 1 = M + 1 - m := by
      ring_nf
      rw [add_tsub_assoc_of_le h_le]
    rw [this]
    apply Nat.card_Icc
lemma card_le_max_sub_min_add_one (S : Finset ℕ) (hS_nonempty : S.Nonempty) :
    S.card ≤ S.max' hS_nonempty - S.min' hS_nonempty + 1 := by
  let m := S.min' hS_nonempty
  let M := S.max' hS_nonempty
  -- Establish that m ≤ M, which is necessary for our card_Icc_eq_sub_add_one lemma
  have h_min_le_max : m ≤ M := by
    apply Finset.le_max'
    exact Finset.min'_mem S hS_nonempty
  -- Rewrite the RHS of the inequality using our helper lemma
  rw [← card_Icc_eq_sub_add_one m M h_min_le_max] -- Goal: S.card ≤ (Finset.Icc m M).card
  -- Now, the goal is S.card ≤ (Finset.Icc m M).card.
  -- This follows if S is a subset of Finset.Icc m M.
  -- Prove S ⊆ Finset.Icc m M.
  have : S ≤ (Finset.Icc m M) := by
    intro x hx_in_S
    -- We need to show x ∈ Finset.Icc m M, which means m ≤ x ∧ x ≤ M.
    simp only [Finset.mem_Icc] -- This changes goal to ⊢ m ≤ x ∧ x ≤ M
    constructor
    · -- Prove m ≤ x. This is true by definition of S.min'.
      exact Finset.min'_le S x hx_in_S
    · -- Prove x ≤ M. This is true by definition of S.max'.
      exact Finset.le_max' S x hx_in_S
  exact Finset.card_le_card this
lemma finset_card_le_of_all_lt (S : Finset ℕ) (X : ℝ) (x_pos : X > 0) (s_pos : ∀ s, s ∈ S → s > 0 ) (hn : ∀ n ∈ S, (n : ℝ) < X) : S.card ≤ X := by
  -- Case analysis: S is empty or non-empty
  cases' S.eq_empty_or_nonempty with h_empty h_nonempty
  · -- Case 1: S is empty
    rw [h_empty, Finset.card_empty] -- S.card = 0
    simp only [Nat.cast_zero] -- Goal is now 0 ≤ X
    exact le_of_lt x_pos -- True because X > 0 implies 0 ≤ X

  · -- Case 2: S is non-empty
    -- Convert s_pos (s > 0) to (1 ≤ s) for use with lemmas
    have s_pos_ge1 : ∀ s ∈ S, 1 ≤ s := by
      intro s hs_mem
      specialize s_pos s hs_mem -- s > 0 for s in S
      linarith
    -- Get the maximum and minimum elements of S
    -- These require S to be non-empty (h_nonempty)
    let s_max := S.max' h_nonempty
    let s_min := S.min' h_nonempty
    -- Prove that s_min ≥ 1
    have h_s_min_mem : s_min ∈ S := Finset.min'_mem S h_nonempty
    have h_s_min_ge1 : 1 ≤ s_min := s_pos_ge1 s_min h_s_min_mem
    -- Key inequality relating card, max, and min for non-empty sets
    -- S.card ≤ s_max - s_min + 1
    have card_le_span : S.card ≤ s_max - s_min + 1 :=
      card_le_max_sub_min_add_one S h_nonempty
    -- From S.card ≤ s_max - s_min + 1 and 1 ≤ s_min, deduce S.card ≤ s_max
    -- This holds because if 1 ≤ s_min, then s_min - 1 ≥ 0.
    -- So, s_max - s_min + 1 = s_max - (s_min - 1) ≤ s_max.
    -- have s_min: (s_min - 1) ≥ 0 := by linarith
    have s_min_leq_smax : s_min ≤ s_max := by
      unfold s_min
      unfold s_max
      simp [Finset.min', Finset.max']
      aesop
    have {a b : Nat} (z : 1 ≤ b) (h : b ≤ a):  a - b + 1 = a - (b - 1) := by
      cases b
      · linarith
      · rename_i num
        simp
        induction a
        linarith
        rename_i ia aih
        rw [Nat.succ_sub_succ_eq_sub ia num]
        rw [←@Nat.sub_add_comm ia 1 num (by linarith)]

    have S_card_le_s_max : S.card ≤ s_max := by
      calc S.card
        _ ≤ s_max - s_min + 1     := card_le_span
        _ = s_max - (s_min - 1)   := this h_s_min_ge1 s_min_leq_smax
        _ ≤ s_max                 := Nat.sub_le s_max (s_min - 1)
    -- Cast this inequality to real numbers
    have S_card_le_s_max_real : (S.card : ℝ) ≤ (s_max : ℝ) := by
      exact Nat.cast_le.mpr S_card_le_s_max
    -- The maximum element s_max is in S, so it's less than X by hypothesis hn
    have h_s_max_mem : s_max ∈ S := Finset.max'_mem S h_nonempty
    have s_max_lt_X : (s_max : ℝ) < X := hn s_max h_s_max_mem
    -- Combine (S.card : ℝ) ≤ (s_max : ℝ) and (s_max : ℝ) < X
    -- This implies (S.card : ℝ) < X
    have S_card_lt_X : (S.card : ℝ) < X :=
      lt_of_le_of_lt S_card_le_s_max_real s_max_lt_X
    -- Since (S.card : ℝ) < X, it's also true that (S.card : ℝ) ≤ X
    exact le_of_lt S_card_lt_X
lemma lemma12 (s : Finset ℕ) (ε : ℝ) (hε : ε > 0) (hε_small : ε < 1/100) (hs_prime : ∀ p ∈ s, p.Prime) :
  (2 / ε : ℝ) ^ ((s.filter (fun (p : ℕ) => (((↑p) : ℝ) ^ ε < (2 : ℝ)))).card : ℝ) ≤ (2 / ε : ℝ) ^ (2 : ℝ) ^ (1 / ε) := by
  -- Let S' = s.filter (fun p => p^ε < 2)
  let S' := s.filter (fun (p : ℕ) => (((↑p) : ℝ) ^ ε < (2 : ℝ)))
  have mem_s_is_prime : ∀ s, s ∈ S' → s.Prime := by aesop
  have s_pos: ∀ s, s ∈ S' → s > 0 := by
    intro n hn
    have : _ := Nat.Prime.ne_zero (mem_s_is_prime n hn)
    exact Nat.zero_lt_of_ne_zero this
  have h_base_gt_one : (2 / ε : ℝ) > 1 := by
    have h1 : (2 : ℝ) / ε > (2 : ℝ) / (1/100 : ℝ) := by
      apply div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 2) hε hε_small
    have h2 : (2 : ℝ) / (1/100 : ℝ) = 200 := by norm_num
    rw [h2] at h1
    linarith

  -- The function x ↦ (2/ε)^x is non-decreasing
  have h_mono : ∀ x y : ℝ, x ≤ y → (2 / ε : ℝ) ^ x ≤ (2 / ε : ℝ) ^ y := by
    intros x y hxy
    exact Real.rpow_le_rpow_of_exponent_le (le_of_lt h_base_gt_one) hxy

  -- Key bound: |S'| ≤ 2^(1/ε)
  have h_card_bound : (S'.card : ℝ) ≤ (2 : ℝ) ^ (1 / ε) := by
    -- Every prime in S' satisfies p^ε < 2, so p < 2^(1/ε)
    have h_prime_bound : ∀ p ∈ S', (p : ℝ) < (2 : ℝ) ^ (1 / ε) := by
      intro p hp
      have hp_mem : p ∈ s := by
        rw [Finset.mem_filter] at hp
        exact hp.1
      have hp_cond : (p : ℝ) ^ ε < 2 := by
        rw [Finset.mem_filter] at hp
        exact hp.2
      have hp_prime : p.Prime := hs_prime p hp_mem
      have hp_ge_two : p ≥ 2 := Nat.Prime.two_le hp_prime

      -- From p^ε < 2, we get p < 2^(1/ε) using contrapositive
      by_contra h_not
      push_neg at h_not
      have h_ge : (p : ℝ) ≥ (2 : ℝ) ^ (1 / ε) := h_not

      -- Since p ≥ 2^(1/ε) and ε > 0, we have p^ε ≥ (2^(1/ε))^ε = 2
      have h_rpow_ge : (p : ℝ) ^ ε ≥ ((2 : ℝ) ^ (1 / ε)) ^ ε := by
        exact Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) _) h_ge (le_of_lt hε)

      -- Simplify: (2^(1/ε))^ε = 2^((1/ε) * ε) = 2^1 = 2
      have h_simplify : ((2 : ℝ) ^ (1 / ε)) ^ ε = 2 := by
        rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        rw [div_mul_cancel₀ _ (ne_of_gt hε)]
        simp only [Real.rpow_one]

      rw [h_simplify] at h_rpow_ge
      -- This contradicts hp_cond : p^ε < 2
      linarith [hp_cond, h_rpow_ge]
    have : 1/ε > 0 := by exact one_div_pos.mpr hε
    have eps_eq_nnrealeps: Real.toNNReal (1/ε) = (1/ε) := by unfold Real.toNNReal; simp [this]; linarith
    have ex : 0 < ((2 : ℝ) ^ (1 / ε)) := by
      apply @NNReal.rpow_pos (1/ε) 2 (by simp)
    exact finset_card_le_of_all_lt S' ((2 : ℝ) ^ (1 / ε)) ex s_pos h_prime_bound
  -- Apply monotonicity
  exact h_mono (S'.card : ℝ) ((2 : ℝ) ^ (1 / ε)) h_card_bound
lemma lemma13 (n : ℕ) (ε : ℝ) (hn : n ≥ 1) (hε : ε > 0) (hε_small : ε < 1/100)  : (tau n : ℝ) / ((n : ℝ) ^ ε) ≤ (2 / ε : ℝ) ^ ((2 : ℝ) ^ (1 / ε)) := by
  rw [tau_n_div_n_rpow_eps_eq_prod n (Nat.one_le_iff_ne_zero.mp hn) ε]

  -- Split the product into two parts based on whether p^ε < 2
  have h_union : n.primeFactors = (n.primeFactors.filter (fun (p : ℕ) => ((p : ℝ) ^ ε < 2))) ∪
    (n.primeFactors.filter (fun (p : ℕ) => ¬((p : ℝ) ^ ε < 2))) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · intro hp
      by_cases h : (p : ℝ) ^ ε < 2
      · left; exact ⟨hp, h⟩
      · right; exact ⟨hp, h⟩
    · intro hp
      cases hp with
      | inl h => exact h.1
      | inr h => exact h.1

  -- Show disjointness
  have h_disj : Disjoint (n.primeFactors.filter (fun (p : ℕ) => ((p : ℝ) ^ ε < 2)))
    (n.primeFactors.filter (fun (p : ℕ) => ¬((p : ℝ) ^ ε < 2))) := by
    apply Finset.disjoint_filter_filter_neg

  -- Apply the union split
  rw [h_union, Finset.prod_union h_disj]

  -- First, bound the product over primes where p^ε < 2
  have h_small : ∀ p ∈ n.primeFactors.filter (fun (p : ℕ) => ((p : ℝ) ^ ε < 2)),
    ((n.factorization p + 1 : ℝ) / ((p : ℝ) ^ ((n.factorization p : ℝ) * ε))) ≤ 2 / ε := by
    intro p hp
    rw [Finset.mem_filter] at hp
    have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp.1
    have hp_pos : 2 ≤ p := Nat.Prime.two_le hp_prime
    have ha_pos : 1 ≤ n.factorization p := by
      rw [Nat.one_le_iff_ne_zero]
      have : p ∣ n := (Nat.mem_primeFactors.mp hp.1).2.1
      apply ne_of_gt
      exact Nat.Prime.factorization_pos_of_dvd hp_prime (Nat.one_le_iff_ne_zero.mp hn) this
    exact lemma8 p (n.factorization p) ε hp_pos ha_pos hε hε_small hp.2

    -- Next, bound the product over primes where p^ε ≥ 2
  have h_large : ∀ p ∈ n.primeFactors.filter (fun (p : ℕ) => ¬((p : ℝ) ^ ε < 2)),
    ((n.factorization p + 1 : ℝ) / ((p : ℝ) ^ ((n.factorization p : ℝ) * ε))) ≤ 1 := by
    intro p hp
    rw [Finset.mem_filter] at hp
    -- p^ε ≥ 2
    have hp_ge : 2 ≤ (p : ℝ) ^ ε := le_of_not_lt hp.2
    -- Use that n.factorization p ≥ 1
    have ha_pos : 1 ≤ n.factorization p := by
      rw [Nat.one_le_iff_ne_zero]
      have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp.1
      have : p ∣ n := (Nat.mem_primeFactors.mp hp.1).2.1
      apply ne_of_gt
      exact Nat.Prime.factorization_pos_of_dvd hp_prime (Nat.one_le_iff_ne_zero.mp hn) this
    -- Use 2^a ≥ a+1 for a ≥ 1
    have h_2pow : 2 ^ (n.factorization p : ℝ) ≥ (n.factorization p : ℝ) + 1 := by
      exact two_rpow_ge_add_one (n.factorization p : ℝ) (Nat.one_le_cast.mpr ha_pos)
    -- p^(a*ε) ≥ 2^a since p^ε ≥ 2 and a ≥ 1
    have h_pow : (p : ℝ) ^ ((n.factorization p : ℝ) * ε) ≥ 2 ^ (n.factorization p : ℝ) := by
      -- Write p^(a*ε) = (p^ε)^a
      have : (p : ℝ) ^ ((n.factorization p : ℝ) * ε) = ((p : ℝ) ^ ε) ^ (n.factorization p : ℝ) := by
        rw [mul_comm, Real.rpow_mul (Nat.cast_nonneg _) ε (n.factorization p : ℝ)]
      rw [this]
      -- Since p^ε ≥ 2, we have (p^ε)^a ≥ 2^a
      apply Real.rpow_le_rpow (by linarith) hp_ge (Nat.cast_nonneg _)
    -- Conclude
    calc ((n.factorization p + 1 : ℝ) / ((p : ℝ) ^ ((n.factorization p : ℝ) * ε)))
      ≤ ((n.factorization p : ℝ) + 1) / (2 ^ (n.factorization p : ℝ)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) h_pow
      _ ≤ 1 := by
        rw [div_le_one (by positivity)]
        exact h_2pow

  -- Apply the overall bound
  have h_prime_factors : ∀ p ∈ n.primeFactors, p.Prime := fun p hp =>
    Nat.prime_of_mem_primeFactors hp

  calc (n.primeFactors.filter (fun (p : ℕ) => ((p : ℝ) ^ ε < 2))).prod
        (fun p => (n.factorization p + 1 : ℝ) / (p : ℝ) ^ ((n.factorization p : ℝ) * ε)) *
       (n.primeFactors.filter (fun (p : ℕ) => ¬((p : ℝ) ^ ε < 2))).prod
        (fun p => (n.factorization p + 1 : ℝ) / (p : ℝ) ^ ((n.factorization p : ℝ) * ε))
  _ ≤ (n.primeFactors.filter (fun (p : ℕ) => ((p : ℝ) ^ ε < 2))).prod
        (fun p => 2 / ε) *
       (n.primeFactors.filter (fun (p : ℕ) => ¬((p : ℝ) ^ ε < 2))).prod
        (fun p => (1 : ℝ)) := by
    apply mul_le_mul
    · apply Finset.prod_le_prod
      · intros i hi
        apply div_nonneg
        · positivity
        · apply Real.rpow_nonneg
          exact Nat.cast_nonneg _
      · exact h_small
    · apply Finset.prod_le_prod
      · intros i hi
        apply div_nonneg
        · positivity
        · apply Real.rpow_nonneg
          exact Nat.cast_nonneg _
      · exact h_large
    · apply Finset.prod_nonneg
      intros i hi
      apply div_nonneg
      · positivity
      · apply Real.rpow_nonneg
        exact Nat.cast_nonneg _
    · apply Finset.prod_nonneg
      intros i hi
      positivity
  _ = (n.primeFactors.filter (fun (p : ℕ) => ((p : ℝ) ^ ε < 2))).prod (fun _ => 2 / ε) * 1 := by
    simp only [Finset.prod_const_one, mul_one]
  _ = (2 / ε) ^ (n.primeFactors.filter (fun (p : ℕ) => ((p : ℝ) ^ ε < 2))).card * 1 := by
    rw [Finset.prod_const]
  _ = (2 / ε) ^ (n.primeFactors.filter (fun (p : ℕ) => ((p : ℝ) ^ ε < 2))).card := by simp
  _ = (2 / ε) ^ ((n.primeFactors.filter (fun (p : ℕ) => ((p : ℝ) ^ ε < 2))).card : ℝ) := by
    rw [Real.rpow_natCast]
  _ ≤ (2 / ε) ^ (2 : ℝ) ^ (1 / ε) := lemma12 n.primeFactors ε hε hε_small h_prime_factors

lemma lemma14 (ε : ℝ) (hε : ε > 0) (hε_small : ε < 1/100)  : ∃ (C : ℝ), C > 0 ∧ (2 / ε) ^ ((2 : ℝ) ^ (1 / ε)) ≤ C := by
  use (2 / ε) ^ ((2 : ℝ) ^ (1 / ε))
  constructor
  · -- Show C > 0
    apply Real.rpow_pos_of_pos
    exact div_pos (by norm_num : (2 : ℝ) > 0) hε
  · -- Show (2/ε)^(2^(1/ε)) ≤ C
    rfl

lemma lemma15 (ε : ℝ) (hε : ε > 0) (hε_small : ε < 1/100)  : ∃ (C : ℝ), C > 0 ∧ ∀ (n : ℕ), 1 ≤ n → (tau n : ℝ) / ((n : ℝ) ^ ε) ≤ C := by
  obtain ⟨C, hC_pos, hC_bound⟩ := lemma14 ε hε hε_small
  use C
  constructor
  · exact hC_pos
  · intro n hn
    calc (tau n : ℝ) / ((n : ℝ) ^ ε)
      _ ≤ (2 / ε : ℝ) ^ ((2 : ℝ) ^ (1 / ε)) := lemma13 n ε hn hε hε_small
      _ ≤ C := hC_bound
lemma lemma16 (ε : ℝ) (hε : ε > 0) (hε_small : ε < 1/100)  : ∃ (C : ℝ), C > 0 ∧ ∀ (n : ℕ), 1 ≤ n → (tau n : ℝ) / ((n : ℝ) ^ ε) ≤ C := by
  exact lemma15 ε hε hε_small
lemma lemma17 (ε : ℝ) (hε : ε > 0) (hε_small : ε < 1/100)  : ∃ (C : ℝ), C > 0 ∧ ∀ (n : ℕ), 1 ≤ n → (tau n : ℝ) ≤ C * ((n : ℝ) ^ ε) := by
  obtain ⟨C, hC_pos, hC⟩ := lemma16 ε hε hε_small
  use C, hC_pos
  intro n hn
  specialize hC n hn
  rw [div_le_iff₀] at hC
  · exact hC
  · exact Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hn))) ε
theorem divisor_bound_tau_le_n_pow_o_one :
  ∀ ε : ℝ, ε > 0 → ε < 1/100 → Filter.Tendsto (fun n : ℕ => (tau n : ℝ) / (n : ℝ) ^ ε) Filter.atTop (nhds 0) := by
  intro ε hε hε_small
  -- We'll use the squeeze theorem with lemma 17
  -- First, get the bound from lemma 17 with ε/2
  have hε_half : ε / 2 > 0 := by linarith
  obtain ⟨C, hC_pos, hC_bound⟩ := lemma17 (ε / 2) hε_half (by linarith [hε_small])
  -- Now we'll show τ(n)/n^ε → 0 using squeeze theorem
  apply squeeze_zero'
  · -- Show 0 ≤ τ(n)/n^ε eventually
    filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    apply div_nonneg
    · exact Nat.cast_nonneg _
    · exact Real.rpow_nonneg (Nat.cast_nonneg n) ε
  · -- Show τ(n)/n^ε ≤ C/n^(ε/2) eventually
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    -- From lemma 17, we have τ(n) ≤ C * n^(ε/2)
    have h1 : (tau n : ℝ) ≤ C * (n : ℝ) ^ (ε / 2) := hC_bound n hn
    have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hn))
    -- We want to show τ(n)/n^ε ≤ C/n^(ε/2)
    calc (tau n : ℝ) / (n : ℝ) ^ ε
        ≤ C * (n : ℝ) ^ (ε / 2) / (n : ℝ) ^ ε := by
          apply div_le_div_of_nonneg_right h1
          exact Real.rpow_nonneg (Nat.cast_nonneg n) ε
      _ = C * ((n : ℝ) ^ (ε / 2) / (n : ℝ) ^ ε) := by
          rw [mul_div_assoc]
      _ = C * (n : ℝ) ^ (ε / 2 - ε) := by
          rw [← Real.rpow_sub hn_pos]
      _ = C * (n : ℝ) ^ (-(ε / 2)) := by
          congr 1
          ring_nf
      _ = C / (n : ℝ) ^ (ε / 2) := by
          rw [Real.rpow_neg (le_of_lt hn_pos)]
          rfl
  · -- Show C/n^(ε/2) → 0
    -- We'll show this converges to C * 0 = 0
    rw [show (0 : ℝ) = C * 0 by ring]
    apply Filter.Tendsto.const_mul
    -- Show (n^(ε/2))⁻¹ → 0
    -- This is the same as n^(-ε/2) → 0
    have h_eq : ∀ n : ℕ, ((n : ℝ) ^ (ε / 2))⁻¹ = (n : ℝ) ^ (-(ε / 2)) := by
      intro n
      rw [← Real.rpow_neg (Nat.cast_nonneg n)]
    simp only [h_eq]
    -- Use composition of tendsto
    have h1 : Filter.Tendsto (fun x : ℝ => x ^ (-(ε / 2))) Filter.atTop (nhds 0) :=
      tendsto_rpow_neg_atTop hε_half
    -- Use tendsto_natCast_atTop_atTop to show (n : ℝ) → ∞
    exact Filter.Tendsto.comp h1 tendsto_natCast_atTop_atTop
-- Definition [Radical]
def rad (n : ℕ) : ℕ := if n = 0 then 0 else n.primeFactors.prod id
lemma rad_eq_prod_distinct_prime_factors (n : ℕ) (hn : n ≠ 0) : rad n = n.factorization.support.prod id := by
  rw [rad, if_neg hn]
  rw [← Nat.support_factorization]
lemma rad_mul_of_coprime {a b : ℕ} (h : Nat.Coprime a b) : rad (a * b) = rad a * rad b := by
  by_cases ha : a = 0
  · simp [ha, rad]
  by_cases hb : b = 0
  · simp [hb, rad, Nat.mul_eq_zero]
  have hab_ne : a * b ≠ 0 := Nat.mul_ne_zero ha hb
  rw [rad, rad, rad, if_neg ha, if_neg hb, if_neg hab_ne]
  rw [Nat.Coprime.primeFactors_mul h]
  rw [Finset.prod_union (Nat.Coprime.disjoint_primeFactors h)]
lemma rad_abc_of_coprime (a b c : ℕ) (ha : a ≥ 1) (hb : b ≥ 1) (hc : c ≥ 1) (h_abc_coprime : Nat.Coprime a (b * c)) (h_bc_coprime : Nat.Coprime b c) : rad (a * b * c) = rad a * rad b * rad c := by
  rw [mul_assoc]
  rw [rad_mul_of_coprime h_abc_coprime]
  rw [rad_mul_of_coprime h_bc_coprime]
  rw [mul_assoc]
lemma lemma23 (a b c : ℕ) (ha : a ≥ 1) (hb : b ≥ 1) (hc : c ≥ 1) (h_abc_coprime : Nat.Coprime a (b * c)) (h_bc_coprime : Nat.Coprime b c) : rad (a * b) * rad (a * c) * rad (b * c) = (rad (a * b * c)) ^ 2 := by
  -- First, we use rad_abc_of_coprime to get rad (a * b * c) = rad a * rad b * rad c
  -- Note: the formal context has a typo - it expects (hc : c ≥ c) instead of (hc : c ≥ 1)
  have h_rad_abc : rad (a * b * c) = rad a * rad b * rad c :=
    rad_abc_of_coprime a b c ha hb hc h_abc_coprime h_bc_coprime

  -- Next, we need to establish pairwise coprimality
  -- From h_abc_coprime: Nat.Coprime a (b * c), we need Nat.Coprime a b and Nat.Coprime a c

  -- To show Nat.Coprime a b, we use the fact that any common divisor of a and b
  -- would also divide b*c, contradicting coprimality of a and b*c
  have h_ab_coprime : Nat.Coprime a b := by
    apply Nat.coprime_of_dvd'
    intro p hp hdvd_a hdvd_b
    -- If p divides both a and b, then p divides b*c
    have hdvd_bc : p ∣ b * c := dvd_mul_of_dvd_left hdvd_b c
    -- But then p is a common divisor of a and b*c, so p must divide their gcd = 1
    have : p ∣ 1 := by
      rw [← h_abc_coprime]
      exact Nat.dvd_gcd hdvd_a hdvd_bc
    exact this

  have h_ac_coprime : Nat.Coprime a c := by
    apply Nat.coprime_of_dvd'
    intro p hp hdvd_a hdvd_c
    -- If p divides both a and c, then p divides b*c
    have hdvd_bc : p ∣ b * c := dvd_mul_of_dvd_right hdvd_c b
    -- But then p is a common divisor of a and b*c, so p must divide their gcd = 1
    have : p ∣ 1 := by
      rw [← h_abc_coprime]
      exact Nat.dvd_gcd hdvd_a hdvd_bc
    exact this

  -- We already have h_bc_coprime: Nat.Coprime b c

  -- Now use rad_mul_of_coprime three times
  have h_rad_ab : rad (a * b) = rad a * rad b := rad_mul_of_coprime h_ab_coprime
  have h_rad_ac : rad (a * c) = rad a * rad c := rad_mul_of_coprime h_ac_coprime
  have h_rad_bc : rad (b * c) = rad b * rad c := rad_mul_of_coprime h_bc_coprime

  -- Now we need to show: rad (a * b) * rad (a * c) * rad (b * c) = (rad (a * b * c)) ^ 2
  rw [h_rad_ab, h_rad_ac, h_rad_bc, h_rad_abc]
  -- This becomes: (rad a * rad b) * (rad a * rad c) * (rad b * rad c) = (rad a * rad b * rad c) ^ 2
  ring
lemma lemma24 (n : ℕ) (hn : n ≥ 1) (s : Finset ℕ) (hs_prime : ∀ p ∈ s, p.Prime) (h_rad : rad n = s.prod id) :
  ∀ p ∈ s, n.factorization p ≥ 1 := by
  intro p hp
  have hn_ne_zero : n ≠ 0 := by omega

  -- rad n divides n
  have h_rad_dvd : rad n ∣ n := by
    rw [rad_eq_prod_distinct_prime_factors n hn_ne_zero]
    exact Nat.prod_primeFactors_dvd n

  -- Since rad n = s.prod id, we have s.prod id divides n
  rw [h_rad] at h_rad_dvd

  -- Since p ∈ s and s.prod id divides n, we have p divides n
  have hp_dvd : p ∣ n := by
    apply Nat.dvd_trans
    · exact Finset.dvd_prod_of_mem id hp
    · exact h_rad_dvd

  -- Convert divisibility to factorization
  rw [ge_iff_le]
  exact (Nat.Prime.dvd_iff_one_le_factorization (hs_prime p hp) hn_ne_zero).mp hp_dvd
/-- The set of natural numbers `n` up to `N` such that `rad n = r`. -/
def radical_set (r N : ℕ) : Finset ℕ := (Finset.range (N + 1)).filter (fun n => rad n = r)
-- Definition of the target set
-- The set of interest: natural numbers whose prime factors are exactly the set `s`.
def target_set (s : Finset ℕ) : Set ℕ :=
  { m : ℕ | m.primeFactors = s ∧ m ≥ 1 ∧ ∀ p ∈ s, m.factorization p ≥ 1 }


lemma lemma26 (s : Finset ℕ) (hs_prime : ∀ p ∈ s, p.Prime) :
  { n : ℕ | rad n = s.prod id } ⊆ target_set s := by
  intro n hn
  simp only [Set.mem_setOf] at hn
  simp only [target_set, Set.mem_setOf_eq]
  -- First show n ≠ 0
  have h_ne_zero : n ≠ 0 := by
    intro h0
    rw [h0, rad] at hn
    simp at hn
    -- We have 0 = s.prod id
    have h_prod_ne_zero : s.prod id ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro p hp
      have : p.Prime := hs_prime p hp
      exact Nat.Prime.ne_zero this
    exact h_prod_ne_zero hn.symm
  constructor
  · -- Show n.primeFactors = s
    -- Use rad_eq_prod_distinct_prime_factors
    rw [rad_eq_prod_distinct_prime_factors n h_ne_zero] at hn
    -- We have n.factorization.support.prod id = s.prod id
    -- And n.factorization.support = n.primeFactors by Nat.support_factorization
    rw [Nat.support_factorization] at hn
    -- So n.primeFactors.prod id = s.prod id
    -- Since both are products of prime sets, they must be equal
    have h_prime_n : ∀ p ∈ n.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
    -- Apply unique factorization
    -- First note that s.prod id = ∏ p ∈ s, p
    have h_prod_eq_s : (s.prod id).primeFactors = s := Nat.primeFactors_prod hs_prime
    have h_prod_eq_n : (n.primeFactors.prod id).primeFactors = n.primeFactors := Nat.primeFactors_prod h_prime_n
    -- Since n.primeFactors.prod id = s.prod id (by hn), their primeFactors are equal
    rw [hn] at h_prod_eq_n
    rw [h_prod_eq_s] at h_prod_eq_n
    exact h_prod_eq_n.symm
  · -- Show ∀ p ∈ s, n.factorization p ≥ 1
    have h_ge : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr h_ne_zero
    exact ⟨h_ge, lemma24 n h_ge s hs_prime hn⟩
lemma card_finset_eq_sum_ones (s : Finset ℕ) : s.card = ∑ _x ∈ s, 1 := by
  exact Finset.card_eq_sum_ones s
lemma lemma28 (ε : ℝ) (n N : ℕ) (hε : ε > 0) (hε_small : ε < 1/100)  (hn : 1 ≤ n) (hnN : n ≤ N) : 1 / ((n : ℝ) ^ ε) ≥ 1 / ((N : ℝ) ^ ε) := by
  have hn_pos : 0 < (n : ℝ) := by
    simp only [Nat.cast_pos]
    exact hn
  have hN_pos : 0 < (N : ℝ) := by
    simp only [Nat.cast_pos]
    linarith
  have hnε_pos : 0 < (n : ℝ) ^ ε := Real.rpow_pos_of_pos hn_pos ε
  have hNε_pos : 0 < (N : ℝ) ^ ε := Real.rpow_pos_of_pos hN_pos ε
  rw [ge_iff_le]
  rw [one_div_le_one_div hNε_pos hnε_pos]
  apply Real.rpow_le_rpow
  · exact le_of_lt hn_pos
  · exact Nat.cast_le.mpr hnN
  · exact le_of_lt hε
lemma lemma29 (ε : ℝ) (N r : ℕ) (hε : ε > 0) (hε_small : ε < 1/100)  (hN : N ≥ 1) (hr : r ≥ 1) :
  ∑ n in radical_set r N, (1 : ℝ) / ((n : ℝ) ^ ε) ≥ ((radical_set r N).card : ℝ) / ((N : ℝ) ^ ε) := by
  -- We'll show the sum is at least card * (1/N^ε)
  have h_each_term : ∀ n ∈ radical_set r N, (1 : ℝ) / ((n : ℝ) ^ ε) ≥ 1 / ((N : ℝ) ^ ε) := by
    intros n hn
    -- Extract conditions from radical_set membership
    rw [radical_set, Finset.mem_filter] at hn
    obtain ⟨hn_range, hn_rad⟩ := hn
    rw [Finset.mem_range] at hn_range
    -- n ≤ N since n < N + 1
    have hn_le_N : n ≤ N := Nat.lt_succ_iff.mp hn_range
    -- n ≥ 1 since rad n = r and r ≥ 1
    have hn_pos : 1 ≤ n := by
      by_contra h
      push_neg at h
      have : n = 0 := by omega
      rw [this] at hn_rad
      simp [rad] at hn_rad
      -- If n = 0, then rad 0 = 0, but we have rad n = r and r ≥ 1
      rw [← hn_rad] at hr
      omega
    exact lemma28 ε n N hε hε_small hn_pos hn_le_N

  -- The sum of 1/N^ε repeated card times equals card * (1/N^ε)
  have sum_const : (∑ n in radical_set r N, (1 : ℝ) / ((N : ℝ) ^ ε)) = (radical_set r N).card * (1 / ((N : ℝ) ^ ε)) := by
    rw [Finset.sum_const]
    simp [nsmul_eq_mul]

  -- Since each term is at least 1/N^ε, the sum is at least the sum of 1/N^ε
  have : (∑ n in radical_set r N, (1 : ℝ) / ((n : ℝ) ^ ε)) ≥ (∑ n in radical_set r N, (1 : ℝ) / ((N : ℝ) ^ ε)) := by
    apply Finset.sum_le_sum
    exact h_each_term

  rw [sum_const] at this
  -- Convert card * (1/N^ε) to card / N^ε
  have eq : ((radical_set r N).card : ℝ) * (1 / ((N : ℝ) ^ ε)) = ((radical_set r N).card : ℝ) / ((N : ℝ) ^ ε) := by
    ring
  rw [← eq]
  exact this

lemma geometric_series_helper (x : ℝ) (hx_pos : 0 < x) (hx_lt_one : x < 1) : (1 - x)⁻¹ = 1 / (1 - x) := by
  exact inv_eq_one_div (1 - x)

theorem geometric_series (x : ℝ) (hx_pos : 0 < x) (hx_lt_one : x < 1) : ∑' (a : ℕ), x ^ (a + 1) = x / (1 - x) := by
  -- First establish that 0 ≤ x
  have hx_nonneg : 0 ≤ x := le_of_lt hx_pos

  -- We know that ∑' (n : ℕ), x ^ n = (1 - x)⁻¹
  have h_geom : ∑' (n : ℕ), x ^ n = (1 - x)⁻¹ :=
    tsum_geometric_of_lt_one hx_nonneg hx_lt_one

  -- The key insight: ∑' (a : ℕ+), x ^ (a : ℕ) = (∑' (n : ℕ), x ^ n) - 1
  -- since the sum over ℕ+ is x + x² + x³ + ... and the sum over ℕ is 1 + x + x² + x³ + ...
  have h_split : ∑' (a : ℕ), x ^ (a + 1) = (∑' (n : ℕ), x ^ n) - 1 := by
    -- Use the lemma about sums over ℕ+ vs ℕ
    have summable : Summable (fun n : ℕ => x ^ n) := summable_geometric_of_lt_one hx_nonneg hx_lt_one
    rw [tsum_eq_zero_add summable]
    simp

  rw [h_split, h_geom]

  -- Now we need to show (1 - x)⁻¹ - 1 = x / (1 - x)
  -- Use geometric_series_helper: (1 - x)⁻¹ = 1 / (1 - x)
  rw [geometric_series_helper x hx_pos hx_lt_one]

  -- Show that 1 / (1 - x) - 1 = x / (1 - x)
  have h_ne_zero : 1 - x ≠ 0 := by linarith [hx_lt_one]
  field_simp [h_ne_zero]

lemma lemma35 (ε : ℝ) (p : ℕ) (hε : ε > 0) (hε_small : ε < 1/100)  (hp_prime : p.Prime) :
  ∑' (a : ℕ), (1 : ℝ) / ((p : ℝ) ^ ((a + 1) * ε)) = 1 / ((p : ℝ) ^ ε - 1) := by
  -- Rewrite the sum using properties of exponents
  have h_rewrite : ∑' (a : ℕ), (1 : ℝ) / ((p : ℝ) ^ ((a + 1) * ε)) =
                   ∑' (a : ℕ), ((1 : ℝ) / ((p : ℝ) ^ ε)) ^ (a + 1) := by
    congr 1
    ext a
    -- Show: 1 / p^(a*ε) = (1/p^ε)^a
    have h1 : (p : ℝ) ^ ((a + 1) * ε) = ((p : ℝ) ^ ε) ^ (a + 1) := by
      rw [mul_comm (a + 1 : ℝ) ε]
      rw [Real.rpow_mul (Nat.cast_nonneg p)]
      rw [← Real.rpow_natCast]
      simp
    rw [h1]
    -- Now use the fact that 1 / x^n = (1/x)^n
    have h2 : (1 : ℝ) / ((p : ℝ) ^ ε) ^ (a + 1) = ((1 : ℝ) / (p : ℝ) ^ ε) ^ (a + 1) := by
      rw [div_pow, one_pow]
    exact h2

  rw [h_rewrite]

  -- Set x = 1 / p^ε
  let x := (1 : ℝ) / ((p : ℝ) ^ ε)

  -- Show that 0 < x < 1
  have hx_pos : 0 < x := by
    unfold x
    apply div_pos
    · norm_num
    · apply Real.rpow_pos_of_pos
      exact Nat.cast_pos.mpr (Nat.Prime.pos hp_prime)

  have hx_lt_one : x < 1 := by
    unfold x
    rw [div_lt_one]
    · apply Real.one_lt_rpow
      · exact Nat.one_lt_cast.mpr (Nat.Prime.one_lt hp_prime)
      · exact hε
    · apply Real.rpow_pos_of_pos
      exact Nat.cast_pos.mpr (Nat.Prime.pos hp_prime)

  -- Apply geometric series formula
  have h_geo := geometric_series x hx_pos hx_lt_one -- <- here

  -- Show that our sum equals the geometric series result
  rw [show ∑' (a : ℕ), (1 / (p : ℝ) ^ ε) ^ (a + 1) = ∑' (a : ℕ), x ^ (a + 1) from rfl]
  rw [h_geo]

  -- Simplify x / (1 - x) = 1 / (p^ε - 1)
  unfold x
  have hp_pow_pos : 0 < (p : ℝ) ^ ε := Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.Prime.pos hp_prime)) ε
  have hp_pow_ne_zero : (p : ℝ) ^ ε ≠ 0 := ne_of_gt hp_pow_pos
  have hp_pow_gt_one : 1 < (p : ℝ) ^ ε := Real.one_lt_rpow (Nat.one_lt_cast.mpr (Nat.Prime.one_lt hp_prime)) hε
  have hp_pow_ne_one : (p : ℝ) ^ ε ≠ 1 := ne_of_gt hp_pow_gt_one

  field_simp [hp_pow_ne_zero, hp_pow_ne_one]

lemma lemma36 (ε : ℝ) (s : Finset ℕ) (hε : ε > 0) (hε_small : ε < 1/100)  (hs_prime : ∀ p ∈ s, p.Prime) :
  ∏ p in s, (∑' (a : ℕ), (1 : ℝ) / ((p : ℝ) ^ ((a + 1) * ε))) = ∏ p in s, (1 : ℝ) / ((p : ℝ) ^ ε - 1) :=  by
  apply Finset.prod_congr rfl
  intros p hp
  exact lemma35 ε p hε hε_small (hs_prime p hp)
lemma lemma37 (ε : ℝ) (s : Finset ℕ) (hε : ε > 0) (hε_small : ε < 1/100)  (hs_prime : ∀ p ∈ s, p.Prime) :
  (∏ p in s, (1 : ℝ) / ((p : ℝ) ^ ε - 1)) =
  (∏ p in s.filter (fun (p : ℕ) => (p : ℝ) ^ ε ≥ 2), (1 : ℝ) / ((p : ℝ) ^ ε - 1)) *
  (∏ p in s.filter (fun (p : ℕ) => (p : ℝ) ^ ε < 2), (1 : ℝ) / ((p : ℝ) ^ ε - 1)) := by
  rw [← Finset.prod_filter_mul_prod_filter_not s (fun p => (p : ℝ) ^ ε ≥ 2)]
  congr 2
  ext p
  simp only [Finset.mem_filter, Finset.mem_filter]
  constructor
  · intro ⟨hp_mem, hp_not⟩
    exact ⟨hp_mem, not_le.mp hp_not⟩
  · intro ⟨hp_mem, hp_lt⟩
    exact ⟨hp_mem, not_le.mpr hp_lt⟩

-- The set of interest: natural numbers whose prime factors are exactly the set `s`.
-- def target_set (s : Finset ℕ) : Set ℕ :=
--   { m : ℕ | m.primeFactors = s ∧ m ≥ 1 ∧ ∀ p ∈ s, m.factorization p ≥ 1 }

-- The set of exponent functions: maps each prime in `s` to a positive integer exponent.
def exponent_functions (s : Finset ℕ) : Type :=
  { f : s → ℕ // ∀ p : s, f p ≥ 1 }

/--
The forward map ` φ` from a number in `target_set s` to its
corresponding exponent function. It maps a number `n` to the function
`p ↦ n.factorization p`.
-/
def map_to_exponents (s : Finset ℕ) (n : target_set s) : exponent_functions s := by
  --The function maps each prime `p` in `s` to its exponent in `n`'s factorization.
  let f : s → ℕ := fun (p : s) => n.val.factorization p.val

  -- We must prove that this function is valid, i.e., all exponents are >= 1.
  have h_f_valid : ∀ (p : s), f p ≥ 1 := by
    intro p
    -- The proof comes directly from the definition of `target_set`.
    -- `n.property` is the proof that `n.val` is in `target_set s`.
    -- `n.property.2` is the assertion `∀ p ∈ s, n.val.factorization p ≥ 1`.
    -- Since `p : s`, `p.val ∈ s` is true by `p.property`.
    exact n.property.2.2 p.val p.property

  -- Construct the subtype element (the function packaged with its validity proof).
  exact ⟨f, h_f_valid⟩

/--
Lemma: The forward map `map_to_exponents` is injective.

Proof Idea: If two numbers `n₁` and `n₂` map to the same exponent function,
it means they have the same factorization for every prime in `s`. Since their
set of prime factors is `s`, their factorization is zero for any prime not in `s`.
Thus, they have the same factorization for all primes, and since they are positive,
they must be the same number.
-/
lemma map_to_exponents_injective (s : Finset ℕ) (hs_prime : ∀ p ∈ s, p.Prime) :
  Function.Injective (map_to_exponents s) := by
    -- To prove injectivity, assume two elements map to the same value
  intro ⟨n₁, hn₁⟩ ⟨n₂, hn₂⟩ h_eq
  -- We need to show that n₁ = n₂
  simp only [Subtype.mk_eq_mk]

  -- From h_eq, we know the exponent functions are equal
  have h_exp_eq : ∀ p : s, n₁.factorization p.val = n₂.factorization p.val := by
    intro p
    -- Extract the equality from h_eq
    have : (map_to_exponents s ⟨n₁, hn₁⟩).val p = (map_to_exponents s ⟨n₂, hn₂⟩).val p := by
      rw [h_eq]
    -- Simplify the definition of map_to_exponents
    exact this

  -- Now we need to show n₁ = n₂ using the fact that they have the same factorization
  -- First, show they have the same factorization for all primes
  have h_all_primes : ∀ p : ℕ, n₁.factorization p = n₂.factorization p := by
    intro p
    by_cases hp : p ∈ s
    -- Case 1: p is in s
    · have : ∃ ps : s, ps.val = p := ⟨⟨p, hp⟩, rfl⟩
      obtain ⟨ps, hps⟩ := this
      rw [← hps]
      exact h_exp_eq ps
    -- Case 2: p is not in s
    · -- For p not in s, we need to show factorization is 0
      -- Use that p ∉ n₁.primeFactors (which equals s)
      have hp₁ : p ∉ n₁.primeFactors := by
        rw [hn₁.1]
        exact hp
      have hp₂ : p ∉ n₂.primeFactors := by
        rw [hn₂.1]
        exact hp
      -- Use that support of factorization equals primeFactors
      rw [← Nat.support_factorization] at hp₁ hp₂
      -- If p is not in support, then factorization p = 0
      rw [Finsupp.not_mem_support_iff] at hp₁ hp₂
      rw [hp₁, hp₂]

  -- Use the fact that numbers with the same factorization are equal
  have h_pos₁ : n₁ ≠ 0 := by
    have : n₁ ≥ 1 := hn₁.2.1
    omega
  have h_pos₂ : n₂ ≠ 0 := by
    have : n₂ ≥ 1 := hn₂.2.1
    omega
  exact Nat.eq_of_factorization_eq h_pos₁ h_pos₂ h_all_primes

/-
The fundamental theorem of arithmetic states that any integer n > 0 can be
written as a product of prime powers. This lemma formalizes that fact.
The expression `n.primeFactors` is the set of prime factors of `n`,
and `n.factorization p` is the exponent of the prime `p` in the factorization of `n`.
-/
lemma prod_primeFactors_pow_factorization_eq_self (n : ℕ) (hn : n ≠ 0) :
    ∏ p ∈ n.primeFactors, p ^ n.factorization p = n := by
  -- Use the theorem that relates product over factorization to product over primeFactors
  rw [← Nat.prod_factorization_eq_prod_primeFactors]
  -- Now apply the fundamental theorem that says n.factorization.prod (· ^ ·) = n
  exact Nat.factorization_prod_pow_eq_self hn

/--
Lemma: The forward map `map_to_exponents` is surjective.

Proof Idea: For any valid exponent function `f`, we can construct a number `n` by
taking the product of `p ^ f(p)` for all `p` in `s`. We then need to prove that
this `n` is in `target_set s` and that it maps back to `f`.
-/
lemma map_to_exponents_surjective (s : Finset ℕ) (hs_prime : ∀ p ∈ s, p.Prime) :
  Function.Surjective (map_to_exponents s) := by
  intro f
  -- Convert f to a finitely supported function
  let g : ℕ →₀ ℕ := {
    support := s
    toFun := fun p => if h : p ∈ s then f.val ⟨p, h⟩ else 0
    mem_support_toFun := by
      intro p
      simp only [Finset.mem_coe, ne_eq]
      constructor
      · intro hp
        simp only [hp, ↓reduceIte]
        -- Show f.val ⟨p, hp⟩ ≠ 0
        apply ne_of_gt
        exact f.property ⟨p, hp⟩
      · intro h
        by_contra h_not_in_s
        simp only [h_not_in_s, ↓reduceIte] at h
        exact h rfl
  }

  -- Construct n using the finitely supported function
  let n := g.prod (· ^ ·)

  -- Show n ≠ 0
  have hn_ne_zero : n ≠ 0 := by
    simp only [n, Finsupp.prod_ne_zero_iff]
    intro p hp
    simp only [g, Finsupp.mem_support_iff, Finsupp.coe_mk] at hp
    have : p ∈ s := hp
    simp only [this, ↓reduceIte] at hp ⊢
    apply ne_of_gt
    apply Nat.pow_pos
    exact Nat.Prime.pos (hs_prime p this)

  -- Show n ≥ 1
  have hn_pos : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr hn_ne_zero

  -- Key lemma: the factorization of n equals g
  have h_factorization : n.factorization = g := by
    apply Nat.prod_pow_factorization_eq_self
    intro p hp
    simp only [g, Finsupp.mem_support_iff, Finsupp.coe_mk] at hp
    exact hs_prime p hp

  -- Show n.primeFactors = s
  have h_prime_factors : n.primeFactors = s := by
    ext p
    simp only [Nat.mem_primeFactors_of_ne_zero hn_ne_zero]
    constructor
    · intro ⟨hp_prime, hp_dvd⟩
      -- If p divides n, then p is in the support of n.factorization
      have : 0 < n.factorization p := by
        rw [Nat.pos_iff_ne_zero]
        intro h
        -- From h : n.factorization p = 0, we want to show False
        -- We know p ∣ n, so by the lemma, 1 ≤ n.factorization p
        have : 1 ≤ n.factorization p := by
          rwa [← Nat.Prime.dvd_iff_one_le_factorization hp_prime hn_ne_zero]
        -- But this contradicts h : n.factorization p = 0
        rw [h] at this
        exact Nat.not_succ_le_zero 0 this
      rw [h_factorization] at this
      simp only [g, Finsupp.coe_mk] at this
      split_ifs at this with h
      · exact h
      · simp at this
    · intro hp
      constructor
      · exact hs_prime p hp
      · -- Show p divides n using Nat.Prime.dvd_iff_one_le_factorization
        rw [Nat.Prime.dvd_iff_one_le_factorization (hs_prime p hp) hn_ne_zero]
        have : 1 ≤ n.factorization p := by
          rw [h_factorization]
          simp only [g, Finsupp.coe_mk, hp, ↓reduceIte]
          exact f.property ⟨p, hp⟩
        exact this

  -- Show that for all p ∈ s, n.factorization p ≥ 1
  have h_factorization_ge : ∀ p ∈ s, n.factorization p ≥ 1 := by
    intro p hp
    rw [h_factorization]
    simp only [g, Finsupp.coe_mk, hp, ↓reduceIte]
    exact f.property ⟨p, hp⟩

  -- Create the element of target_set s
  let n_in_target : target_set s := ⟨n, h_prime_factors, hn_pos, h_factorization_ge⟩

  -- Show that map_to_exponents s n_in_target = f
  use n_in_target
  apply Subtype.ext
  funext p
  simp only [map_to_exponents, n_in_target]
  -- We need to show n.factorization p.val = f.val p
  rw [h_factorization]
  simp only [g, Finsupp.coe_mk]
  have : p.val ∈ s := p.property
  simp only [this, ↓reduceIte]
  -- Need to show f.val ⟨p.val, p.property⟩ = f.val p
  congr

theorem bijection_target_set_functions_h (s : Finset ℕ) (hs_prime : ∀ p ∈ s, p.Prime) :
  ∃ (φ : target_set s ≃ exponent_functions s),
    ∀ n : target_set s, (n : ℕ) = ∏ p : s, p.val ^ (φ n).val p := by
  -- Let `φ` be our forward map.
  let φ := map_to_exponents s

  -- We can construct an equivalence (a bijection, `≃`) from a function
  -- that is both injective and surjective.
  let φ_equiv := Equiv.ofBijective φ ⟨
    map_to_exponents_injective s hs_prime,
    map_to_exponents_surjective s hs_prime
  ⟩

  -- This equivalence is the one whose existence we want to prove.
  use φ_equiv

  -- Now, we prove the second part of the theorem: the reconstruction property.
  intro n
  -- We need to show that `n.val` is equal to the product of its prime powers.
  -- This is a direct consequence of the Fundamental Theorem of Arithmetic,
  -- captured in mathlib as `Nat.prod_primeFactors_pow_factorization`.
  -- First, we need that n.val is not zero.
  have hn_ne_zero : n.val ≠ 0 := by
    have := n.property.2.1
    linarith
  dsimp [φ_equiv]
  dsimp [φ]
  dsimp [map_to_exponents]
  dsimp [target_set] at n
  cases' n with n n_property
  cases' n_property with np1 np2
  cases' np2 with np2 np3
  simp [*]
  rw [← np1]
  symm
  -- Apply the reconstruction theorem.
  apply prod_primeFactors_pow_factorization_eq_self
  simp [hn_ne_zero]

lemma bijection_target_set_functions (s : Finset ℕ) (hs_prime : ∀ p ∈ s, p.Prime) :
  ∃ (φ : target_set s ≃ { f : s → ℕ // ∀ p : s, f p ≥ 1 }),
    ∀ n : target_set s, (n : ℕ) = ∏ p : s, p.val ^ (φ n).val p := by
    exact bijection_target_set_functions_h s hs_prime


lemma sum_over_target_set_eq_sum_over_functions (s : Finset ℕ) (ε : ℝ) (hε : ε > 0) (hs_prime : ∀ p ∈ s, p.Prime) :
  ∑' (n : target_set s), (1 : ℝ) / ((n : ℝ) ^ ε) =
  ∑' (f : { f : s → ℕ // ∀ p : s, f p ≥ 1 }), ∏ p : s, (1 : ℝ) / ((p : ℝ) ^ (f.val p * ε)) := by
  -- Get the bijection from bijection_target_set_functions
  obtain ⟨φ, hφ⟩ := bijection_target_set_functions s hs_prime

  -- Use that φ is a bijection to rewrite the sum
  rw [← Equiv.tsum_eq φ]
  -- Now we need to show that for each n, 1/(n:ℝ)^ε = ∏ p, 1/p^((φ n) p * ε)
  congr 1
  ext n

  -- By hφ, we have (n : ℕ) = ∏ p, p ^ (φ n) p
  have h_n : (n : ℕ) = ∏ p : s, p.val ^ (φ n).val p := hφ n

  -- Show 1/(n:ℝ)^ε = ∏ p, 1/p^((φ n) p * ε)
  rw [h_n]

  -- Handle the cast and exponent
  have h_rpow : ((∏ p : s, p.val ^ (φ n).val p : ℕ) : ℝ) ^ ε = ∏ p : s, (p.val : ℝ) ^ ((φ n).val p * ε) := by
    -- Cast the natural number product to real
    rw [Nat.cast_prod]
    -- Use the fact that (∏ x_i)^ε = ∏ x_i^ε for nonnegative x_i
    rw [← Real.finset_prod_rpow]
    · congr 1
      ext p
      -- Show (p^((φ n) p))^ε = p^((φ n) p * ε)
      rw [Nat.cast_pow]
      rw [← Real.rpow_natCast (p.val : ℝ) ((φ n).val p)]
      rw [← Real.rpow_mul (Nat.cast_nonneg _)]
    · -- All terms are nonnegative
      intro p _
      exact Nat.cast_nonneg _

  -- Apply the exponent rule
  rw [h_rpow]
  -- Show 1 / ∏ p^((φ n) p * ε) = ∏ 1/p^((φ n) p * ε)
  rw [one_div, ← Finset.prod_inv_distrib]
  simp_rw [one_div]

lemma reindex_sum_positive_to_nat (p : ℕ) (ε : ℝ) (hp : p.Prime) (hε : ε > 0) :
  ∑' (a : { a : ℕ // a ≥ 1 }), (1 : ℝ) / ((p : ℝ) ^ (a * ε)) =
  ∑' (a : ℕ), (1 : ℝ) / ((p : ℝ) ^ ((a + 1) * ε)) := by
  -- Define the equivalence e : { a : ℕ // a ≥ 1 } ≃ ℕ
  let e : { a : ℕ // a ≥ 1 } ≃ ℕ := {
    toFun := fun a => a.val - 1
    invFun := fun b => ⟨b + 1, by simp⟩
    left_inv := by
      intro a
      ext
      simp
      have h : a.val ≥ 1 := a.property
      omega
    right_inv := by intro b; simp
  }

  -- Use the symmetry of the equivalence
  -- e.symm : ℕ ≃ { a : ℕ // a ≥ 1 } maps b ↦ ⟨b + 1, _⟩
  have h_eq : ∑' (a : { a : ℕ // a ≥ 1 }), (1 : ℝ) / ((p : ℝ) ^ (a * ε)) =
              ∑' (b : ℕ), (1 : ℝ) / ((p : ℝ) ^ ((e.symm b) * ε)) := by
    exact (Equiv.tsum_eq e.symm (fun a => (1 : ℝ) / ((p : ℝ) ^ (a * ε)))).symm

  rw [h_eq]
  congr 1
  ext b
  -- e.symm b = ⟨b + 1, _⟩, so (e.symm b).val = b + 1
  have h_val : (e.symm b).val = b + 1 := rfl
  -- Now we need to handle the coercions carefully
  -- In the goal, (e.symm b) * ε means ↑↑(e.symm b) * ε = ((e.symm b).val : ℝ) * ε
  simp only [h_val]
  -- Now we need to show: 1 / p ^ (↑(b + 1) * ε) = 1 / p ^ ((↑b + 1) * ε)
  -- Use Nat.cast_add to convert ↑(b + 1) to ↑b + ↑1, then simplify ↑1 to 1
  congr 2
  simp only [Nat.cast_add, Nat.cast_one]


lemma summable_geometric_series_of_p_gt_1
    (p : ℕ) (ε : ℝ) (hp : p > 1) (hε : ε > 0) :
    Summable (fun (a : { a : ℕ // a ≥ 1 }) => (1 : ℝ) / (p : ℝ) ^ (a.val * ε)) := by
  -- Step 1: Rewrite 1 / p^(a.val * ε) as (1 / p^ε)^a.val
  have h_rewrite : ∀ a : { a : ℕ // a ≥ 1 }, (1 : ℝ) / (p : ℝ) ^ (a.val * ε) = ((1 : ℝ) / (p : ℝ) ^ ε) ^ a.val := by
    intro a
    rw [div_pow, one_pow]
    congr 1
    -- Need to show p^(a.val * ε) = (p^ε)^a.val
    rw [mul_comm (a.val : ℝ) ε]
    rw [← Real.rpow_mul_natCast]
    linarith

  -- Step 2: Set x = 1 / p^ε and show 0 < x < 1
  set x := (1 : ℝ) / (p : ℝ) ^ ε with hx_def

  have hp_pos : (0 : ℝ) < p := by
    norm_cast
    linarith

  have hx_pos : 0 < x := by
    rw [hx_def]
    apply div_pos one_pos
    apply Real.rpow_pos_of_pos hp_pos

  have hx_lt_one : x < 1 := by
    rw [hx_def, div_lt_one]
    · -- Show 1 < p^ε
      have hp_one : (1 : ℝ) < p := by norm_cast
      -- Since p > 1 and ε > 0, we have p^ε > p^0 = 1
      calc (1 : ℝ) = (p : ℝ) ^ (0 : ℝ) := by rw [Real.rpow_zero]
                  _ < (p : ℝ) ^ ε := by
                    apply Real.rpow_lt_rpow_of_exponent_lt hp_one
                    exact hε
    · apply Real.rpow_pos_of_pos hp_pos

  -- Step 3: Rewrite the sum using h_rewrite
  simp_rw [h_rewrite]

  -- Step 4: Show summability
  -- We'll show this is summable by using the fact that x^(n+1) is summable for n : ℕ
  have h_summable : Summable (fun n : ℕ => x ^ (n + 1)) := by
    -- x^(n+1) = x * x^n
    have : (fun n : ℕ => x ^ (n + 1)) = (fun n : ℕ => x * x ^ n) := by
      ext n
      rw [pow_succ, mul_comm]
    rw [this]
    exact Summable.mul_left x (summable_geometric_of_lt_one (le_of_lt hx_pos) hx_lt_one)

  -- Now we need to relate the sum over { a : ℕ // a ≥ 1 } to the sum over ℕ
  -- Define a bijection between ℕ and { a : ℕ // a ≥ 1 }
  let equiv : ℕ ≃ { a : ℕ // a ≥ 1 } := {
    toFun := fun n => ⟨n + 1, Nat.succ_pos n⟩
    invFun := fun a => a.val - 1
    left_inv := fun n => by simp
    right_inv := fun a => by
      ext
      simp
      exact Nat.sub_add_cancel a.property
  }

  -- Show that our function equals the composition
  have h_eq : (fun a : { a : ℕ // a ≥ 1 } => x ^ a.val) = (fun n : ℕ => x ^ (n + 1)) ∘ equiv.symm := by
    ext a
    simp only [Function.comp_apply]
    congr 1
    -- Need to show a.val = equiv.symm a + 1
    have : equiv.symm a = a.val - 1 := rfl
    rw [this]
    exact (Nat.sub_add_cancel a.property).symm

  rw [h_eq]
  exact h_summable.comp_injective equiv.symm.injective
noncomputable def equiv_reindex_choice_functions
    {ι : Type u} (β : ι → Type v)
    [DecidableEq ι] {j : ι} (s : Finset ι) (hjs : j ∉ s) :
    -- The type we are mapping from: a function on `s` and a value at `j`
    ((i : s) → β i.1) × β j ≃
    -- The type we are mapping to: a single function on `insert j s`
    ((i : {x // x ∈ insert j s}) → β i.1) :=
{
  -- The forward function: from a pair (f, x) to a single function g.
  -- We use `dite` (dependent if-then-else) which is what `if h : ...` elaborates to.
  -- If the input index `i` is `j`, we return `x`.
  -- Otherwise, `i` must be in `s`, so we can apply `f`.
  toFun := fun ⟨f, x⟩ ⟨i, hi⟩ =>
    if h : i = j then
      by {simp [h] at *; exact x }
    else
      f ⟨i, (Finset.mem_insert.mp hi).resolve_left h⟩,

  -- The inverse function: from a single function g to a pair (f, x).
  -- The function `f` on `s` is just `g` restricted to `s`.
  -- The value `x` at `j` is just `g` evaluated at `j`.
  invFun := fun g =>
    ( (fun i => g ⟨i, Finset.mem_insert_of_mem i.2⟩),
      g ⟨j, Finset.mem_insert_self j s⟩ ),

  -- Proof that invFun ∘ toFun = id
  left_inv := by
    -- We want to prove equality for any input pair `⟨f, x⟩`.
    intro ⟨f, x⟩
    -- The goal is an equality of pairs, so we use `Prod.ext` to split it into two goals.
    apply Prod.ext
    -- Goal 1: Prove the first components (the functions on `s`) are equal.
    · funext i -- Use function extensionality. `i` is an element of the subtype `s`.
      -- `i.val ∈ s` and `j ∉ s` implies `i.val ≠ j`. `simp` can use this fact.
      grind
    -- Goal 2: Prove the second components (the values at `j`) are equal.
    · simp,

  -- Proof that toFun ∘ invFun = id
  right_inv := by
    -- We want to prove equality for any function `g`.
    intro g
    -- Use function extensionality for functions on `{x // x ∈ insert j s}`.
    funext ⟨i, hi⟩ -- The index `i` is from the subtype.
    -- Unfold the function definitions.
    simp
    -- The goal now contains an `if i = j then ... else ...`.
    -- The `split_ifs` tactic will create two subgoals, one assuming `i = j`
    -- and one assuming `i ≠ j`.
    split_ifs with h
    -- In both cases, the goal simplifies to something trivial.
    subst h
    simp
    rfl
}
theorem prod_equiv_of_emb {ι₁ ι₂ α} [CommMonoid α]
    (s₁ : Finset ι₁) (s₂ : Finset ι₂)
    (f : ι₁ → α) (g : ι₂ → α)
    (e : Function.Embedding ι₁ ι₂)
    (h_s : s₂ = s₁.map e)
    (h_f : ∀ i ∈ s₁, f i = g (e i)) :
    ∏ i ∈ s₁, f i = ∏ j ∈ s₂, g j := by
  -- First, substitute `f` with `g ∘ e` inside the product on the left.
  -- `Finset.prod_congr` requires the finsets to be the same (`rfl`) and a proof
  -- that the functions are equal for all elements in the finset (`h_f`).
  rw [Finset.prod_congr rfl h_f]

  -- Now the goal is `∏ i in s₁, g (e i) = ∏ j in s₂, g j`.
  -- We can re-index the product on the left using `Finset.prod_map`.
  -- `Finset.prod_map` states: `∏ i in s₁, g (e i) = ∏ j in (s₁.map e.toEmbedding), g j`
  have := @Finset.prod_map ι₁ α ι₂ _ s₁ e g
  change  ∏ x ∈ Finset.map e s₁, g x = ∏ x ∈ s₁, g (e x) at this
  rw [← this]

  -- Now the goal is `∏ j in s₁.map e.toEmbedding, g j = ∏ j in s₂, g j`.
  -- The hypothesis `h_s` says `s₂ = s₁.map e.toEmbedding`, so we can rewrite.
  rw [h_s]

lemma tsum_prod_insert {α β : Type*} [DecidableEq α] (f : α → β → ℝ) (a : α) (S : Finset α) (ha : a ∉ S) :
  ∑' g : ({ x // x ∈ insert a S } → β), ∏ s : { x // x ∈ insert a S }, f s.1 (g s) =
  ∑' p : β × ({ x // x ∈ S } → β), f a p.1 * ∏ s : { x // x ∈ S }, f s.1 (p.2 s) := by
  let e_swap := Equiv.prodComm β ({ x : α // x ∈ S } → β)
  let e_insert := @equiv_reindex_choice_functions α (fun _ => β) _ a S ha
  let e_total := e_swap.trans e_insert

  rw [← e_total.tsum_eq]
  refine tsum_congr (fun g_prod => ?_)
  dsimp[e_total, e_insert, e_swap, equiv_reindex_choice_functions, Equiv.prodComm, Equiv.trans]

  let F (s : α) := dite (s ∈ (insert a S)) (fun hs => f (s) (if hjeq : s = a then g_prod.1 else g_prod.2 ⟨s, by {
    have : ¬ s = a := by simp [*]
    rw [Finset.mem_insert] at hs
    cases' hs with h1 h2
    · contradiction
    · assumption
  }⟩)) (fun nhs => 0)

  have : f a g_prod.1 * ∏ s ∈ S.attach, f (↑s) (g_prod.2 s) = F a * ∏ x ∈ S, F x := by
    congr 1
    · simp [F, *]
    · let emb : {x // x ∈ S} ↪ α := ⟨fun ⟨x, _⟩ => x, by simp [Function.Injective]⟩
      -- Convert to products over S using prod_attach
      rw [← Finset.prod_attach (s := S) (f := F)]
      apply Finset.prod_congr rfl
      intro x hx
      simp only [F]
      have hxa : x.1 ≠ a := ne_of_mem_of_not_mem x.2 ha
      simp [hxa, Finset.mem_insert, x.2]

  rw [this]
  rw [← Finset.prod_insert ha (f := F)]
  have this3 : ∏ s ∈ (insert a S).attach, f (↑s) (if hjeq : ↑s = a then g_prod.1 else g_prod.2 ⟨↑s, by {
    cases' s with s1 hs
    simp [*]
    have : ¬ s1 = a := by simp [*]
    rw [Finset.mem_insert] at hs
    cases' hs with h1 h2
    · contradiction
    · assumption
  }⟩) = ∏ x ∈ insert a S, F x := by
    let emb : { x // x ∈ insert a S } ↪ α := ⟨fun ⟨x, _⟩ => x, by simp [Function.Injective]⟩
    -- Convert using prod_attach
    rw [← Finset.prod_attach (s := insert a S) (f := F)]
    apply Finset.prod_congr rfl
    intro x hx
    simp only [F, x.2]
    by_cases hxa : x.1 = a
    · simp [hxa]
    · simp [hxa]
  assumption

lemma tsum_prod_empty {α β : Type*} (f : α → β → ℝ) :
  ∑' g : ({ x : α // x ∈ (∅ : Finset α) } → β), ∏ s : { x : α // x ∈ (∅ : Finset α) }, f s.1 (g s) = 1 := by
  -- First, show that { x : α // x ∈ ∅ } is an empty type
  have h_empty : IsEmpty { x : α // x ∈ (∅ : Finset α) } := by
    constructor
    intro ⟨x, hx⟩
    exact absurd hx (Finset.not_mem_empty x)

  -- By Pi.uniqueOfIsEmpty, there's a unique function from an empty type to β
  haveI h_unique : Unique ({ x : α // x ∈ (∅ : Finset α) } → β) := Pi.uniqueOfIsEmpty _

  -- For any function g from the empty type to β, the product is 1
  have h_prod : ∀ g : { x : α // x ∈ (∅ : Finset α) } → β,
    ∏ s : { x : α // x ∈ (∅ : Finset α) }, f s.1 (g s) = 1 := by
    intro g
    -- The product over an empty type is 1
    rw [Fintype.prod_empty]

  -- Since every term in the tsum equals 1, we have a tsum of constants
  have h_const : ∀ g : { x : α // x ∈ (∅ : Finset α) } → β,
    (∏ s : { x : α // x ∈ (∅ : Finset α) }, f s.1 (g s)) = 1 := h_prod

  -- The tsum equals 1
  simp only [h_const]
  -- Now we have ∑' g : ({ x : α // x ∈ ∅ } → β), 1 = 1

  -- For a unique type that is also finite, we can use tsum_fintype
  haveI fintype_inst : Fintype ({ x : α // x ∈ (∅ : Finset α) } → β) := by
    -- A unique type is finite
    exact Fintype.ofFinite _

  -- The tsum of 1 over a finite type is the cardinality
  rw [tsum_fintype]
  simp only [Finset.sum_const, Finset.card_univ]
  -- Now we need: Fintype.card ({ x : α // x ∈ ∅ } → β) • 1 = 1
  -- This simplifies to: Fintype.card ({ x : α // x ∈ ∅ } → β) = 1
  simp only [nsmul_one]
  -- For a unique type, the cardinality is 1
  rw [Fintype.card_unique]
  -- Now we have ↑1 = 1, which is just a coercion
  simp



lemma tsum_prod_fintype_univ {α β : Type*} [Fintype α] (f : α → β → ℝ) :
  ∑' g : ({ x // x ∈ Finset.univ } → β), ∏ s : { x // x ∈ Finset.univ }, f s.1 (g s) =
  ∑' g : (α → β), ∏ a : α, f a (g a) := by
  -- Define the equivalence between { x // x ∈ Finset.univ } and α
  let e : { x // x ∈ Finset.univ } ≃ α := {
    toFun := fun ⟨x, _⟩ => x
    invFun := fun x => ⟨x, Finset.mem_univ x⟩
    left_inv := fun ⟨x, hx⟩ => by simp
    right_inv := fun x => by simp
  }

  -- Define the induced equivalence between function spaces
  let F : ({ x // x ∈ Finset.univ } → β) ≃ (α → β) := {
    toFun := fun g a => g (e.invFun a)
    invFun := fun g' s => g' (e.toFun s)
    left_inv := fun g => by
      ext s
      simp [e]
    right_inv := fun g' => by
      ext a
      simp [e]
  }

  -- The key lemma: for any g, the products are related by F
  have h_prod : ∀ g : { x // x ∈ Finset.univ } → β,
    ∏ s : { x // x ∈ Finset.univ }, f s.1 (g s) = ∏ a : α, f a (F g a) := by
    intro g
    -- Use Fintype.prod_equiv to reindex the product
    rw [← Fintype.prod_equiv e.symm (fun a => f a (F g a))]
    -- After reindexing, we need to show the products are equal
    congr 1
    intro s
    -- Show: f s.1 (g s) = f (e.symm (e s)) (F g (e s))
    -- We know e.symm (e s) = s and F g (e s) = g (e.invFun (e s)) = g s
    simp [F, e]

  -- Now use this to rewrite the left side
  simp_rw [h_prod]

  -- Apply Equiv.tsum_eq
  exact Equiv.tsum_eq F (fun g => ∏ a : α, f a (g a))


lemma prod_tsum_eq_tsum_prod_subtype
  {α β : Type*} [Fintype α] [DecidableEq α] (f : α → β → ℝ)
  (h_summable : ∀ a : α, Summable (f a))
  (h_sum_pos : ∀ a : α, ∑' b : β , f a b > 0)
  (h_pos : ∀ a : α, ∀ b : β , f a b > 0)
  (h_abs_summable : ∀ a : α, Summable (fun b => |f a b|)) :
  ∏ a : α, ∑' b, f a b = ∑' g : (α → β), ∏ a : α, f a (g a) := by
  -- We prove by induction on finite subsets
  suffices ∀ S : Finset α,
    ∏ s in S, ∑' b, f s b = ∑' g : ({ x // x ∈ S } → β), ∏ s : { x // x ∈ S }, f s.1 (g s) by
    -- Apply to Finset.univ
    have h := this Finset.univ
    -- Convert between { x // x ∈ Finset.univ } → β and α → β
    rw [h, tsum_prod_fintype_univ]

  -- Induction on S
  intro S
  induction S using Finset.induction with
  | empty =>
    -- Base case: S = ∅
    simp only [Finset.prod_empty]
    -- The sum over functions from ∅ to β equals 1
    rw [tsum_prod_empty]

  | @insert a S ha IH =>
    -- Inductive step
    rw [Finset.prod_insert ha, IH]
    -- Apply tsum_mul_tsum_of_summable_norm
    have ha_norm : Summable (fun b => ‖f a b‖) := by
      simpa [Real.norm_eq_abs] using h_abs_summable a
    -- Norm summability of the second series
    have hS_norm : Summable (fun g : ({ x // x ∈ S } → β) => ‖∏ s : { x // x ∈ S }, f s.1 (g s)‖) := by
      -- Following the informal proof and target_set_summable pattern
      by_contra h_not_summable
      -- If not summable, tsum would be 0
      have h_tsum_zero : ∑' g : ({ x // x ∈ S } → β), ‖∏ s : { x // x ∈ S }, f s.1 (g s)‖ = 0 :=
        tsum_eq_zero_of_not_summable h_not_summable

      -- Since all f values are positive, each product is positive
      -- and therefore norm equals the value itself
      have h_norm_eq_val : ∀ g : ({ x // x ∈ S } → β),
        ‖∏ s : { x // x ∈ S }, f s.1 (g s)‖ = ∏ s : { x // x ∈ S }, f s.1 (g s) := by
        intro g
        apply Real.norm_of_nonneg
        apply Finset.prod_nonneg
        intro s _
        exact le_of_lt (h_pos s.1 (g s))

      -- Rewrite the tsum using this equality
      simp_rw [h_norm_eq_val] at h_tsum_zero

      -- From IH, we know this sum equals a positive product
      rw [← IH] at h_tsum_zero

      -- The finite product is positive
      have h_prod_pos : 0 < ∏ s in S, ∑' b, f s b := by
        apply Finset.prod_pos
        intro s hs
        exact h_sum_pos s

      -- This is a contradiction
      linarith [h_prod_pos, h_tsum_zero]

    rw [tsum_mul_tsum_of_summable_norm ha_norm hS_norm]

    -- Use tsum_prod_insert to complete
    rw [tsum_prod_insert f a S ha]


lemma p_a_eps_pos
 {s : Finset ℕ} {ε : ℝ} (hs : ∀ p ∈ s, p > 1) (hε : ε > 0): ∀ (a : { x // x ∈ s }), ∀ (b : { a // a ≥ 1 }), 1 / (a : ℝ) ^ ((b : ℕ) * ε) > 0 := by
  intro a b
  -- We need to show 1 / a^(b * ε) > 0
  -- This is equivalent to showing a^(b * ε) > 0
  apply div_pos one_pos
  -- Now we need to show a^(b * ε) > 0
  -- First, we know a.val > 1 from the hypothesis
  have ha : a.val > 1 := hs a.val a.property
  -- As a real number, a > 0
  have ha_pos : (a.val : ℝ) > 0 := by
    norm_cast
    linarith [ha]
  -- The exponent b * ε is positive (though we don't need this fact directly)
  -- Since a > 0 as a real number, any real power of a is positive
  apply Real.rpow_pos_of_pos ha_pos

lemma tsum_p_a_eps_pos
 {s : Finset ℕ} {ε : ℝ} (hs : ∀ p ∈ s, p > 1) (hε : ε > 0): ∀ (a : { x // x ∈ s }), ∑' (b : { a // a ≥ 1 }), 1 / (a : ℝ) ^ ((b : ℕ) * ε) > 0 := by
  intro a
  -- From p_a_eps_pos, we know that every term is positive
  have h_pos : ∀ b : { a // a ≥ 1 }, 1 / (a : ℝ) ^ ((b : ℕ) * ε) > 0 := by
    intro b
    exact p_a_eps_pos hs hε a b

  -- We need summability
  have h_summable : Summable (fun b : { a // a ≥ 1 } => 1 / (a : ℝ) ^ ((b : ℕ) * ε)) := by
    have ha_gt_1 : a.val > 1 := hs a.val a.property
    exact summable_geometric_series_of_p_gt_1 a.val ε ha_gt_1 hε

  -- All terms are non-negative
  have h_nonneg : ∀ i : { a // a ≥ 1 }, 0 ≤ 1 / (a : ℝ) ^ ((i : ℕ) * ε) := by
    intro i
    exact le_of_lt (h_pos i)

  -- Create the element b=1
  let b₁ : { a : ℕ // a ≥ 1 } := ⟨1, le_refl 1⟩

  -- Apply tsum_pos with b₁
  apply tsum_pos h_summable h_nonneg b₁
  -- Prove that the b₁ term is positive
  exact p_a_eps_pos hs hε a b₁

lemma prod_of_tsums_eq_tsum_of_prods
    (s : Finset ℕ) (ε : ℝ) (hε : ε > 0) (hs : ∀ p ∈ s, p > 1) :
    ∏ p : s, (∑' (a : { a : ℕ // a ≥ 1 }), (1 : ℝ) / (p : ℝ) ^ (a.val * ε)) =
    ∑' (f : s → { a : ℕ // a ≥ 1 }), ∏ p : s, (1 : ℝ) / (p : ℝ) ^ ((f p).val * ε) := by
  -- First establish summability for each geometric series
  have h_summable : ∀ p ∈ s, Summable (fun (a : { a : ℕ // a ≥ 1 }) => (1 : ℝ) / (p : ℝ) ^ (a.val * ε)) := by
    intro p hp
    exact summable_geometric_series_of_p_gt_1 p ε (hs p hp) hε

  -- The equality follows from the general principle of interchanging
  -- finite products and infinite sums for absolutely convergent series

  -- First we need summability for the subtype version
  have h_summable' : ∀ p : s, Summable (fun (a : { a : ℕ // a ≥ 1 }) => (1 : ℝ) / (p.val : ℝ) ^ (a.val * ε)) := by
    intro ⟨p, hp⟩
    exact h_summable p hp

  -- And absolute summability
  have h_abs_summable' : ∀ p : s, Summable (fun a : { a : ℕ // a ≥ 1 } => |(1 : ℝ) / (p.val : ℝ) ^ (a.val * ε)|) := by
    intro ⟨p, hp⟩
    convert h_summable p hp using 1
    ext a
    simp only [abs_div, abs_one]
    rw [abs_of_pos]
    apply Real.rpow_pos_of_pos
    exact Nat.cast_pos.mpr (Nat.zero_lt_of_lt (hs p hp))

  have h_tsum_pos' : ∀ (a : { x // x ∈ s }), ∑' (b : { a // a ≥ 1 }), 1 / (a : ℝ) ^ ((b : ℕ) * ε) > 0 := by
    intro a
    -- Use the helper lemma to show positivity
    apply tsum_p_a_eps_pos
    . exact hs
    . exact hε
  have h_pos' : ∀ (a : { x // x ∈ s }), ∀ (b : { a // a ≥ 1 }), 1 / (a : ℝ) ^ ((b : ℕ) * ε) > 0 := by
    intro a b
    -- Use the helper lemma to show positivity
    apply p_a_eps_pos
    . exact hs
    . exact hε

  -- Apply the interchange theorem
  exact prod_tsum_eq_tsum_prod_subtype
    (fun (p : s) (a : { a : ℕ // a ≥ 1 }) => (1 : ℝ) / (p.val : ℝ) ^ (a.val * ε))
    h_summable'
    h_tsum_pos'
    h_pos'
    h_abs_summable'

lemma tsum_over_fun_subtype_equiv_tsum_over_pi
    (s : Finset ℕ) (ε : ℝ) :
    ∑' (f : { f : s → ℕ // ∀ p, f p ≥ 1 }), ∏ p : s, (1 : ℝ) / (p : ℝ) ^ (f.val p * ε) =
    ∑' (f : s → { a : ℕ // a ≥ 1 }), ∏ p : s, (1 : ℝ) / (p : ℝ) ^ ((f p).val * ε) := by
  -- Define the bijection between the two indexing sets
  -- From left to right: given f with property ∀ p, f p ≥ 1, construct g mapping to {a : ℕ // a ≥ 1}
  let to_fun : { f : s → ℕ // ∀ p, f p ≥ 1 } → (s → { a : ℕ // a ≥ 1 }) :=
    fun f p => ⟨f.val p, f.property p⟩

  -- From right to left: given g : s → {a : ℕ // a ≥ 1}, extract the underlying function
  let inv_fun : (s → { a : ℕ // a ≥ 1 }) → { f : s → ℕ // ∀ p, f p ≥ 1 } :=
    fun g => ⟨fun p => (g p).val, fun p => (g p).property⟩

  -- Verify this is a bijection by showing left and right inverses
  have left_inv : ∀ f, inv_fun (to_fun f) = f := by
    intro f
    -- Need to show equality of subtypes
    apply Subtype.ext
    rfl

  have right_inv : ∀ g, to_fun (inv_fun g) = g := by
    intro g
    -- Need to show equality of functions
    funext p
    -- The values are the same by construction
    rfl

  -- Create the equivalence
  let e : { f : s → ℕ // ∀ p, f p ≥ 1 } ≃ (s → { a : ℕ // a ≥ 1 }) :=
    ⟨to_fun, inv_fun, left_inv, right_inv⟩

  -- Apply the equivalence to transform the tsum
  rw [← Equiv.tsum_eq e]
  -- Now we need to show that the summand is preserved
  simp only [e]
  -- The product terms are identical since f.val p = (to_fun f p).val
  rfl


lemma tsum_prod_positive_functions (s : Finset ℕ) (ε : ℝ) (hε : ε > 0) (hs_prime : ∀ p ∈ s, p.Prime) :
∑' (f : { f : s → ℕ // ∀ p : s, f p ≥ 1 }), ∏ p : s, (1 : ℝ) / ((p : ℝ) ^ (f.val p * ε)) =
∏ p : s, ∑' (a : { a : ℕ // a ≥ 1 }), (1 : ℝ) / ((p : ℝ) ^ (a * ε)) := by
  -- First, we need to establish that all primes in s are > 1
  have hs : ∀ p ∈ s, p > 1 := fun p hp => Nat.Prime.one_lt (hs_prime p hp)

  -- Rewrite the RHS using prod_of_tsums_eq_tsum_of_prods
  rw [prod_of_tsums_eq_tsum_of_prods s ε hε hs]

  -- Rewrite the LHS using tsum_over_fun_subtype_equiv_tsum_over_pi
  rw [tsum_over_fun_subtype_equiv_tsum_over_pi s ε]

lemma tsum_prod_eq_prod_tsum (s : Finset ℕ) (ε : ℝ) (hε : ε > 0) (hs_prime : ∀ p ∈ s, p.Prime) :
  ∑' (n : target_set s), (1 : ℝ) / ((n : ℝ) ^ ε) = ∏ p ∈ s, ∑' (a : ℕ), (1 : ℝ) / ((p : ℝ) ^ ((a + 1) * ε)) := by

  -- Step 2: Rewriting the sum over target_set s in terms of the function f
  have h_rewrite := sum_over_target_set_eq_sum_over_functions s ε hε hs_prime
  rw [h_rewrite]

  -- Step 3: Using the distributive property to separate the sum into products
  have h_distribute := tsum_prod_positive_functions s ε hε hs_prime
  rw [h_distribute]

  -- Now I have: ∏ p : s, ∑' (a : { a : ℕ // a ≥ 1 }), (1 : ℝ) / ((p.val : ℝ) ^ (a.val * ε))
  -- I want: ∏ p ∈ s, ∑' (a : ℕ), (1 : ℝ) / ((p : ℝ) ^ ((a + 1) * ε))

  -- First, convert the product over the subtype to a product over membership
  conv_rhs => rw [← Finset.prod_attach s]

  -- Now both sides are products over p : s, so we can use prod_congr
  congr 1
  ext ⟨p, hp⟩
  simp only [Finset.coe_sort_coe]

  -- Apply the reindexing lemma
  exact reindex_sum_positive_to_nat p ε (hs_prime p hp) hε

lemma lemma33 (ε : ℝ) (s : Finset ℕ) (hε : ε > 0) (hε_small : ε < 1/100)  (hs_prime : ∀ p ∈ s, p.Prime) :
  ∑' (n : target_set s), (1 : ℝ) / ((n : ℝ) ^ ε) =   ∏ p ∈ s, (1 : ℝ) / ((p : ℝ) ^ ε - 1)
 := by
  rw [← lemma36 ε s hε hε_small hs_prime]
  exact tsum_prod_eq_prod_tsum s ε hε hs_prime

lemma summable_indicator_of_summable_subtype (t : Set ℕ) (f : ℕ → ℝ)
  (h : Summable (fun (m : t) => f (m : ℕ))) : Summable (t.indicator f) := by
  exact summable_subtype_iff_indicator.mp h

lemma finset_sum_le_tsum_of_subset (s : Finset ℕ) (t : Set ℕ) (f : ℕ → ℝ)
  (h_subset : ∀ n ∈ s, n ∈ t) (h_nonneg : ∀ n : ℕ, 0 ≤ f n)
  (h_summable : Summable (fun (m_subtype : t) => f (m_subtype : ℕ))) :
  ∑ n in s, f n ≤ ∑' (m : t), f (m : ℕ) := by
  classical
  -- Use tsum_subtype to rewrite the RHS in terms of indicator function
  have h_tsum : ∑' (m : t), f (m : ℕ) = ∑' n : ℕ, t.indicator f n := by
    exact tsum_subtype t f

  rw [h_tsum]

  -- Show that the sum over s is bounded by the sum over ℕ of the indicator
  have h_le : ∑ n in s, f n ≤ ∑' n : ℕ, t.indicator f n := by
    -- First show ∑ n in s, f n = ∑ n in s, t.indicator f n
    have h_eq : ∑ n in s, f n = ∑ n in s, t.indicator f n := by
      apply Finset.sum_congr rfl
      intro n hn
      simp only [Set.indicator]
      rw [if_pos (h_subset n hn)]

    rw [h_eq]

    -- Apply sum_le_tsum
    apply sum_le_tsum
    · intro n hn
      simp only [Set.indicator]
      split_ifs with h
      · exact h_nonneg n
      · exact le_refl 0
    · -- Show summability of indicator function using our added lemma
      exact summable_indicator_of_summable_subtype t f h_summable

  exact h_le

lemma target_set_summable (ε : ℝ) (s : Finset ℕ) (hε : ε > 0) (hε_small : ε < 1/100)  (hs_prime : ∀ p ∈ s, p.Prime) : Summable (fun n : target_set s => (1 : ℝ) / ((n : ℝ) ^ ε)) := by
  -- In lemma33 we showed that the sum equals a finite product
  have h_eq : ∑' (n : target_set s), (1 : ℝ) / ((n : ℝ) ^ ε) = ∏ p ∈ s, (1 : ℝ) / ((p : ℝ) ^ ε - 1) :=
    lemma33 ε s hε hε_small hs_prime

  -- Therefore, its value is finite and thus converges
  -- The key insight from the informal proof: since the sum equals a finite product, it converges
  -- This is a fundamental property that if tsum equals a finite value, the series is summable
  by_contra h_not_summable
  -- If not summable, then tsum would be 0 (for nonnegative terms)
  have h_nonneg : ∀ n : target_set s, 0 ≤ (1 : ℝ) / ((n : ℝ) ^ ε) := by
    intro n
    apply div_nonneg
    · norm_num
    · apply Real.rpow_nonneg
      exact Nat.cast_nonneg n

  have h_tsum_zero : ∑' (n : target_set s), (1 : ℝ) / ((n : ℝ) ^ ε) = 0 :=
    tsum_eq_zero_of_not_summable h_not_summable

  -- But this contradicts lemma33 when s is nonempty and the product is positive
  rw [h_eq] at h_tsum_zero
  -- The finite product is positive when s is nonempty
  by_cases h_empty : s = ∅
  · -- If s is empty, then the product is 1, contradicting tsum = 0
    simp [h_empty] at h_tsum_zero
  · -- If s is nonempty, then the product is positive, contradicting tsum = 0
    have h_prod_pos : 0 < ∏ p ∈ s, (1 : ℝ) / ((p : ℝ) ^ ε - 1) := by
      apply Finset.prod_pos
      intro p hp
      apply div_pos
      · norm_num
      · -- Show p^ε - 1 > 0
        have hp_prime : p.Prime := hs_prime p hp
        have hp_eps_gt_one : 1 < (p : ℝ) ^ ε := by
          apply Real.one_lt_rpow
          · exact Nat.one_lt_cast.mpr (Nat.Prime.one_lt hp_prime)
          · exact hε
        linarith [hp_eps_gt_one]
    linarith [h_prod_pos, h_tsum_zero]

lemma lemma31 (ε : ℝ) (N : ℕ) (r : ℕ) (hε : ε > 0) (hε_small : ε < 1/100)  (hN : N ≥ 1) (hr : r ≥ 1) (hr_sf : rad r = r) :
  ∑ n in radical_set r N, (1 : ℝ) / ((n : ℝ) ^ ε) ≤ ∑' (n : target_set r.primeFactors), (1 : ℝ) / ((n : ℝ) ^ ε) := by
  -- Following the informal proof strategy
  have hr_ne_zero : r ≠ 0 := by omega
  have h_primes : ∀ p ∈ r.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp

  -- Since r is squarefree, rad r = r.primeFactors.prod id
  have h_rad_prod : rad r = r.primeFactors.prod id := by
    rw [rad, if_neg hr_ne_zero]

  -- Combined with hr_sf: rad r = r, we get r = r.primeFactors.prod id
  have h_r_prod : r = r.primeFactors.prod id := by
    calc r
      _ = rad r := hr_sf.symm
      _ = r.primeFactors.prod id := h_rad_prod

  -- KEY INSIGHT from informal proof: subset relationship
  -- "any n ∈ R(r,N) must be of the form n = p₁^a₁⋯pₖ^aₖ for some integers a₁,...,aₖ ≥ 1"
  have h_subset : ∀ n ∈ radical_set r N, n ∈ target_set r.primeFactors := by
    intro n hn
    rw [radical_set, Finset.mem_filter] at hn
    obtain ⟨_, hn_rad⟩ := hn
    rw [h_r_prod] at hn_rad
    exact lemma26 r.primeFactors h_primes hn_rad

  -- POSITIVITY from informal proof: "Since all terms are positive"
  have h_nonneg : ∀ n : ℕ, 0 ≤ (1 : ℝ) / ((n : ℝ) ^ ε) := by
    intro n
    apply div_nonneg
    · norm_num
    · apply Real.rpow_nonneg; exact Nat.cast_nonneg n

  -- Apply the fundamental principle using our added lemma
  apply finset_sum_le_tsum_of_subset -- This now expects three hypotheses
  · exact h_subset -- The subset relation
  · exact h_nonneg -- The non-negativity of terms in the finite sum
  · -- The new Summable argument for the infinite sum:
    exact target_set_summable ε r.primeFactors hε hε_small h_primes
-- Lemma 32
lemma lemma32 (ε : ℝ) (p1 p2 : ℕ) (hε : ε > 0) (hε_small : ε < 1/100)  (hp1 : p1 ≥ 2) (hp2 : p2 ≥ 2) :
  ∑' (a1 : ℕ), ∑' (a2 : ℕ), (1 : ℝ) / (((p1 ^ (a1 + 1) * p2 ^ (a2 + 1)) : ℝ) ^ ε) =
  (∑' (a1 : ℕ), (1 : ℝ) / (((p1 ^ (a1 + 1)) : ℝ) ^ ε)) * (∑' (a2 : ℕ), (1 : ℝ) / (((p2 ^ (a2 + 1)) : ℝ) ^ ε)) := by
  -- Rewrite the expression inside the double sum
  have h1 : ∀ (a1 a2 : ℕ), (1 : ℝ) / (((p1 ^ (a1 + 1) * p2 ^ (a2 + 1)) : ℝ) ^ ε) =
    ((1 : ℝ) / (((p1 ^ (a1 + 1)) : ℝ) ^ ε)) * ((1 : ℝ) / (((p2 ^ (a2 + 1)) : ℝ) ^ ε)) := by
    intro a1 a2
    -- Use basic algebraic properties
    have h_cast : ((p1 ^ (a1 + 1) * p2 ^ (a2 + 1)) : ℝ) = (p1 ^ (a1 + 1) : ℝ) * (p2 ^ (a2 + 1) : ℝ) := by norm_cast
    have h_pos1 : (0 : ℝ) ≤ (p1 ^ (a1 + 1) : ℝ) := pow_nonneg (Nat.cast_nonneg p1) _
    have h_pos2 : (0 : ℝ) ≤ (p2 ^ (a2 + 1) : ℝ) := pow_nonneg (Nat.cast_nonneg p2) _
    rw [h_cast, Real.mul_rpow h_pos1 h_pos2]
    rw [mul_comm ((p1 ^ (a1 + 1) : ℝ) ^ ε) ((p2 ^ (a2 + 1) : ℝ) ^ ε)]
    rw [one_div_mul_one_div_rev]

  simp_rw [h1]

  -- Factor out the inner sum since it doesn't depend on a1
  calc ∑' (a1 : ℕ), ∑' (a2 : ℕ), (1 : ℝ) / (((p1 ^ (a1 + 1)) : ℝ) ^ ε) * ((1 : ℝ) / (((p2 ^ (a2 + 1)) : ℝ) ^ ε))
    _ = ∑' (a1 : ℕ), ((1 : ℝ) / (((p1 ^ (a1 + 1)) : ℝ) ^ ε)) * ∑' (a2 : ℕ), ((1 : ℝ) / (((p2 ^ (a2 + 1)) : ℝ) ^ ε)) := by
      congr 1; ext a1; rw [← tsum_mul_left]
    _ = (∑' (a1 : ℕ), (1 : ℝ) / (((p1 ^ (a1 + 1)) : ℝ) ^ ε)) * (∑' (a2 : ℕ), (1 : ℝ) / (((p2 ^ (a2 + 1)) : ℝ) ^ ε)) := by
      rw [← tsum_mul_right]

lemma lemma38 (p : ℕ) (ε : ℝ) (hp : p.Prime) (hε : ε > 0) (hε_small : ε < 1/100)  (hpε : (p : ℝ) ^ ε ≥ 2) :
  1 / ((p : ℝ) ^ ε - 1) ≤ 1 := by
  rw [div_le_one]
  · linarith [hpε]
  · linarith [hpε]
lemma lemma39 (ε : ℝ) (s : Finset ℕ) (hε : ε > 0) (hε_small : ε < 1/100)  (hs_prime : ∀ p ∈ s, p.Prime) :
  let s_ge_two := s.filter (fun (p : ℕ) => (p : ℝ) ^ ε ≥ 2)
  ∏ p in s_ge_two, (1 : ℝ) / ((p : ℝ) ^ ε - 1) ≤ 1 := by
  apply Finset.prod_le_one
  · intro p hp
    apply div_nonneg
    · norm_num
    · have h : (p : ℝ) ^ ε ≥ 2 := (Finset.mem_filter.mp hp).2
      linarith
  · intro p hp
    apply lemma38
    · exact hs_prime p (Finset.mem_of_mem_filter _ hp)
    · exact hε
    · exact hε_small
    · exact (Finset.mem_filter.mp hp).2
lemma lemma40 (ε : ℝ) (hε : ε > 0) (hε_small : ε < 1/100)  : 1 / ((2 : ℝ) ^ ε - 1) ≤ 2 / ε := by
  have h1 : (2 : ℝ) ^ ε ≥ ε / 2 + 1 := two_rpow_ge_half_add_one ε hε.le
  have h2 : (2 : ℝ) ^ ε - 1 ≥ ε / 2 := by linarith
  have h3 : ε / 2 > 0 := by linarith
  have h4 : (2 : ℝ) ^ ε - 1 > 0 := by linarith
  have h5 : 1 / ((2 : ℝ) ^ ε - 1) ≤ 1 / (ε / 2) := by
    rw [one_div_le_one_div h4 h3]
    exact h2
  rw [one_div_div] at h5
  exact h5

lemma lemma41 (p : ℕ) (ε : ℝ) (hp : p ≥ 2) (hε : ε > 0) (hε_small : ε < 1/100)  (hpε : (p : ℝ) ^ ε < 2) :
  1 / ((p : ℝ) ^ ε - 1) ≤ 2 / ε := by
  have hp_ge_two : (p : ℝ) ≥ 2 := by
    norm_cast
  have h_pow_monotone : (2 : ℝ) ^ ε ≤ (p : ℝ) ^ ε := by
    exact Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 2) hp_ge_two (le_of_lt hε)
  have h_sub_monotone : (2 : ℝ) ^ ε - 1 ≤ (p : ℝ) ^ ε - 1 := by
    linarith
  have h_two_pow_sub_one_pos : 0 < (2 : ℝ) ^ ε - 1 := by
    have : 1 < (2 : ℝ) ^ ε := by
      have : 1 = (2 : ℝ) ^ (0 : ℝ) := by norm_num
      rw [this]
      exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) hε
    linarith
  have h_p_pow_sub_one_pos : 0 < (p : ℝ) ^ ε - 1 := by
    linarith [h_sub_monotone, h_two_pow_sub_one_pos]
  have h_inv_le : 1 / ((p : ℝ) ^ ε - 1) ≤ 1 / ((2 : ℝ) ^ ε - 1) := by
    have h_inv_eq : ∀ (x : ℝ), x⁻¹ = 1 / x := by intro x; exact inv_eq_one_div x
    rw [← h_inv_eq, ← h_inv_eq]
    exact inv_anti₀ h_two_pow_sub_one_pos h_sub_monotone
  exact le_trans h_inv_le (lemma40 ε hε hε_small)
lemma lemma42 (ε : ℝ) (s : Finset ℕ) (hε : ε > 0) (hε_small : ε < 1/100)  (hs_prime : ∀ p ∈ s, p.Prime) :
  (∏ p in s.filter (fun (p : ℕ) => (p : ℝ) ^ ε < 2), (1 : ℝ) / ((p : ℝ) ^ ε - 1)) ≤
  (∏ p in s.filter (fun (p : ℕ) => (p : ℝ) ^ ε < 2), (2 / ε : ℝ)) := by
  apply Finset.prod_le_prod
  · intro p hp
    simp at hp
    have hp_prime : p.Prime := hs_prime p hp.1
    have hp_ge_2 : p ≥ 2 := hp_prime.two_le
    have hp_ε_gt_1 : (p : ℝ) ^ ε > 1 := by
      apply Real.one_lt_rpow
      · exact Nat.one_lt_cast.mpr (Nat.Prime.one_lt hp_prime)
      · exact hε
    exact le_of_lt (one_div_pos.mpr (sub_pos.mpr hp_ε_gt_1))
  · intro p hp
    simp at hp
    have hp_lt_2 : (p : ℝ) ^ ε < 2 := hp.2
    have hp_prime : p.Prime := hs_prime p hp.1
    have hp_ge_2 : p ≥ 2 := hp_prime.two_le

    -- Since p ≥ 2 and ε > 0, we have 2^ε ≤ p^ε
    have h_2_le_p : (2 : ℝ) ^ ε ≤ (p : ℝ) ^ ε := by
      apply Real.rpow_le_rpow
      · norm_num
      · exact Nat.cast_le.mpr hp_ge_2
      · exact le_of_lt hε

    -- So 2^ε ≤ p^ε < 2
    have h_2_ε_lt_2 : (2 : ℝ) ^ ε < 2 := lt_of_le_of_lt h_2_le_p hp_lt_2

    -- Both 2^ε and p^ε are greater than 1
    have h_2_ε_gt_1 : (2 : ℝ) ^ ε > 1 := by
      apply Real.one_lt_rpow
      · norm_num
      · exact hε
    have hp_ε_gt_1 : (p : ℝ) ^ ε > 1 := by
      apply Real.one_lt_rpow
      · exact Nat.one_lt_cast.mpr (Nat.Prime.one_lt hp_prime)
      · exact hε

    -- Since 2^ε ≤ p^ε and x ↦ 1/(x-1) is antitone on (1,∞), we have 1/(p^ε - 1) ≤ 1/(2^ε - 1)
    have h_anti : AntitoneOn (fun x : ℝ => (x - 1)⁻¹) (Set.Ioi 1) := sub_inv_antitoneOn_Ioi
    have h_mem_2 : (2 : ℝ) ^ ε ∈ Set.Ioi 1 := h_2_ε_gt_1
    have h_mem_p : (p : ℝ) ^ ε ∈ Set.Ioi 1 := hp_ε_gt_1
    have h_ineq : ((p : ℝ) ^ ε - 1)⁻¹ ≤ ((2 : ℝ) ^ ε - 1)⁻¹ := h_anti h_mem_2 h_mem_p h_2_le_p

    -- Convert to division form
    have h_div : 1 / ((p : ℝ) ^ ε - 1) ≤ 1 / ((2 : ℝ) ^ ε - 1) := by
      rw [one_div, one_div]
      exact h_ineq

    -- Apply lemma40
    exact le_trans h_div (lemma40 ε hε hε_small)
lemma lemma44 (ε : ℝ) (s : Finset ℕ) (hε : ε > 0) (hε_small : ε < 1/100)  (hs_prime : ∀ p ∈ s, p.Prime) :
  (∏ p in s.filter (fun p : ℕ => (p : ℝ) ^ ε < 2), ((1 : ℝ) / ((p : ℝ) ^ ε - 1))) ≤ ((2 : ℝ) / ε) ^ ((2 : ℝ) ^ (1 / ε)) := by
  calc
      ∏ p in s.filter (fun p : ℕ => (p : ℝ) ^ ε < 2), (1 : ℝ) / ((p : ℝ) ^ ε - 1)
      _ ≤ ∏ p in s.filter (fun p : ℕ => (p : ℝ) ^ ε < 2), (2 / ε : ℝ) := lemma42 ε s hε hε_small hs_prime
      _ = (2 / ε : ℝ) ^ (s.filter (fun p : ℕ => (p : ℝ) ^ ε < 2)).card := by
        simp only [Finset.prod_const]
      _ = (2 / ε : ℝ) ^ ((s.filter (fun p : ℕ => (p : ℝ) ^ ε < 2)).card : ℝ) := by
        norm_cast
      _ ≤ (2 / ε : ℝ) ^ ((2 : ℝ) ^ (1 / ε)) := lemma12 s ε hε hε_small hs_prime

lemma lemma45 (ε : ℝ) (hε : ε > 0) (hε_small : ε < 1/100)  :
  ∃ (C : ℝ), C > 0 ∧ (2 / ε) ^ ((2 : ℝ) ^ (1 / ε)) ≤ C := by
  use (2 / ε) ^ ((2 : ℝ) ^ (1 / ε))
  constructor
  · -- Show C > 0
    apply Real.rpow_pos_of_pos
    exact div_pos (by norm_num : (2 : ℝ) > 0) hε
  · -- Show (2/ε)^(2^(1/ε)) ≤ C
    rfl

lemma lemma46 (ε : ℝ) (hε : ε > 0) (hε_small : ε < 1/100)  :
  ∃ (C : ℝ), C > 0 ∧ ∀ (N : ℕ) (r : ℕ), 1 ≤ N → 1 ≤ r → rad r = r → ((radical_set r N).card : ℝ) / ((N : ℝ) ^ ε) ≤ C := by
    -- Get the constant from lemma45
  obtain ⟨C, hC_pos, hC_bound⟩ := lemma45 ε hε hε_small
  use C, hC_pos
  intro N r hN hr hr_sf

  -- From lemma29: card/N^ε ≤ sum
  have h_from_29 : ((radical_set r N).card : ℝ) / ((N : ℝ) ^ ε) ≤
                   ∑ n in radical_set r N, (1 : ℝ) / ((n : ℝ) ^ ε) :=
    lemma29 ε N r hε hε_small hN hr

  -- The sum is bounded by (2/ε)^(2^(1/ε))
  have h_sum_bound : ∑ n in radical_set r N, (1 : ℝ) / ((n : ℝ) ^ ε) ≤ (2 / ε) ^ ((2 : ℝ) ^ (1 / ε)) := by
    -- hr_sf is assumed available from the context of lemma46
    -- let hr_sf_proof : rad r = r := hr_sf -- If hr_sf is not directly in scope, use the one from lemma46's body
    -- For the purpose of this solution, we assume hr_sf is in the local context.
    -- If `r` is not squarefree, `radical_set r N` is empty, sum is 0. RHS is positive. So 0 <= RHS holds.
    -- We proceed assuming `hr_sf : rad r = r`, which is the non-trivial case.

    let s := r.primeFactors
    have hs_prime : ∀ p ∈ s, p.Prime := by aesop

    calc ∑ n in radical_set r N, (1 : ℝ) / ((n : ℝ) ^ ε)
        _ ≤ ∑' (m : target_set s), (1 : ℝ) / (((m : ℕ) : ℝ) ^ ε) :=
          lemma31 ε N r hε hε_small hN hr hr_sf -- Uses hr_sf
        _ = ∏ p ∈ s, (1 : ℝ) / ((p : ℝ) ^ ε - 1)  :=
            lemma33 ε s hε hε_small hs_prime
        _ = (∏ p in s.filter (fun (p : ℕ) => (p : ℝ) ^ ε ≥ 2), (1 : ℝ) / ((p : ℝ) ^ ε - 1)) *
            (∏ p in s.filter (fun (p : ℕ) => (p : ℝ) ^ ε < 2), (1 : ℝ) / ((p : ℝ) ^ ε - 1)) :=
            lemma37 ε s hε hε_small hs_prime
        _ ≤ 1 * (∏ p in s.filter (fun (p : ℕ) => (p : ℝ) ^ ε < 2), (1 : ℝ) / ((p : ℝ) ^ ε - 1)) := by
          apply mul_le_mul_of_nonneg_right
          · exact lemma39 ε s hε hε_small hs_prime
          · -- Prove the second product is non-negative
            apply Finset.prod_nonneg
            intros p_val hp_filter
            obtain ⟨hp_s_mem, _⟩ := Finset.mem_filter.mp hp_filter
            apply le_of_lt
            apply one_div_pos.mpr
            apply sub_pos.mpr
            -- Need (p:ℝ)^ε > 1. p is prime, so p ≥ 2. ε > 0.
            -- (p:ℝ) > 1 since p ≥ 2.
            have p_prime_prop : (p_val).Prime := hs_prime p_val hp_s_mem
            exact Real.one_lt_rpow (Nat.one_lt_cast.mpr p_prime_prop.one_lt) hε
        _ = (∏ p in s.filter (fun (p : ℕ) => (p : ℝ) ^ ε < 2), (1 : ℝ) / ((p : ℝ) ^ ε - 1)) := by
            rw [one_mul]
        _ ≤ ((2 : ℝ) / ε) ^ ((2 : ℝ) ^ (1 / ε)) :=
            lemma44 ε s hε hε_small hs_prime

  -- Use hC_bound to complete the proof
  have h_final : (2 / ε) ^ ((2 : ℝ) ^ (1 / ε)) ≤ C := hC_bound

  -- Combine all bounds
  calc ((radical_set r N).card : ℝ) / ((N : ℝ) ^ ε)
      ≤ ∑ n in radical_set r N, (1 : ℝ) / ((n : ℝ) ^ ε) := h_from_29
    _ ≤ (2 / ε) ^ ((2 : ℝ) ^ (1 / ε)) := h_sum_bound
    _ ≤ C := h_final

lemma lemma47 (ε : ℝ) (hε : ε > 0) (hε_small : ε < 1/100)  :
  ∃ (C : ℝ), C > 0 ∧ ∀ (N r : ℕ), 1 ≤ r → r ≤ N → rad r = r → ((radical_set r N).card : ℝ) ≤ C * ((N : ℝ) ^ ε) := by
  obtain ⟨C, hC_pos, hC⟩ := lemma46 ε hε hε_small
  use C, hC_pos
  intro N r hr hrN
  -- We need to show: ((radical_set r N).card : ℝ) ≤ C * ((N : ℝ) ^ ε)
  -- From lemma46, we have: ((radical_set r N).card : ℝ) / ((N : ℝ) ^ ε) ≤ C
  -- We need 1 ≤ N to apply lemma46
  have hN : 1 ≤ N := le_trans hr hrN
  specialize hC N r hN hr
  -- Multiply both sides by N^ε
  rw [div_le_iff₀] at hC
  · exact hC
  · exact Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hN))) ε
theorem theorem48 (ε : ℝ) (hε : ε > 0) (hε_small : ε < 1/100)  :
  ∃ (N₀ : ℕ), ∀ (N : ℕ), N ≥ N₀ → ∀ (r : ℕ), 1 ≤ r → r ≤ N → rad r = r → ((radical_set r N).card : ℝ) ≤ (N : ℝ) ^ ε := by
  have h_half : ε / 2 > 0 := by linarith
  obtain ⟨C, hC_pos, hC_bound⟩ := lemma47 (ε / 2) h_half (by linarith [hε_small])
  -- Choose N₀ large enough so that C ≤ N₀^(ε/2)
  -- Since C is fixed and N^(ε/2) → ∞ as N → ∞, such N₀ exists
  have : ∃ N₀ : ℕ, N₀ > 0 ∧ C ≤ (N₀ : ℝ) ^ (ε / 2) := by
    -- Use Archimedean property: for any C > 0, there exists N such that N > C
    have : ∃ N₀ : ℕ, (N₀ : ℝ) > C ^ (2 / ε) := by
      exact exists_nat_gt (C ^ (2 / ε))
    obtain ⟨N₀, hN₀_gt⟩ := this
    use max N₀ 1
    constructor
    · simp
    · have h1 : (max N₀ 1 : ℕ) ≥ N₀ := by simp
      have h2 : (N₀ : ℝ) > C ^ (2 / ε) := hN₀_gt
      have h3 : ((max N₀ 1 : ℕ) : ℝ) ≥ (N₀ : ℝ) := by simp
      have h4 : ((max N₀ 1 : ℕ) : ℝ) > C ^ (2 / ε) := by linarith
      -- Take (ε/2)-th power of both sides
      have h5 : ((max N₀ 1 : ℕ) : ℝ) ^ (ε / 2) > (C ^ (2 / ε)) ^ (ε / 2) := by
        apply Real.rpow_lt_rpow
        · apply Real.rpow_nonneg
          linarith
        · exact h4
        · linarith
      -- Simplify the right side using rpow_mul
      have h6 : (C ^ (2 / ε)) ^ (ε / 2) = C ^ ((2 / ε) * (ε / 2)) := by
        rw [← Real.rpow_mul]
        · linarith
      have h7 : (2 / ε) * (ε / 2) = 1 := by field_simp
      rw [h6, h7, Real.rpow_one] at h5
      linarith
  obtain ⟨N₀, hN₀_pos, hN₀⟩ := this
  use N₀
  intros N hN r hr_lower hr_upper hr_sf
  -- Show N > 0
  have hN_pos : N > 0 := by linarith [hN₀_pos, hN]
  -- Apply the bound from lemma47
  have h_bound := hC_bound N r hr_lower hr_upper
  -- Since N ≥ N₀, we have C ≤ N^(ε/2)
  have hC_le : C ≤ (N : ℝ) ^ (ε / 2) := by
    calc C ≤ (N₀ : ℝ) ^ (ε / 2) := hN₀
    _ ≤ (N : ℝ) ^ (ε / 2) := by
      apply Real.rpow_le_rpow
      · simp
      · exact Nat.cast_le.mpr hN
      · linarith
  -- Combine to get the desired bound
  calc ((radical_set r N).card : ℝ)
    ≤ C * ((N : ℝ) ^ (ε / 2)) := h_bound hr_sf
    _ ≤ ((N : ℝ) ^ (ε / 2)) * ((N : ℝ) ^ (ε / 2)) := by
      rw [mul_comm]
      apply mul_le_mul_of_nonneg_left hC_le
      apply Real.rpow_nonneg
      simp
    _ = (N : ℝ) ^ ε := by
      rw [← Real.rpow_add]
      · ring_nf
      · simp [hN_pos]
lemma lemma49 (N : ℕ) (hN : N ≥ 1) (lambda : ℝ) (hlambda : 0 < lambda ∧ lambda < 1) :
    ((Finset.Icc 1 N).filter (fun n => (rad n : ℝ) ≤ (N : ℝ) ^ lambda)).card = ∑ r in Finset.Icc 1 (Nat.floor ((N : ℝ) ^ lambda)), ((Finset.Icc 1 N).filter (fun n => rad n = r)).card := by
  let X := (N : ℝ) ^ lambda
  -- Precompute 0 ≤ X. This is needed for `Nat.le_floor_iff` and `Nat.floor_le`.
  have hX_nonneg : 0 ≤ X := by exact Real.rpow_nonneg (Nat.cast_nonneg N) lambda
  have rad_pos_of_pos (n : ℕ) (h_pos : n ≠ 0) : rad n > 0 := by
    rw [rad, if_neg h_pos] -- By def of rad and n ≠ 0, rad n = n.primeFactors.prod id
    apply Finset.prod_pos
    intro x hx_mem_factors -- Let x be an element of n.primeFactors
    exact Nat.Prime.pos (Nat.prime_of_mem_primeFactors hx_mem_factors) -- x is prime, so x > 0
  have rad_ge_one_of_ge_one {n : ℕ} (hn : 1 ≤ n) : 1 ≤ rad n := by
    rw [Nat.one_le_iff_ne_zero] -- Goal is now `rad n ≠ 0`
    apply Nat.one_le_iff_ne_zero.mp (rad_pos_of_pos n (by linarith [hn]))
  -- The core of the proof is to show that the set on the LHS can be partitioned
  -- into a disjoint union of sets, where each set in the partition corresponds
  -- to a specific value of `rad n`.
  have h_partition : (Finset.Icc 1 N).filter (fun n => (rad n : ℝ) ≤ X) =
    (Finset.Icc 1 (Nat.floor X)).biUnion (fun r : ℕ => (Finset.Icc 1 N).filter (fun n => rad n = r)) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_Icc]
    constructor
    · -- Forward direction: if n is in the LHS, show it's in the RHS
      intro ⟨hn_Icc, h_rad_le_X⟩ -- n ∈ Finset.Icc 1 N AND (rad n : ℝ) ≤ X
      use rad n -- This is our candidate for `r`
      constructor
      · -- Show 1 ≤ rad n
        constructor
        apply rad_ge_one_of_ge_one hn_Icc.1 -- hn_Icc.1 is the hypothesis n ≥ 1
        rw [Nat.le_floor_iff]
        <;> assumption
      · exact ⟨hn_Icc, rfl⟩
    · -- Backward direction: if n is in the RHS, show it's in the LHS
      intro ⟨r, hr_Icc_r, hn_filter_r⟩
      obtain ⟨hn_Icc, h_rad_eq_r⟩ := hn_filter_r -- n ∈ Finset.Icc 1 N AND rad n = r
      -- Goal: n ∈ Finset.Icc 1 N ∧ (rad n : ℝ) ≤ X
      constructor
      · exact hn_Icc -- First part is direct from hn_filter_r
      · -- Show (rad n : ℝ) ≤ X
        rw [h_rad_eq_r] -- Goal becomes (r : ℝ) ≤ X
        -- We know r ≤ Nat.floor X (from hr_Icc_r.2)
        -- And (Nat.floor X : ℝ) ≤ X (from Nat.floor_le, needs 0 ≤ X)
        calc (r : ℝ) ≤ (Nat.floor X : ℝ) := Nat.cast_le.mpr hr_Icc_r.2
             _ ≤ X                       := Nat.floor_le hX_nonneg
  -- Now use the partition equality and properties of card_biUnion
  rw [h_partition]
  rw [Finset.card_biUnion]
  -- Side goal for Finset.card_biUnion: show pairwise disjointness
  · intros r₁ _ r₂ _ h_r_ne -- r₁ and r₂ are distinct elements from Finset.Icc 1 (Nat.floor X)
    intro n h_n_in_F1 h_n_in_F2
    simp only [Finset.mem_filter] at h_n_in_F1 h_n_in_F2
    -- Define F₁ and F₂ for clarity
    let F₁ := {m ∈ Finset.Icc 1 N | rad m = r₁}
    let F₂ := {m ∈ Finset.Icc 1 N | rad m = r₂}
    have h_s_n_subset_inter : n ≤ F₁ ∩ F₂ :=
      Finset.subset_inter h_n_in_F1 h_n_in_F2
    -- Now, we show that F₁ ∩ F₂ is the empty set.
    have h_inter_empty : F₁ ∩ F₂ = ∅ := by
      -- To show a set is empty, we show that it has no elements.
      apply Finset.eq_empty_iff_forall_not_mem.mpr
      intro x hx_mem_inter -- Assume x is an element in the intersection.
      -- Unpack what it means for x to be in the intersection.
      rw [Finset.mem_inter] at hx_mem_inter
      obtain ⟨hx_mem_F1, hx_mem_F2⟩ := hx_mem_inter
      -- Unpack what it means for x to be in F₁ and F₂ (these are filtered sets).
      rw [Finset.mem_filter] at hx_mem_F1 hx_mem_F2
      obtain ⟨_x_in_Icc1N_F1, h_rad_x_eq_r1⟩ := hx_mem_F1
      obtain ⟨_x_in_Icc1N_F2, h_rad_x_eq_r2⟩ := hx_mem_F2
      have h_r1_eq_r2 : r₁ = r₂ := Eq.trans (Eq.symm h_rad_x_eq_r1) h_rad_x_eq_r2
      exact h_r_ne h_r1_eq_r2
    rw [h_inter_empty] at h_s_n_subset_inter
    exact h_s_n_subset_inter
lemma lemma50 (N : ℕ) (hN : N ≥ 1) (lambda : ℝ) (hlambda : 0 < lambda ∧ lambda < 1) :
    ((Finset.Icc 1 N).filter (fun n => rad n ≤ (N : ℝ) ^ lambda)).card = ∑ r in Finset.Icc 1 (Nat.floor ((N : ℝ) ^ lambda)), (radical_set r N).card := by
  rw [lemma49 N hN lambda hlambda]
  apply Finset.sum_congr rfl
  intro r hr
  have hr_ge : r ≥ 1 := (Finset.mem_Icc.mp hr).1
  have h_eq : (Finset.Icc 1 N).filter (fun n => rad n = r) = (Finset.range (N + 1)).filter (fun n => rad n = r) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
    constructor
    · intro ⟨⟨_, hn_le⟩, hn_rad⟩
      exact ⟨Nat.lt_succ_of_le hn_le, hn_rad⟩
    · intro ⟨hn_lt, hn_rad⟩
      constructor
      · constructor
        · by_contra h_not
          push_neg at h_not
          have : n = 0 := by omega
          rw [this, rad] at hn_rad
          simp at hn_rad
          rw [← hn_rad] at hr_ge
          omega
        · exact Nat.le_of_succ_le_succ hn_lt
      · exact hn_rad
  rw [radical_set, h_eq]
lemma lemma51 (ε : ℝ) (hε : ε > 0) (hε_small : ε < 1/100)  :
  ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ → ∀ lambda : ℝ, 0 < lambda → lambda < 1 →
    (((Finset.Icc 1 N).filter (fun n => rad n ≤ (N : ℝ) ^ lambda)).card : ℝ) ≤
    (Nat.floor ((N : ℝ) ^ lambda) : ℝ) * ((N : ℝ) ^ ε) := by
  -- Get N₀ from theorem48
  obtain ⟨N₀, hN₀⟩ := theorem48 ε hε hε_small
  use max N₀ 1
  intros N hN lambda hlambda_pos hlambda_lt_one

  -- Basic setup
  have hN_ge_one : N ≥ 1 := le_trans (le_max_right N₀ 1) hN
  have hN_ge_N₀ : N ≥ N₀ := le_trans (le_max_left N₀ 1) hN

  -- Apply lemma50 (following the informal proof structure)
  have h_eq : ((Finset.Icc 1 N).filter (fun n => rad n ≤ (N : ℝ) ^ lambda)).card =
              ∑ r in Finset.Icc 1 (Nat.floor ((N : ℝ) ^ lambda)), (radical_set r N).card :=
    lemma50 N hN_ge_one lambda ⟨hlambda_pos, hlambda_lt_one⟩

  rw [h_eq, Nat.cast_sum]

  -- Key insight: each radical_set has size ≤ N^ε by theorem48
  have h_each_bounded : ∀ r ∈ Finset.Icc 1 (Nat.floor ((N : ℝ) ^ lambda)),
                        ((radical_set r N).card : ℝ) ≤ (N : ℝ) ^ ε := by
    intros r hr
    rw [Finset.mem_Icc] at hr

    -- Apply theorem48 when rad r = r (squarefree case)
    by_cases h_sf : rad r = r
    · -- Squarefree case: use theorem48
      have floor_pow_le_self (N : ℕ) (lambda : ℝ) (hN : N ≥ 1) (hlambda : 0 < lambda) (hlambda_lt : lambda < 1) : Nat.floor ((N : ℝ) ^ lambda) ≤ N := by
        apply Nat.floor_le_of_le
        exact Real.rpow_le_self_of_one_le (Nat.one_le_cast.mpr hN) (le_of_lt hlambda_lt)
      have hr_le_N : r ≤ N := by
        -- Use floor_pow_le_self lemma
        exact le_trans hr.2 (floor_pow_le_self N lambda hN_ge_one hlambda_pos hlambda_lt_one)
      exact hN₀ N hN_ge_N₀ r hr.1 hr_le_N h_sf
    · -- Non-squarefree case: radical_set is empty
      have h_empty : (radical_set r N).card = 0 := by
        -- Use rad_idempotent to show this leads to contradiction
        rw [Finset.card_eq_zero, radical_set, Finset.filter_eq_empty_iff]
        intro n hn
        intro h_rad_eq
        -- We have rad n = r but rad r ≠ r
        -- This contradicts rad_idempotent: rad(rad n) = rad n
        have h_rad_n : rad (rad n) = rad n := by
          by_cases h_n_eq_zero : n = 0
          · simp [h_n_eq_zero, rad]
          · have h_rad_n_eq_prod : rad n = n.primeFactors.prod id := by
              simp [rad, h_n_eq_zero]
            rw [h_rad_n_eq_prod]
            have rad_pos_of_pos (n : ℕ) (h_pos : n ≠ 0) : rad n > 0 := by
              rw [rad, if_neg h_pos] -- By def of rad and n ≠ 0, rad n = n.primeFactors.prod id
              apply Finset.prod_pos
              intro x hx_mem_factors -- Let x be an element of n.primeFactors
              exact Nat.Prime.pos (Nat.prime_of_mem_primeFactors hx_mem_factors) -- x is prime, so x > 0
            have h_prod_ne_zero : n.primeFactors.prod id ≠ 0 := by
              rw [← h_rad_n_eq_prod] -- Goal changes to rad n ≠ 0
              linarith [rad_pos_of_pos n (by linarith [Nat.one_le_iff_ne_zero.mpr h_n_eq_zero])]
            rw [rad, if_neg h_prod_ne_zero]
            have h_factors_of_prod : (n.primeFactors.prod id).primeFactors = n.primeFactors := by
              apply Nat.primeFactors_prod
              intro p hp_mem_factors -- p ∈ n.primeFactors
              exact Nat.prime_of_mem_primeFactors hp_mem_factors -- p is indeed prime.
            rw [h_factors_of_prod]
        rw [h_rad_eq] at h_rad_n
        exact h_sf h_rad_n
      rw [h_empty]
      simp
      exact Real.rpow_nonneg (Nat.cast_nonneg N) ε

  -- Apply the bound to the sum
  calc ∑ r ∈ Finset.Icc 1 (Nat.floor ((N : ℝ) ^ lambda)), ↑(radical_set r N).card
      ≤ ∑ r ∈ Finset.Icc 1 (Nat.floor ((N : ℝ) ^ lambda)), ((N : ℝ) ^ ε) := by
        apply Finset.sum_le_sum h_each_bounded
    _ = (Finset.Icc 1 (Nat.floor ((N : ℝ) ^ lambda))).card * ((N : ℝ) ^ ε) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Nat.floor ((N : ℝ) ^ lambda) : ℝ) * ((N : ℝ) ^ ε) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg N) ε)
        have card_Icc_le (k : ℕ) : (Finset.Icc 1 k).card ≤ k := by aesop
        exact Nat.cast_le.mpr (card_Icc_le (Nat.floor ((N : ℝ) ^ lambda)))

theorem corollary52 (ε : ℝ) (hε : ε > 0) (hε_small : ε < 1/100)  :
  ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ → ∀ lambda : ℝ, 0 < lambda → lambda < 1 →
    (((Finset.Icc 1 N).filter (fun n => rad n ≤ (N : ℝ) ^ lambda)).card : ℝ) ≤ (N : ℝ) ^ (lambda + ε) := by
  obtain ⟨N₀, hN₀⟩ := lemma51 ε hε hε_small
  use max N₀ 1  -- Ensure N₀ ≥ 1
  intro N hN lambda hlambda_pos hlambda_lt
  have hN_ge_1 : N ≥ 1 := by
    calc N ≥ max N₀ 1 := hN
         _ ≥ 1 := le_max_right N₀ 1
  have h_bound := hN₀ N (le_trans (le_max_left N₀ 1) hN) lambda hlambda_pos hlambda_lt
  suffices (Int.toNat ⌊(N : ℝ) ^ lambda⌋ : ℝ) * ((N : ℝ) ^ ε) ≤ (N : ℝ) ^ (lambda + ε) by
    exact le_trans h_bound this
  -- Key: (Int.toNat ⌊x⌋ : ℝ) ≤ x for positive x
  have h_floor_le : (Int.toNat ⌊(N : ℝ) ^ lambda⌋ : ℝ) ≤ (N : ℝ) ^ lambda := by
    have h_pos : 0 < (N : ℝ) ^ lambda := by
      apply Real.rpow_pos_of_pos
      exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hN_ge_1))
    rw [Int.floor_toNat]
    exact Nat.floor_le (le_of_lt h_pos)
  calc (Int.toNat ⌊(N : ℝ) ^ lambda⌋ : ℝ) * ((N : ℝ) ^ ε)
      ≤ (N : ℝ) ^ lambda * (N : ℝ) ^ ε := by
        exact mul_le_mul_of_nonneg_right h_floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) ε)
    _ = (N : ℝ) ^ (lambda + ε) := by
        rw [← Real.rpow_add]
        exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hN_ge_1))
def exceptionalSet (N : ℕ) (ε : ℝ) : Set (ℕ × ℕ × ℕ) :=
  { (a, b, c) |
    1 ≤ a ∧ a ≤ N ∧
    1 ≤ b ∧ b ≤ N ∧
    1 ≤ c ∧ c ≤ N ∧
    a + b = c ∧
    Nat.Coprime a b ∧
    (rad (a * b * c) : ℝ) < (c : ℝ) ^ (1 - ε) }
lemma lemma54 (a b c : ℕ) (ha : a ≥ 1) (hb : b ≥ 1) (hc : c ≥ 1) (h_abc_coprime : Nat.Coprime a (b * c)) (h_bc_coprime : Nat.Coprime b c) (ε : ℝ) (hε : ε > 0) (hε_small : ε < 1/100)
  (h_rab_gt : (rad (a * b) : ℝ) > (c : ℝ) ^ (2 / 3 * (1 - ε)))
  (h_rac_gt : (rad (a * c) : ℝ) > (c : ℝ) ^ (2 / 3 * (1 - ε)))
  (h_rbc_gt : (rad (b * c) : ℝ) > (c : ℝ) ^ (2 / 3 * (1 - ε))) :
  (c : ℝ) ^ (2 - 2 * ε) ≤ (rad (a * b) * rad (a * c) * rad (b * c) : ℝ) ∧ (rad (a * b) * rad (a * c) * rad (b * c) : ℝ) = (rad (a * b * c) : ℝ) ^ 2 := by
  constructor
  · -- First prove (c : ℝ) ^ (2 - 2 * ε) ≤ (rad (a * b) * rad (a * c) * rad (b * c) : ℝ)
    -- First establish that all values are positive
    have h_ab_ne_zero : a * b ≠ 0 := Nat.mul_ne_zero (Nat.one_le_iff_ne_zero.mp ha) (Nat.one_le_iff_ne_zero.mp hb)
    have h_ac_ne_zero : a * c ≠ 0 := Nat.mul_ne_zero (Nat.one_le_iff_ne_zero.mp ha) (Nat.one_le_iff_ne_zero.mp hc)
    have h_bc_ne_zero : b * c ≠ 0 := Nat.mul_ne_zero (Nat.one_le_iff_ne_zero.mp hb) (Nat.one_le_iff_ne_zero.mp hc)

    have h_c_pos : 0 < (c : ℝ) := by
      simp only [Nat.cast_pos]
      exact Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hc)

    -- Show the product of three c^(2/3*(1-ε)) equals c^(2-2ε)
    have h_exp : (c : ℝ) ^ (2 / 3 * (1 - ε)) * (c : ℝ) ^ (2 / 3 * (1 - ε)) * (c : ℝ) ^ (2 / 3 * (1 - ε)) =
                (c : ℝ) ^ (2 - 2 * ε) := by
      rw [← Real.rpow_add h_c_pos, ← Real.rpow_add h_c_pos]
      congr 1
      ring

    -- Now show the inequality
    rw [← h_exp]

    -- Convert > to < for easier manipulation
    have h1 : (c : ℝ) ^ (2 / 3 * (1 - ε)) < (rad (a * b) : ℝ) := h_rab_gt
    have h2 : (c : ℝ) ^ (2 / 3 * (1 - ε)) < (rad (a * c) : ℝ) := h_rac_gt
    have h3 : (c : ℝ) ^ (2 / 3 * (1 - ε)) < (rad (b * c) : ℝ) := h_rbc_gt

    -- Apply transitivity of multiplication with positive numbers
    apply le_of_lt

    have h_pow_pos : 0 < (c : ℝ) ^ (2 / 3 * (1 - ε)) := Real.rpow_pos_of_pos h_c_pos _

    -- Multiply the inequalities
    have h12 : (c : ℝ) ^ (2 / 3 * (1 - ε)) * (c : ℝ) ^ (2 / 3 * (1 - ε)) < (rad (a * b) : ℝ) * (rad (a * c) : ℝ) := by
      apply mul_lt_mul'
      · exact le_of_lt h1
      · exact h2
      · exact le_of_lt h_pow_pos
      · simp only [Nat.cast_pos]
        rw [rad]
        split_ifs
        · contradiction
        · apply Finset.prod_pos
          intros p hp
          exact Nat.Prime.pos (Nat.prime_of_mem_primeFactors hp)

    apply mul_lt_mul'
    · exact le_of_lt h12
    · exact h3
    · exact le_of_lt h_pow_pos
    · apply mul_pos
      · simp only [Nat.cast_pos]
        rw [rad]
        split_ifs
        · contradiction
        · apply Finset.prod_pos
          intros p hp
          exact Nat.Prime.pos (Nat.prime_of_mem_primeFactors hp)
      · simp only [Nat.cast_pos]
        rw [rad]
        split_ifs
        · contradiction
        · apply Finset.prod_pos
          intros p hp
          exact Nat.Prime.pos (Nat.prime_of_mem_primeFactors hp)

  · -- Second prove (rad (a * b) * rad (a * c) * rad (b * c) : ℝ) = (rad (a * b * c) : ℝ) ^ 2
    norm_cast
    exact lemma23 a b c ha hb hc h_abc_coprime h_bc_coprime

lemma lemma55 (a b c : ℕ) (ha : a ≥ 1) (hb : b ≥ 1) (hc : c ≥ 1)
  (h_abc_coprime : Nat.Coprime a (b * c)) (h_bc_coprime : Nat.Coprime b c)
  (ε : ℝ) (hε : ε > 0) (hε_small : ε < 1/100)
  (h_rab_gt : (rad (a * b) : ℝ) > (c : ℝ) ^ (2 / 3 * (1 - ε)))
  (h_rac_gt : (rad (a * c) : ℝ) > (c : ℝ) ^ (2 / 3 * (1 - ε)))
  (h_rbc_gt : (rad (b * c) : ℝ) > (c : ℝ) ^ (2 / 3 * (1 - ε))) :
  (c : ℝ) ^ (1 - ε) ≤ (rad (a * b * c) : ℝ) := by
  have h := lemma54 a b c ha hb hc h_abc_coprime h_bc_coprime ε hε hε_small h_rab_gt h_rac_gt h_rbc_gt
  have h1 : (c : ℝ) ^ (2 - 2 * ε) ≤ (rad (a * b * c) : ℝ) ^ 2 := by
    rw [← h.2]
    exact h.1
  -- Apply rpow_le_rpow with exponent 1/2
  have h2 : ((c : ℝ) ^ (2 - 2 * ε)) ^ (1/2 : ℝ) ≤ ((rad (a * b * c) : ℝ) ^ 2) ^ (1/2 : ℝ) := by
    apply Real.rpow_le_rpow
    · exact Real.rpow_nonneg (Nat.cast_nonneg c) _
    · exact h1
    · norm_num
  -- Simplify the left side
  have eq1 : (2 - 2 * ε) * (1 / 2) = 1 - ε := by ring
  rw [← Real.rpow_mul (Nat.cast_nonneg c), eq1] at h2
  -- Simplify the right side
  rw [← Real.rpow_natCast (rad (a * b * c)) 2] at h2
  -- Now we need to simplify (↑(rad (a * b * c)) ^ ↑2) ^ (1 / 2)
  have eq2 : ((rad (a * b * c) : ℝ) ^ (2 : ℝ)) ^ (1/2 : ℝ) = (rad (a * b * c) : ℝ) := by
    rw [← Real.rpow_mul (Nat.cast_nonneg (rad (a * b * c)))]
    norm_num
  -- Convert h2 to the final form
  convert h2
  exact eq2.symm
lemma lemma56 (N a b c : ℕ) (ε : ℝ) (hN : N ≥ 1) (hε : ε > 0) (hε_small : ε < 1/100)  (h_in_E : (a, b, c) ∈ exceptionalSet N ε) :
  (rad (a * b) : ℝ) < (c : ℝ) ^ (2 / 3 * (1 - ε)) ∨
  (rad (a * c) : ℝ) < (c : ℝ) ^ (2 / 3 * (1 - ε)) ∨
  (rad (b * c) : ℝ) < (c : ℝ) ^ (2 / 3 * (1 - ε)) := by
-- Unfold the exceptional set membership
  unfold exceptionalSet at h_in_E
  -- Extract the conditions
  obtain ⟨ha, ha_le, hb, hb_le, hc, hc_le, h_sum, h_coprime, h_rad_lt⟩ := h_in_E

  -- Use classical logic to prove by cases
  by_cases h1 : (rad (a * b) : ℝ) < (c : ℝ) ^ (2 / 3 * (1 - ε))
  · left; exact h1
  · by_cases h2 : (rad (a * c) : ℝ) < (c : ℝ) ^ (2 / 3 * (1 - ε))
    · right; left; exact h2
    · by_cases h3 : (rad (b * c) : ℝ) < (c : ℝ) ^ (2 / 3 * (1 - ε))
      · right; right; exact h3
      · -- Now all three are NOT <, so all three are ≥
        push_neg at h1 h2 h3

        -- Derive the coprimality conditions
        have h_ac : Nat.Coprime a c := by
          have h_eq : c = a + b := h_sum.symm
          rw [h_eq]
          exact Nat.coprime_self_add_right.mpr h_coprime

        have h_bc : Nat.Coprime b c := by
          have h_eq : c = a + b := h_sum.symm
          rw [h_eq, add_comm]
          exact Nat.coprime_self_add_right.mpr (Nat.Coprime.symm h_coprime)

        have h_abc : Nat.Coprime a (b * c) := by
          apply Nat.Coprime.mul_right h_coprime h_ac

        -- Use lemma23 to get the identity
        have h_eq_nat : rad (a * b) * rad (a * c) * rad (b * c) = (rad (a * b * c)) ^ 2 :=
          lemma23 a b c ha hb hc h_abc h_bc

        -- Cast to reals
        have h_eq : (rad (a * b) : ℝ) * (rad (a * c) : ℝ) * (rad (b * c) : ℝ) =
                    ((rad (a * b * c) : ℝ)) ^ 2 := by
          norm_cast

        -- Now we need to show this leads to a contradiction
        -- If all three are ≥ c^(2/3*(1-ε)), their product is ≥ [c^(2/3*(1-ε))]^3 = c^(2*(1-ε))
        have h_prod_ge : (rad (a * b) : ℝ) * (rad (a * c) : ℝ) * (rad (b * c) : ℝ) ≥
                         (c : ℝ) ^ (2 / 3 * (1 - ε)) * (c : ℝ) ^ (2 / 3 * (1 - ε)) *
                         (c : ℝ) ^ (2 / 3 * (1 - ε)) := by
          have h_pos : 0 ≤ (c : ℝ) ^ (2 / 3 * (1 - ε)) := by
            apply Real.rpow_nonneg
            exact Nat.cast_nonneg c
          have h_nonneg1 : 0 ≤ (rad (a * b) : ℝ) := Nat.cast_nonneg _
          have h_nonneg2 : 0 ≤ (rad (a * c) : ℝ) := Nat.cast_nonneg _
          have h_nonneg3 : 0 ≤ (rad (b * c) : ℝ) := Nat.cast_nonneg _
          apply mul_le_mul
          · apply mul_le_mul h1 h2 h_pos (le_trans h_pos h1)
          · exact h3
          · exact h_pos
          · exact mul_nonneg h_nonneg1 h_nonneg2

        -- Simplify the right side using power laws
        have h_exp : (c : ℝ) ^ (2 / 3 * (1 - ε)) * (c : ℝ) ^ (2 / 3 * (1 - ε)) *
                     (c : ℝ) ^ (2 / 3 * (1 - ε)) = (c : ℝ) ^ (2 * (1 - ε)) := by
          rw [← Real.rpow_add, ← Real.rpow_add]
          ring_nf
          · exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hc))
          · exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hc))

        rw [h_eq, h_exp] at h_prod_ge

        -- So (rad(abc))^2 ≥ c^(2*(1-ε))
        -- This means rad(abc) ≥ c^(1-ε)
        have h_rad_ge : (rad (a * b * c) : ℝ) ≥ (c : ℝ) ^ (1 - ε) := by
          have h_sq : ((rad (a * b * c) : ℝ)) ^ 2 ≥ (c : ℝ) ^ (2 * (1 - ε)) := h_prod_ge
          have h_c_nonneg : 0 ≤ (c : ℝ) ^ (1 - ε) := by
            apply Real.rpow_nonneg
            exact Nat.cast_nonneg c
          have h_rad_nonneg : 0 ≤ (rad (a * b * c) : ℝ) := Nat.cast_nonneg _
          -- Use the fact that x^2 ≥ y^2 and 0 ≤ y implies x ≥ y
          have h_pow_eq : (c : ℝ) ^ (2 * (1 - ε)) = ((c : ℝ) ^ (1 - ε)) ^ 2 := by
            rw [← Real.rpow_two]
            rw [← Real.rpow_mul]
            ring_nf
            exact Nat.cast_nonneg c
          rw [h_pow_eq] at h_sq
          exact le_of_sq_le_sq h_sq h_rad_nonneg

        -- This contradicts h_rad_lt
        linarith
lemma lemma57 (N a b c : ℕ) (ε : ℝ) (hε : ε > 0) (hε_small : ε < 1/100) (h_in_E : (a, b, c) ∈ exceptionalSet N ε) :
  (rad (a * b) : ℝ) < (N : ℝ) ^ ((2 : ℝ) / 3 * (1 - ε)) ∨
  (rad (a * c) : ℝ) < (N : ℝ) ^ ((2 : ℝ) / 3 * (1 - ε)) ∨
  (rad (b * c) : ℝ) < (N : ℝ) ^ ((2 : ℝ) / 3 * (1 - ε)) := by
    -- Extract conditions from exceptional set membership first for later use
  unfold exceptionalSet at h_in_E
  obtain ⟨ha, ha_le, hb, hb_le, hc, hc_le, h_sum, h_coprime, h_rad_lt⟩ := h_in_E

  -- We need N ≥ 1 for lemma56
  have hN_ge_1 : N ≥ 1 := by
    linarith [ha, ha_le]

  -- Reconstruct the membership for lemma56
  have h_in_E_reconstructed : (a, b, c) ∈ exceptionalSet N ε := by
    unfold exceptionalSet
    exact ⟨ha, ha_le, hb, hb_le, hc, hc_le, h_sum, h_coprime, h_rad_lt⟩

  -- Apply lemma56 to get that one of the three conditions holds with c^(2/3*(1-ε))
  have h_from_56 := lemma56 N a b c ε hN_ge_1 hε hε_small h_in_E_reconstructed

  -- Since c ≤ N, we have c^(2/3*(1-ε)) ≤ N^(2/3*(1-ε))
  have h_c_le_N : (c : ℝ) ^ (2 / 3 * (1 - ε)) ≤ (N : ℝ) ^ (2 / 3 * (1 - ε)) := by
    apply Real.rpow_le_rpow
    · exact Nat.cast_nonneg c
    · exact Nat.cast_le.mpr hc_le
    · -- Need to show 2/3*(1-ε) ≥ 0
      apply mul_nonneg
      · norm_num
      · linarith [hε_small]

  -- Now use transitivity to get the result
  cases h_from_56 with
  | inl h1 =>
    left
    exact lt_of_lt_of_le h1 h_c_le_N
  | inr h2 =>
    cases h2 with
    | inl h2a =>
      right; left
      exact lt_of_lt_of_le h2a h_c_le_N
    | inr h2b =>
      right; right
      exact lt_of_lt_of_le h2b h_c_le_N
lemma lemma58 (N : ℕ) (ε : ℝ) [Finite (exceptionalSet N ε)] [Fintype ↑(exceptionalSet N ε)] :
  (exceptionalSet N ε).toFinset.card = ∑ x in (exceptionalSet N ε).toFinset, 1 := by
  exact Finset.card_eq_sum_ones _
-- Lemma 59
lemma lemma59 (N : ℕ) (ε : ℝ) [Finite (exceptionalSet N ε)] [Fintype ↑(exceptionalSet N ε)] (hN : N ≥ 1) (hε : ε > 0) (hε_small : ε < 1/100) :
  (exceptionalSet N ε).toFinset.card ≤ 3 * ((Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter (fun p : ℕ × ℕ => Nat.Coprime p.fst p.snd ∧ ((rad (p.fst * p.snd)) : ℝ) ≤ (N : ℝ) ^ ((2 : ℝ) / 3 * (1 - ε)))).card := by
  -- Let S be the set of valid pairs
  let S := (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter (fun p : ℕ × ℕ => Nat.Coprime p.fst p.snd ∧ (rad (p.fst * p.snd) : ℝ) < (N : ℝ) ^ ((2 : ℝ) / 3 * (1 - ε)))

  let S_goal := (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter (fun p : ℕ × ℕ => Nat.Coprime p.fst p.snd ∧ ((rad (p.fst * p.snd)) : ℝ) ≤ (N : ℝ) ^ ((2 : ℝ) / 3 * (1 - ε)))

  -- Count triples by their contributing pairs
  let count_ab := (exceptionalSet N ε).toFinset.filter (fun t => (rad (t.1 * t.2.1) : ℝ) < (N : ℝ) ^ ((2 : ℝ) / 3 * (1 - ε)))
  let count_ac := (exceptionalSet N ε).toFinset.filter (fun t => (rad (t.1 * t.2.2) : ℝ) < (N : ℝ) ^ ((2 : ℝ) / 3 * (1 - ε)))
  let count_bc := (exceptionalSet N ε).toFinset.filter (fun t => (rad (t.2.1 * t.2.2) : ℝ) < (N : ℝ) ^ ((2 : ℝ) / 3 * (1 - ε)))

  -- By lemma57, every triple is in at least one of these sets
  have h_cover : (exceptionalSet N ε).toFinset ⊆ count_ab ∪ count_ac ∪ count_bc := by
    intro ⟨a, b, c⟩ h_mem
    simp [count_ab, count_ac, count_bc]
    have h_set_mem : (a, b, c) ∈ exceptionalSet N ε := Set.mem_toFinset.mp h_mem
    have h57 := lemma57 N a b c ε hε hε_small h_set_mem
    cases h57 with
    | inl h_ab => left; exact ⟨h_set_mem, h_ab⟩
    | inr h_rest =>
      cases h_rest with
      | inl h_ac => right; left; exact ⟨h_set_mem, h_ac⟩
      | inr h_bc => right; right; exact ⟨h_set_mem, h_bc⟩

  -- Use the basic union bound: |A ∪ B ∪ C| ≤ |A| + |B| + |C|
  have h_union_bound : (exceptionalSet N ε).toFinset.card ≤ count_ab.card + count_ac.card + count_bc.card := by
    have h_card_le : (count_ab ∪ count_ac ∪ count_bc).card ≤ count_ab.card + count_ac.card + count_bc.card := by
      calc (count_ab ∪ count_ac ∪ count_bc).card
        ≤ (count_ab ∪ count_ac).card + count_bc.card := Finset.card_union_le _ _
        _ ≤ count_ab.card + count_ac.card + count_bc.card := by
          linarith [Finset.card_union_le count_ab count_ac]
    apply le_trans _ h_card_le
    exact Finset.card_le_card h_cover

  -- Each count_xy.card ≤ S.card using injection
  have h_bound_ab : count_ab.card ≤ S.card := by
    apply Finset.card_le_card_of_injOn (fun t => (t.1, t.2.1))
    · intro ⟨a, b, c⟩ h_mem
      simp [count_ab, S] at h_mem ⊢
      obtain ⟨h_set_mem, h_rad⟩ := h_mem
      unfold exceptionalSet at h_set_mem
      constructor
      · exact ⟨⟨h_set_mem.1, h_set_mem.2.1⟩, ⟨h_set_mem.2.2.1, h_set_mem.2.2.2.1⟩⟩
      · exact ⟨h_set_mem.2.2.2.2.2.2.2.1, h_rad⟩
    · simp only [Set.InjOn]
      intro ⟨a₁, b₁, c₁⟩ h_mem₁ ⟨a₂, b₂, c₂⟩ h_mem₂ h_eq
      simp at h_eq
      obtain ⟨h_a_eq, h_b_eq⟩ := h_eq
      simp [count_ab] at h_mem₁ h_mem₂
      obtain ⟨h_set_mem₁, _⟩ := h_mem₁
      obtain ⟨h_set_mem₂, _⟩ := h_mem₂
      unfold exceptionalSet at h_set_mem₁ h_set_mem₂
      have h_c₁ : c₁ = a₁ + b₁ := h_set_mem₁.2.2.2.2.2.2.1.symm
      have h_c₂ : c₂ = a₂ + b₂ := h_set_mem₂.2.2.2.2.2.2.1.symm
      rw [h_a_eq, h_b_eq] at h_c₁
      simp [h_a_eq, h_b_eq, h_c₁, h_c₂]

  have h_bound_ac : count_ac.card ≤ S.card := by
    apply Finset.card_le_card_of_injOn (fun t => (t.1, t.2.2))
    · intro ⟨a, b, c⟩ h_mem
      simp [count_ac, S] at h_mem ⊢
      obtain ⟨h_set_mem, h_rad⟩ := h_mem
      unfold exceptionalSet at h_set_mem
      constructor
      · exact ⟨⟨h_set_mem.1, h_set_mem.2.1⟩, ⟨h_set_mem.2.2.2.2.1, h_set_mem.2.2.2.2.2.1⟩⟩
      · have h_ac_coprime : Nat.Coprime a c := by
          have h_eq : c = a + b := h_set_mem.2.2.2.2.2.2.1.symm
          rw [h_eq]
          exact Nat.coprime_self_add_right.mpr h_set_mem.2.2.2.2.2.2.2.1
        exact ⟨h_ac_coprime, h_rad⟩
    · simp only [Set.InjOn]
      intro ⟨a₁, b₁, c₁⟩ h_mem₁ ⟨a₂, b₂, c₂⟩ h_mem₂ h_eq
      simp at h_eq
      obtain ⟨h_a_eq, h_c_eq⟩ := h_eq
      simp [count_ac] at h_mem₁ h_mem₂
      obtain ⟨h_set_mem₁, _⟩ := h_mem₁
      obtain ⟨h_set_mem₂, _⟩ := h_mem₂
      unfold exceptionalSet at h_set_mem₁ h_set_mem₂
      have h_eq₁ : a₁ + b₁ = c₁ := h_set_mem₁.2.2.2.2.2.2.1
      have h_eq₂ : a₂ + b₂ = c₂ := h_set_mem₂.2.2.2.2.2.2.1
      rw [h_a_eq, h_c_eq] at h_eq₁
      have h_b_eq : b₁ = b₂ := by linarith [h_eq₁, h_eq₂]
      simp [h_a_eq, h_b_eq, h_c_eq]

  have h_bound_bc : count_bc.card ≤ S.card := by
    apply Finset.card_le_card_of_injOn (fun t => (t.2.1, t.2.2))
    · intro ⟨a, b, c⟩ h_mem
      simp [count_bc, S] at h_mem ⊢
      obtain ⟨h_set_mem, h_rad⟩ := h_mem
      unfold exceptionalSet at h_set_mem
      constructor
      · exact ⟨⟨h_set_mem.2.2.1, h_set_mem.2.2.2.1⟩, ⟨h_set_mem.2.2.2.2.1, h_set_mem.2.2.2.2.2.1⟩⟩
      · have h_bc_coprime : Nat.Coprime b c := by
          have h_eq : c = a + b := h_set_mem.2.2.2.2.2.2.1.symm
          rw [h_eq, add_comm]
          exact Nat.coprime_self_add_right.mpr (Nat.Coprime.symm h_set_mem.2.2.2.2.2.2.2.1)
        exact ⟨h_bc_coprime, h_rad⟩
    · simp only [Set.InjOn]
      intro ⟨a₁, b₁, c₁⟩ h_mem₁ ⟨a₂, b₂, c₂⟩ h_mem₂ h_eq
      simp at h_eq
      obtain ⟨h_b_eq, h_c_eq⟩ := h_eq
      simp [count_bc] at h_mem₁ h_mem₂
      obtain ⟨h_set_mem₁, _⟩ := h_mem₁
      obtain ⟨h_set_mem₂, _⟩ := h_mem₂
      unfold exceptionalSet at h_set_mem₁ h_set_mem₂
      have h_eq₁ : a₁ + b₁ = c₁ := h_set_mem₁.2.2.2.2.2.2.1
      have h_eq₂ : a₂ + b₂ = c₂ := h_set_mem₂.2.2.2.2.2.2.1
      rw [h_b_eq, h_c_eq] at h_eq₁
      have h_a_eq : a₁ = a₂ := by linarith [h_eq₁, h_eq₂]
      simp [h_a_eq, h_b_eq, h_c_eq]

  have h_S_subset_S_goal : S ⊆ S_goal := by
    intro p h_mem_S
    simp only [S, S_goal, Finset.mem_filter] at h_mem_S ⊢
    obtain ⟨h_p_domain, h_coprime, h_rad_lt⟩ := h_mem_S
    exact ⟨h_p_domain, h_coprime, le_of_lt h_rad_lt⟩
  have h_card_S_le_S_goal : S.card ≤ S_goal.card := Finset.card_le_card h_S_subset_S_goal

  -- Combine everything
  calc (exceptionalSet N ε).toFinset.card
    ≤ count_ab.card + count_ac.card + count_bc.card := h_union_bound
    _ ≤ S.card + S.card + S.card := by linarith [h_bound_ab, h_bound_ac, h_bound_bc]
    _ = 3 * S.card := by ring
    _ ≤ 3 * S_goal.card := Nat.mul_le_mul_left 3 h_card_S_le_S_goal

lemma lemma60 (ε : ℝ) (N : ℕ) (hε : ε > 0) (hN : N ≥ 1) (h_exp_pos : (2 : ℝ) / 3 * (1 - ε) > 0) : let K0 := (N : ℝ) ^ ((2 : ℝ) / 3 * (1 - ε)); (((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter (fun p : ℕ × ℕ => Nat.Coprime p.fst p.snd ∧ ((rad (p.fst * p.snd)) : ℝ) ≤ K0)).card = ∑ r in Finset.Icc 1 (Nat.floor K0), (((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter (fun p : ℕ × ℕ => Nat.Coprime p.fst p.snd ∧ rad (p.fst * p.snd) = r)).card := by
  intro K0
  -- Partition the set based on the exact value of rad(xy)
  have h_partition : (((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter (fun p : ℕ × ℕ => Nat.Coprime p.fst p.snd ∧ (rad (p.fst * p.snd) : ℝ) ≤ K0)) =
    (Finset.Icc 1 (Nat.floor K0)).biUnion (fun r => ((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter (fun p : ℕ × ℕ => Nat.Coprime p.fst p.snd ∧ rad (p.fst * p.snd) = r)) := by
    ext p
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · intro ⟨hp_prod, h_coprime, h_le⟩
      use rad (p.fst * p.snd)
      constructor
      · constructor
        · -- rad(xy) ≥ 1 for x,y ≥ 1
          have h_pos : 1 ≤ rad (p.fst * p.snd) := by
            by_contra h_not
            push_neg at h_not
            have h_zero : rad (p.fst * p.snd) = 0 := Nat.lt_one_iff.mp h_not
            have h_prod_mem : p ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N) := hp_prod
            simp only [Finset.mem_product, Finset.mem_Icc] at h_prod_mem
            have h_x_pos : 1 ≤ p.fst := h_prod_mem.1.1
            have h_y_pos : 1 ≤ p.snd := h_prod_mem.2.1
            have h_xy_ne_zero : p.fst * p.snd ≠ 0 := Nat.mul_ne_zero (Nat.one_le_iff_ne_zero.mp h_x_pos) (Nat.one_le_iff_ne_zero.mp h_y_pos)
            rw [rad, if_neg h_xy_ne_zero] at h_zero
            have : (p.fst * p.snd).primeFactors.prod id ≠ 0 := by
              apply Finset.prod_ne_zero_iff.mpr
              intro q hq
              exact Nat.Prime.ne_zero (Nat.prime_of_mem_primeFactors hq)
            exact this h_zero
          exact h_pos
        · -- rad(xy) < ceil(K0)
          have h_ceil_bound : (rad (p.fst * p.snd) : ℝ) ≤ K0 := h_le
          have h_floor_bound: _ := Nat.le_floor h_ceil_bound
          exact h_floor_bound
      · exact ⟨hp_prod, h_coprime, rfl⟩
    · intro ⟨r, ⟨⟨hr_ge, hr_lt⟩, hp_prod, h_coprime, h_eq⟩⟩
      refine ⟨hp_prod, h_coprime, ?_⟩
      rw [h_eq]
      have h_K0ge0 : K0 ≥ 0 := by refine Real.rpow_nonneg (by linarith) (2 / 3 * (1 - ε))
      have h_floor_le: Nat.floor K0 ≤ K0 := Nat.floor_le h_K0ge0
      exact (Nat.le_floor_iff h_K0ge0).mp hr_lt


  -- Apply the partition to get card equality
  rw [h_partition, Finset.card_biUnion]

  -- Show pairwise disjointness: Function.onFun Disjoint f means Disjoint (f r₁) (f r₂)
  intro r₁ hr₁ r₂ hr₂ h_ne
  -- We need to show Disjoint (sets for r₁) (sets for r₂)
  rw [Function.onFun]
  -- Now we need to show Disjoint of the two filtered sets
  apply Finset.disjoint_left.mpr
  intro p hp₁ hp₂
  -- Extract the conditions from membership in the filtered sets
  simp only [Finset.mem_filter] at hp₁ hp₂
  -- hp₁ gives us: p ∈ product ∧ coprime ∧ rad = r₁
  -- hp₂ gives us: p ∈ product ∧ coprime ∧ rad = r₂
  have h₁ : rad (p.fst * p.snd) = r₁ := hp₁.2.2
  have h₂ : rad (p.fst * p.snd) = r₂ := hp₂.2.2
  -- This gives r₁ = r₂, contradicting h_ne
  have : r₁ = r₂ := by rw [← h₁, h₂]
  exact h_ne this
lemma lemma61 (N r : ℕ) :
  ((Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter (fun (x, y) => Nat.Coprime x y ∧ rad (x * y) = r)).card
  ≤ ∑ n in radical_set r (N * N), tau n := by -- Following the informal proof strategy: group pairs (x,y) by their product n = xy
  -- For each n with rad(n) = r, bound the coprime factorizations by τ(n)

  have h_key_bound : ∀ n, ((Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter (fun (x, y) => x * y = n ∧ Nat.Coprime x y)).card ≤ tau n := by
    intro n
    -- Each coprime factorization n = xy corresponds to x being a divisor of n
    apply Finset.card_le_card_of_injOn (fun p => p.1)
    · -- Show image is in divisors
      intro ⟨x, y⟩ h_mem
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at h_mem
      obtain ⟨⟨⟨hx_ge, _⟩, ⟨hy_ge, _⟩⟩, h_eq, _⟩ := h_mem
      simp only [tau, Nat.mem_divisors]
      constructor
      · rw [← h_eq]; exact dvd_mul_right x y
      · rw [← h_eq]
        exact Nat.mul_ne_zero (Nat.one_le_iff_ne_zero.mp hx_ge) (Nat.one_le_iff_ne_zero.mp hy_ge)
    · -- Show injectivity: if two pairs have the same first component, they're equal
      intro ⟨x₁, y₁⟩ h₁ ⟨x₂, y₂⟩ h₂ h_eq
      simp at h_eq
      simp only [Finset.mem_filter, Finset.mem_product] at h₁ h₂
      have h_eq₁ : x₁ * y₁ = n := by simp at h₁; exact h₁.2.1
      have h_eq₂ : x₂ * y₂ = n := by simp at h₂; exact h₂.2.1
      -- Since x₁ = x₂ and x₁ * y₁ = n = x₂ * y₂, we get x₂ * y₁ = x₂ * y₂, so y₁ = y₂
      have h_y_eq : y₁ = y₂ := by
        have h_x_ne_zero : x₁ ≠ 0 := by
          simp at h₁
          exact Nat.one_le_iff_ne_zero.mp h₁.1.1.1
        rw [h_eq] at h_eq₁
        -- Now h_eq₁ : x₂ * y₁ = n and h_eq₂ : x₂ * y₂ = n
        -- So x₂ * y₁ = x₂ * y₂
        have : x₂ * y₁ = x₂ * y₂ := h_eq₁.trans h_eq₂.symm
        rw [h_eq] at h_x_ne_zero
        exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero h_x_ne_zero) this
      simp [h_eq, h_y_eq]

  -- Use the subset relationship to bound the original set
  suffices h : ((Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter (fun (x, y) => Nat.Coprime x y ∧ rad (x * y) = r)).card ≤
    ∑ n in radical_set r (N * N), ((Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter (fun (x, y) => x * y = n ∧ Nat.Coprime x y)).card by
    calc ((Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter (fun (x, y) => Nat.Coprime x y ∧ rad (x * y) = r)).card
      ≤ ∑ n in radical_set r (N * N), ((Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter (fun (x, y) => x * y = n ∧ Nat.Coprime x y)).card := h
      _ ≤ ∑ n in radical_set r (N * N), tau n := by
        apply Finset.sum_le_sum
        intro n _
        exact h_key_bound n

  -- Prove the suffices goal using subset argument
  -- The key insight: each pair (x,y) with Coprime x y ∧ rad (x * y) = r
  -- contributes to exactly one n = x * y in the sum
  have h_subset : ((Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter (fun (x, y) => Nat.Coprime x y ∧ rad (x * y) = r)) ⊆
    (radical_set r (N * N)).biUnion (fun n => (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter (fun (x, y) => x * y = n ∧ Nat.Coprime x y)) := by
    intro ⟨x, y⟩ h_mem
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at h_mem ⊢
    obtain ⟨⟨⟨hx_ge, hx_le⟩, ⟨hy_ge, hy_le⟩⟩, h_coprime, h_rad⟩ := h_mem
    use x * y
    constructor
    · simp only [radical_set, Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.lt_succ_of_le (Nat.mul_le_mul hx_le hy_le), h_rad⟩
    · exact ⟨⟨⟨hx_ge, hx_le⟩, ⟨hy_ge, hy_le⟩⟩, rfl, h_coprime⟩

  -- The subset gives us the bound we need
  calc ((Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter (fun (x, y) => Nat.Coprime x y ∧ rad (x * y) = r)).card
    ≤ ((radical_set r (N * N)).biUnion (fun n => (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter (fun (x, y) => x * y = n ∧ Nat.Coprime x y))).card := Finset.card_le_card h_subset
    _ ≤ ∑ n in radical_set r (N * N), ((Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter (fun (x, y) => x * y = n ∧ Nat.Coprime x y)).card := by
      apply Finset.card_biUnion_le
lemma lemma61_new (ε : ℝ) (hε : ε > 0) (hε_small : ε < 1/100) :
∀ δ₁ : ℝ, δ₁ > 0 → ∃ N₁ : ℕ, ∀ (N : ℕ), N ≥ N₁ → ∀ (r : ℕ), r ≥ 1 →
(((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter (fun p : ℕ × ℕ => Nat.Coprime p.fst p.snd ∧ rad (p.fst * p.snd) = r)).card
≤ (N : ℝ) ^ δ₁ * ((Finset.Icc 1 (N * N)).filter (fun n' => rad n' = r)).card := by
  intro δ₁ hδ₁

  -- Choose a small enough ε' such that we can apply lemma17
  let ε' := min (δ₁ / 4) (ε / 2)
  have hε'_pos : ε' > 0 := by
    simp only [ε', lt_min_iff]
    constructor
    · exact div_pos hδ₁ (by norm_num : (0 : ℝ) < 4)
    · exact half_pos hε
  have hε'_small : ε' < 1/100 := by
    simp only [ε']
    exact lt_of_le_of_lt (min_le_right _ _) (by linarith)

  -- Get the tau bound from lemma17
  obtain ⟨C, hC_pos, hC_bound⟩ := lemma17 ε' hε'_pos hε'_small

  -- Choose N₁ large enough
  use max (Nat.ceil (C ^ (2 / δ₁))) 2

  intros N hN r hr

  -- Apply lemma61 to get the initial bound
  have h_lemma61 := lemma61 N r

  -- Show that radical_set r (N * N) and the filter set have the same cardinality
  have h_same_card : (radical_set r (N * N)).card = ((Finset.Icc 1 (N * N)).filter (fun n' => rad n' = r)).card := by
    -- radical_set excludes 0, but since r ≥ 1 and rad 0 = 0, this doesn't matter
    conv_lhs => rw [radical_set]
    congr 1
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    constructor
    · intro ⟨h_lt, h_rad⟩
      by_cases hn : n = 0
      · subst hn
        simp [rad] at h_rad
        omega
      · exact ⟨⟨Nat.one_le_iff_ne_zero.mpr hn, Nat.le_of_succ_le_succ h_lt⟩, h_rad⟩
    · intro ⟨⟨h_ge, h_le⟩, h_rad⟩
      exact ⟨Nat.lt_succ_of_le h_le, h_rad⟩

  -- Bound each tau(n) for n in the radical set
  have h_sum_bound : (∑ n in radical_set r (N * N), tau n : ℝ) ≤
                     C * (N : ℝ) ^ (2 * ε') * (radical_set r (N * N)).card := by
    -- For each n in radical_set r (N * N), we have n ≥ 1 (since rad n = r ≥ 1)
    -- and n ≤ N * N
    have h_n_bounds : ∀ n ∈ radical_set r (N * N), 1 ≤ n ∧ n ≤ N * N := by
      intro n hn
      simp only [radical_set, Finset.mem_filter, Finset.mem_range] at hn
      constructor
      · by_contra h_not
        push_neg at h_not
        have : n = 0 := by omega
        rw [this, rad] at hn
        simp at hn
        omega
      · exact Nat.le_of_succ_le_succ hn.1

    -- Apply tau bound to each term
    calc (∑ n in radical_set r (N * N), tau n : ℝ)
      = ∑ n in radical_set r (N * N), (tau n : ℝ) := by simp only [Nat.cast_sum]
      _ ≤ ∑ n in radical_set r (N * N), C * (n : ℝ) ^ ε' := by
        apply Finset.sum_le_sum
        intro n hn
        have ⟨h_ge, _⟩ := h_n_bounds n hn
        exact hC_bound n h_ge
      _ ≤ ∑ n in radical_set r (N * N), C * ((N * N) : ℝ) ^ ε' := by
        apply Finset.sum_le_sum
        intro n hn
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hC_pos)
        have ⟨_, h_le⟩ := h_n_bounds n hn
        have h_cast_N : ((N * N) : ℝ) = (N : ℝ) * (N : ℝ) := by norm_cast
        rw [h_cast_N]
        have h_n_le : (n : ℝ) ≤ (N : ℝ) * (N : ℝ) := by
          rw [← h_cast_N]
          norm_cast
        exact Real.rpow_le_rpow (Nat.cast_nonneg _) h_n_le (le_of_lt hε'_pos)
      _ = (radical_set r (N * N)).card * (C * ((N * N) : ℝ) ^ ε') := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ = C * ((N : ℝ) * (N : ℝ)) ^ ε' * (radical_set r (N * N)).card := by
        ring_nf
      _ = C * (N : ℝ) ^ (2 * ε') * (radical_set r (N * N)).card := by
        congr 2
        rw [mul_comm (N : ℝ), ← sq]
        rw [← Real.rpow_natCast (N : ℝ) 2, ← Real.rpow_mul (Nat.cast_nonneg N)]
        norm_num

  -- Now we need to show C * N^(2ε') ≤ N^δ₁
  have hN_pos : N ≥ 2 := by
    calc N ≥ max (Nat.ceil (C ^ (2 / δ₁))) 2 := hN
         _ ≥ 2 := le_max_right _ _

  have h_C_bound : C ≤ (N : ℝ) ^ (δ₁ / 2) := by
    have h1 : Nat.ceil (C ^ (2 / δ₁)) ≤ N := le_trans (le_max_left _ _) hN
    have h2 : C ^ (2 / δ₁) ≤ N := by
      exact le_trans (Nat.le_ceil _) (Nat.cast_le.mpr h1)
    -- Take (δ₁/2)-th power of both sides
    have h3 : (C ^ (2 / δ₁)) ^ (δ₁ / 2) ≤ (N : ℝ) ^ (δ₁ / 2) := by
      apply Real.rpow_le_rpow
      · exact Real.rpow_nonneg (le_of_lt hC_pos) _
      · exact h2
      · exact le_of_lt (half_pos hδ₁)
    rw [← Real.rpow_mul (le_of_lt hC_pos)] at h3
    have h_simplify : 2 / δ₁ * (δ₁ / 2) = 1 := by
      field_simp
    rw [h_simplify, Real.rpow_one] at h3
    exact h3

  have h_final_bound : C * (N : ℝ) ^ (2 * ε') ≤ (N : ℝ) ^ δ₁ := by
    have h_step1 : C * (N : ℝ) ^ (2 * ε') ≤ (N : ℝ) ^ (δ₁ / 2) * (N : ℝ) ^ (2 * ε') := by
      exact mul_le_mul_of_nonneg_right h_C_bound (Real.rpow_nonneg (Nat.cast_nonneg N) _)
    have h_step2 : (N : ℝ) ^ (δ₁ / 2) * (N : ℝ) ^ (2 * ε') = (N : ℝ) ^ (δ₁ / 2 + 2 * ε') := by
      rw [← Real.rpow_add (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hN_pos))]
    have h_step3 : (N : ℝ) ^ (δ₁ / 2 + 2 * ε') ≤ (N : ℝ) ^ δ₁ := by
      apply Real.rpow_le_rpow_of_exponent_le
      · exact Nat.one_le_cast.mpr (le_trans (by norm_num : 1 ≤ 2) hN_pos)
      · simp only [ε']
        have h_ineq : 2 * min (δ₁ / 4) (ε / 2) ≤ 2 * (δ₁ / 4) := by
          exact mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num)
        calc δ₁ / 2 + 2 * min (δ₁ / 4) (ε / 2)
          ≤ δ₁ / 2 + 2 * (δ₁ / 4) := by linarith [h_ineq]
          _ = δ₁ / 2 + δ₁ / 2 := by ring
          _ = δ₁ := by ring
    calc C * (N : ℝ) ^ (2 * ε')
      ≤ (N : ℝ) ^ (δ₁ / 2) * (N : ℝ) ^ (2 * ε') := h_step1
      _ = (N : ℝ) ^ (δ₁ / 2 + 2 * ε') := h_step2
      _ ≤ (N : ℝ) ^ δ₁ := h_step3

  -- Combine everything
  calc ((((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter (fun p : ℕ × ℕ => Nat.Coprime p.fst p.snd ∧ rad (p.fst * p.snd) = r)).card : ℝ)
    = ↑(((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter (fun p : ℕ × ℕ => Nat.Coprime p.fst p.snd ∧ rad (p.fst * p.snd) = r)).card := by rfl
    _ ≤ ↑(∑ n in radical_set r (N * N), tau n) := by exact Nat.cast_le.mpr h_lemma61
    _ ≤ C * (N : ℝ) ^ (2 * ε') * (radical_set r (N * N)).card := h_sum_bound
    _ ≤ (N : ℝ) ^ δ₁ * (radical_set r (N * N)).card := by
      exact mul_le_mul_of_nonneg_right h_final_bound (Nat.cast_nonneg _)
    _ = (N : ℝ) ^ δ₁ * ↑((Finset.Icc 1 (N * N)).filter (fun n' => rad n' = r)).card := by
      rw [h_same_card]
lemma lemma62 (ε : ℝ) (hε : ε > 0) (hε_small : ε < 1/100)  :
  ∃ (N₀ : ℕ), ∀ (N : ℕ), N ≥ N₀ → ∀ (r : ℕ), r ≥ 1 →
    let S := (Finset.Icc 1 (N*N)).filter (fun n => rad n = r)
    (∑ n in S, (tau n : ℝ)) ≤ (S.card : ℝ) * ((N : ℝ) ^ ε) := by
  -- The key insight: for any ε > 0, there exists N₀ such that for N ≥ N₀,
  -- we have τ(n) ≤ N^ε for all n ≤ N²

  -- Use lemma17 with ε/3 to get a bound τ(n) ≤ C * n^(ε/3)
  have hε_third : ε / 3 > 0 := by linarith
  obtain ⟨C, hC_pos, hC_bound⟩ := lemma17 (ε / 3) hε_third (by linarith [hε_small])

  -- Choose N₀ large enough so that for N ≥ N₀:
  -- C * (N²)^(ε/3) ≤ N^ε
  -- This means C * N^(2ε/3) ≤ N^ε
  -- So C ≤ N^(ε - 2ε/3) = N^(ε/3)
  have : ∃ N₀ : ℕ, N₀ ≥ 1 ∧ ∀ N ≥ N₀, C ≤ (N : ℝ) ^ (ε / 3) := by
    -- Since ε/3 > 0, N^(ε/3) → ∞ as N → ∞, so we can find such N₀
    have : ∃ N₀ : ℕ, (N₀ : ℝ) ≥ C ^ (3 / ε) := by
      exact exists_nat_ge (C ^ (3 / ε))
    obtain ⟨N₀, hN₀_ge⟩ := this
    use max N₀ 1
    constructor
    · simp
    · intro N hN
      have hN_ge_N₀ : N ≥ N₀ := by
        calc N ≥ max N₀ 1 := hN
        _ ≥ N₀ := le_max_left N₀ 1
      have hN_real : (N : ℝ) ≥ (N₀ : ℝ) := Nat.cast_le.mpr hN_ge_N₀
      have hN_bound : (N : ℝ) ≥ C ^ (3 / ε) := le_trans hN₀_ge hN_real
      have hN_pow : (N : ℝ) ^ (ε / 3) ≥ (C ^ (3 / ε)) ^ (ε / 3) := by
        apply Real.rpow_le_rpow
        · apply Real.rpow_nonneg; exact hC_pos.le
        · exact hN_bound
        · linarith
      have h_simp : (C ^ (3 / ε)) ^ (ε / 3) = C := by
        rw [← Real.rpow_mul hC_pos.le]
        congr 1
        field_simp
      rw [h_simp] at hN_pow
      exact hN_pow

  obtain ⟨N₀, hN₀_ge, hN₀_bound⟩ := this
  use N₀
  intros N hN r hr

  -- Now prove the main bound
  have h_bound : ∀ n ∈ (Finset.Icc 1 (N*N)).filter (fun n => rad n = r),
    (tau n : ℝ) ≤ (N : ℝ) ^ ε := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    have hn_ge : 1 ≤ n := hn.1.1
    have hn_le : n ≤ N * N := hn.1.2

    -- Apply the divisor bound: τ(n) ≤ C * n^(ε/3)
    have h_tau : (tau n : ℝ) ≤ C * ((n : ℝ) ^ (ε / 3)) := hC_bound n hn_ge

    -- Since n ≤ N², we have n^(ε/3) ≤ (N²)^(ε/3) = N^(2ε/3)
    have h_n_bound : (n : ℝ) ^ (ε / 3) ≤ ((N * N : ℕ) : ℝ) ^ (ε / 3) := by
      apply Real.rpow_le_rpow
      · exact Nat.cast_nonneg n
      · exact Nat.cast_le.mpr hn_le
      · linarith

    have h_N2_pow : ((N * N : ℕ) : ℝ) ^ (ε / 3) = (N : ℝ) ^ (2 * ε / 3) := by
      rw [Nat.cast_mul]
      rw [Real.mul_rpow (Nat.cast_nonneg N) (Nat.cast_nonneg N)]
      rw [← Real.rpow_add (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp (by linarith [hN₀_ge, hN]))))]
      ring_nf

    rw [h_N2_pow] at h_n_bound

    -- Now use our choice of N₀: C ≤ N^(ε/3)
    have hC_N : C ≤ (N : ℝ) ^ (ε / 3) := hN₀_bound N hN

    -- Combine everything
    calc (tau n : ℝ) ≤ C * ((n : ℝ) ^ (ε / 3)) := h_tau
    _ ≤ C * (N : ℝ) ^ (2 * ε / 3) := by
      apply mul_le_mul_of_nonneg_left h_n_bound hC_pos.le
    _ ≤ ((N : ℝ) ^ (ε / 3)) * (N : ℝ) ^ (2 * ε / 3) := by
      apply mul_le_mul_of_nonneg_right hC_N
      apply Real.rpow_nonneg; exact Nat.cast_nonneg N
    _ = (N : ℝ) ^ (ε / 3 + 2 * ε / 3) := by
      rw [← Real.rpow_add (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp (by linarith [hN₀_ge, hN]))))]
    _ = (N : ℝ) ^ ε := by ring_nf

  -- Apply the bound to the sum
  calc (∑ n in (Finset.Icc 1 (N*N)).filter (fun n => rad n = r), (tau n : ℝ))
      ≤ ∑ n in (Finset.Icc 1 (N*N)).filter (fun n => rad n = r), (N : ℝ) ^ ε := by
        apply Finset.sum_le_sum h_bound
    _ = ((Finset.Icc 1 (N*N)).filter (fun n => rad n = r)).card * (N : ℝ) ^ ε := by
        rw [Finset.sum_const, nsmul_eq_mul]

lemma adaptive_constant_absorption (ε' : ℝ) (hε' : ε' > 0) :
  ∃ (δ : ℝ) (N₀ : ℕ), δ > 0 ∧ δ < 1/100 ∧ N₀ ≥ 1 ∧ ∀ N ≥ N₀, (3 : ℝ) * (N : ℝ) ^ δ ≤ (N : ℝ) ^ ε' := by
  -- Choose δ = min(ε'/2, 1/200)
  let δ := min (ε' / 2) (1 / 200)

  -- Show δ > 0
  have hδ_pos : δ > 0 := by
    apply lt_min
    · linarith [hε']
    · norm_num

  -- Show δ < 1/100
  have hδ_small : δ < 1/100 := by
    have h1 : (1 : ℝ) / 200 < 1 / 100 := by norm_num
    exact lt_of_le_of_lt (min_le_right _ _) h1

  -- Show ε' - δ > 0
  have hε'_δ_pos : ε' - δ > 0 := by
    have h1 : δ ≤ ε' / 2 := min_le_left _ _
    linarith [hε']

  -- Since ε' - δ > 0, there exists a large enough N₀
  have : ∃ N₀ : ℕ, N₀ ≥ 1 ∧ (N₀ : ℝ) ^ (ε' - δ) ≥ 3 := by
    -- Find a natural number larger than 3^(1/(ε' - δ))
    have h_target_pos : (3 : ℝ) ^ (1 / (ε' - δ)) > 0 := Real.rpow_pos_of_pos (by norm_num) _
    obtain ⟨n, hn⟩ := exists_nat_gt ((3 : ℝ) ^ (1 / (ε' - δ)))
    use max n 1
    constructor
    · exact le_max_right n 1
    · -- Show (max n 1 : ℝ)^(ε' - δ) ≥ 3
      have h_n_ge : (max n 1 : ℝ) ≥ (n : ℝ) := by aesop
      have h_n_gt : (n : ℝ) > (3 : ℝ) ^ (1 / (ε' - δ)) := hn
      have h_target_identity : ((3 : ℝ) ^ (1 / (ε' - δ))) ^ (ε' - δ) = 3 := by
        rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
        simp only [one_div]
        -- conv =>
        --   lhs
        --   rhs
        rw [inv_mul_cancel₀ (by linarith [hε'_δ_pos]) ]
        norm_num
      calc (max n 1) ^ (ε' - δ) ≥ (n : ℝ) ^ (ε' - δ) := by apply Real.rpow_le_rpow; exact Nat.cast_nonneg n; aesop; exact le_of_lt hε'_δ_pos
        _ ≥  ((3 : ℝ) ^ (1 / (ε' - δ))) ^ (ε' - δ) := by

          apply Real.rpow_le_rpow
          · exact le_of_lt h_target_pos
          · linarith [h_n_gt]
          · linarith [hε'_δ_pos]
        _ = 3 := h_target_identity

  obtain ⟨N₀, hN₀_ge, hN₀_pow⟩ := this

  use δ, N₀
  refine ⟨hδ_pos, hδ_small, hN₀_ge, ?_⟩

  intro N hN
  -- Show 3 * N^δ ≤ N^ε'
  have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp (le_trans hN₀_ge hN)))

  -- First establish that 3 ≤ N^(ε' - δ)
  have h_key : 3 ≤ (N : ℝ) ^ (ε' - δ) := by
    have hN_ge_N₀ : (N : ℝ) ≥ (N₀ : ℝ) := Nat.cast_le.mpr hN
    calc (3 : ℝ)
      ≤ (N₀ : ℝ) ^ (ε' - δ) := hN₀_pow
      _ ≤ (N : ℝ) ^ (ε' - δ) := by
        apply Real.rpow_le_rpow
        · exact Nat.cast_nonneg N₀
        · exact hN_ge_N₀
        · exact le_of_lt hε'_δ_pos

  -- Now use this to prove the main inequality
  -- We want to show 3 * N^δ ≤ N^ε'
  -- This follows from 3 ≤ N^(ε' - δ) by multiplying both sides by N^δ
  calc (3 : ℝ) * (N : ℝ) ^ δ
    ≤ ((N : ℝ) ^ (ε' - δ)) * (N : ℝ) ^ δ := by
        apply mul_le_mul_of_nonneg_right h_key
        exact le_of_lt (Real.rpow_pos_of_pos hN_pos δ)
    _ = (N : ℝ) ^ (ε' - δ + δ) := by
        rw [← Real.rpow_add hN_pos]
    _ = (N : ℝ) ^ ε' := by
        congr 1
        ring

lemma lemma63 (ε : ℝ) (N : ℕ) (hε : ε > 0) (hN : N ≥ 1) (h_exp_pos : (2 : ℝ) / 3 * (1 - ε) > 0) :
  ∀ ε' : ℝ, ε' > 0 → ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
    3 * (∑ r in Finset.Icc 1 (Nat.floor ((N : ℝ) ^ ((2 : ℝ) / 3 * (1 - ε)))), ∑ n in (Finset.Icc 1 (N * N)).filter (fun n' => rad n' = r), (tau n : ℝ))
    ≤ ∑ r in Finset.Icc 1 (Nat.floor ((N : ℝ) ^ ((2 : ℝ) / 3 * (1 - ε)))), ((Finset.Icc 1 (N * N)).filter (fun n' => rad n' = r)).card * ((N : ℝ) ^ ε') := by
  intro ε' hε'
  -- Use the adaptive constant absorption lemma to get appropriate δ and N₀₂
  obtain ⟨δ, N₀₂, hδ_pos, hδ_small, hN₀₂_ge, hN₀₂⟩ := adaptive_constant_absorption ε' hε'

  obtain ⟨N₀₁, hN₀₁⟩ := lemma62 δ hδ_pos hδ_small

  let N₀ := max N₀₁ N₀₂

  use N₀
  intro N hN

  have hN₁ : N ≥ N₀₁ := le_trans (le_max_left N₀₁ N₀₂) hN
  have hN₂ : N ≥ N₀₂ := le_trans (le_max_right N₀₁ N₀₂) hN

  -- Apply lemma62 to bound tau functions
  have h_tau_bound : ∀ r ∈ Finset.Icc 1 (Int.toNat ⌊(N : ℝ) ^ ((2 : ℝ) / 3 * (1 - ε))⌋),
    ∑ n in (Finset.Icc 1 (N * N)).filter (fun n' => rad n' = r), (tau n : ℝ) ≤
    ((Finset.Icc 1 (N * N)).filter (fun n' => rad n' = r)).card * ((N : ℝ) ^ δ) := by
    intro r hr
    have h_ge_1 : r ≥ 1 := by
      rw [Finset.mem_Icc] at hr
      exact hr.1
    exact hN₀₁ N hN₁ r h_ge_1

  -- Apply the bounds
  calc 3 * (∑ r in Finset.Icc 1 (Int.toNat ⌊(N : ℝ) ^ ((2 : ℝ) / 3 * (1 - ε))⌋), ∑ n in (Finset.Icc 1 (N * N)).filter (fun n' => rad n' = r), (tau n : ℝ))
      ≤ 3 * (∑ r in Finset.Icc 1 (Int.toNat ⌊(N : ℝ) ^ ((2 : ℝ) / 3 * (1 - ε))⌋), ((Finset.Icc 1 (N * N)).filter (fun n' => rad n' = r)).card * ((N : ℝ) ^ δ)) := by
        apply mul_le_mul_of_nonneg_left
        · apply Finset.sum_le_sum h_tau_bound
        · norm_num
    _ = ∑ r in Finset.Icc 1 (Int.toNat ⌊(N : ℝ) ^ ((2 : ℝ) / 3 * (1 - ε))⌋), 3 * (((Finset.Icc 1 (N * N)).filter (fun n' => rad n' = r)).card * ((N : ℝ) ^ δ)) := by
        rw [Finset.mul_sum]
    _ = ∑ r in Finset.Icc 1 (Int.toNat ⌊(N : ℝ) ^ ((2 : ℝ) / 3 * (1 - ε))⌋), ((Finset.Icc 1 (N * N)).filter (fun n' => rad n' = r)).card * (3 * ((N : ℝ) ^ δ)) := by
        congr 1; ext r; ring
    _ ≤ ∑ r in Finset.Icc 1 (Int.toNat ⌊(N : ℝ) ^ ((2 : ℝ) / 3 * (1 - ε))⌋), ((Finset.Icc 1 (N * N)).filter (fun n' => rad n' = r)).card * ((N : ℝ) ^ ε') := by
        apply Finset.sum_le_sum
        intro r hr
        apply mul_le_mul_of_nonneg_left (hN₀₂ N hN₂)
        exact Nat.cast_nonneg _
-- Lemma 64
lemma lemma64 (N : ℕ) (ε : ℝ) (hN : N ≥ 1) (hε : ε > 0) (hε_small : ε < 1/100)  (h_exp_pos : (2 : ℝ) / 3 * (1 - ε) > 0) :
  ∑ r in Finset.Icc 1 (Nat.floor ((N : ℝ) ^ ((2 : ℝ) / 3 * (1 - ε)))),
    ((Finset.Icc 1 (N * N)).filter (fun n => rad n = r)).card =
  ((Finset.Icc 1 (N * N)).filter (fun n => (rad n : ℝ) ≤ (N : ℝ) ^ ((2 : ℝ) / 3 * (1 - ε)))).card := by
  let X := (N : ℝ) ^ ((2 : ℝ) / 3 * (1 - ε))
  have hX_nonneg : 0 ≤ X := Real.rpow_nonneg (Nat.cast_nonneg N) _

  -- The key insight: partition the RHS set based on the exact value of rad(n)
  have h_partition : ((Finset.Icc 1 (N * N)).filter (fun n => (rad n : ℝ) ≤ X)) =
    (Finset.Icc 1 (Nat.floor X)).biUnion (fun r => (Finset.Icc 1 (N * N)).filter (fun n => rad n = r)) := by
    ext n
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · -- Forward direction: if n satisfies rad(n) ≤ X, then it belongs to some partition
      intro ⟨hn_range, h_rad_le_X⟩
      use rad n
      constructor
      · constructor
        · -- rad(n) ≥ 1 for n ≥ 1
          have h_ne_zero : n ≠ 0 := by
            linarith [hn_range.1]
          have h_rad_pos : rad n > 0 := by
            rw [rad, if_neg h_ne_zero]
            apply Finset.prod_pos
            intro p hp
            exact Nat.Prime.pos (Nat.prime_of_mem_primeFactors hp)
          exact h_rad_pos
        · -- rad(n) ≤ floor(X)
          rw [Nat.le_floor_iff hX_nonneg]
          exact h_rad_le_X
      · exact ⟨hn_range, rfl⟩
    · -- Backward direction: if n belongs to some partition, then rad(n) ≤ X
      intro ⟨r, ⟨⟨hr_ge, hr_le⟩, hn_range, h_rad_eq⟩⟩
      constructor
      · exact hn_range
      · rw [h_rad_eq]
        calc (r : ℝ) ≤ (Nat.floor X : ℝ) := Nat.cast_le.mpr hr_le
        _ ≤ X := Nat.floor_le hX_nonneg

  -- Apply the partition to get card equality
  rw [h_partition, Finset.card_biUnion]

  -- Show pairwise disjointness
  intro r₁ hr₁ r₂ hr₂ h_ne
  rw [Function.onFun]
  apply Finset.disjoint_left.mpr
  intro n hn₁ hn₂
  simp only [Finset.mem_filter] at hn₁ hn₂
  have h₁ : rad n = r₁ := hn₁.2
  have h₂ : rad n = r₂ := hn₂.2
  have : r₁ = r₂ := by rw [← h₁, h₂]
  exact h_ne this

lemma lemma65_step1_apply_lemma59 (N : ℕ) (ε : ℝ) [Fintype ↑(exceptionalSet N ε)] (hN : N ≥ 1) (hε : ε > 0) (hε_small : ε < 1/100) :
  ((exceptionalSet N ε).toFinset.card : ℝ) ≤ (3 : ℝ) * ((((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter (fun p : ℕ × ℕ => Nat.Coprime p.fst p.snd ∧ ((rad (p.fst * p.snd)) : ℝ) ≤ (N : ℝ) ^ ((2 : ℝ) / 3 * (1 - ε)))).card : ℝ) := by
  convert Nat.cast_le.mpr (lemma59 N ε hN hε hε_small)
  <;> aesop
  exact addLeftMono_of_addLeftStrictMono ℝ
  exact Real.instZeroLEOneClass
  exact IsStrictOrderedRing.toCharZero

lemma lemma65_step2_apply_lemma60 (N : ℕ) (ε : ℝ) (hN : N ≥ 1) (hε : ε > 0) (h_exp_pos : (2 : ℝ) / 3 * (1 - ε) > 0) :
  let K0 := (N : ℝ) ^ ((2 : ℝ) / 3 * (1 - ε))
  let S_pairs_le_K0_card := (((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter (fun p : ℕ × ℕ => Nat.Coprime p.fst p.snd ∧ ((rad (p.fst * p.snd)) : ℝ) ≤ K0)).card
  let Sum_r_S_pairs_eq_r_card := ∑ r_val in Finset.Icc 1 (Nat.floor K0), (((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter (fun p : ℕ × ℕ => Nat.Coprime p.fst p.snd ∧ rad (p.fst * p.snd) = r_val)).card
  (S_pairs_le_K0_card : ℝ) = (Sum_r_S_pairs_eq_r_card : ℝ) := by
  simp [lemma60 ε N hε hN h_exp_pos]

-- lemma Nat.cast_sum {α β : Type*} [AddCommMonoid α] [Semiring β] (s : Finset α) (f : α → ℕ) :
--   (↑(∑ x in s, f x) : β) = ∑ x in s, (f x : β) := by
--   exact Nat.cast_sum s f -- Using existing Mathlib lemma

-- theorem Finset.sum_mul_boole {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] (s : Finset M) (c : R) (f : M → R) :
--     (∑ x in s, f x) * c = ∑ x in s, f x * c := by
--   simp_rw [← smul_eq_mul, Finset.sum_smul, smul_eq_mul]


lemma lemma65_step3_apply_lemma61_new (N : ℕ) (ε : ℝ) (δ_half : ℝ)
    (hN : N ≥ 1) (hε : ε > 0) (hε_small : ε < 1/100) (h_exp_pos : (2 : ℝ) / 3 * (1 - ε) > 0)
    (h_δ_half_pos : δ_half > 0)
    (N₁ : ℕ) (h_lemma61_new_cond: N ≥ N₁ ∧ ∀ (r : ℕ), r ≥ 1 →
      ((((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter (fun p : ℕ × ℕ => Nat.Coprime p.fst p.snd ∧ rad (p.fst * p.snd) = r)).card : ℝ)
      ≤ (N : ℝ) ^ δ_half * (((Finset.Icc 1 (N * N)).filter (fun n' => rad n' = r)).card : ℝ)) :
  let K0 := (N : ℝ) ^ ((2 : ℝ) / 3 * (1 - ε))
  let Sum_r_S_pairs_eq_r_val := ∑ r_val in Finset.Icc 1 (Nat.floor K0), (((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter (fun p : ℕ × ℕ => Nat.Coprime p.fst p.snd ∧ rad (p.fst * p.snd) = r_val)).card
  let Sum_r_S_n_eq_r_NN_val := ∑ r_val in Finset.Icc 1 (Nat.floor K0), (((Finset.Icc 1 (N * N)).filter (fun n' => rad n' = r_val)).card)
  (Sum_r_S_pairs_eq_r_val : ℝ) ≤ (N : ℝ)^δ_half * (Sum_r_S_n_eq_r_NN_val : ℝ) :=
by
  -- The `let` bindings mean that K0, Sum_r_S_pairs_eq_r_val, and Sum_r_S_n_eq_r_NN_val
  -- are abbreviations for the expressions on their right-hand side within the proposition.

  -- Rewrite sums of natural numbers cast to real numbers as sums of cast natural numbers.
  -- This applies to the LHS, and to the sum part of the RHS.
  simp_rw [Nat.cast_sum]

  -- On the RHS, distribute the multiplication by (N : ℝ)^δ_half into the sum.
  -- (N : ℝ)^δ_half * (∑ r_val, ↑(card_n r_val)) = ∑ r_val, (N : ℝ)^δ_half * ↑(card_n r_val)
  rw [Finset.mul_sum]

  -- Now the goal is to show that a sum is less than or equal to another sum, term by term.
  -- ∑ r_val, ↑(card_pairs r_val) ≤ ∑ r_val, (N : ℝ)^δ_half * ↑(card_n r_val)
  apply Finset.sum_le_sum
  intros r_val hr_val_in_Icc

  -- For each r_val in the summation range, we need to prove:
  -- ↑(card_pairs r_val) ≤ (N : ℝ)^δ_half * ↑(card_n r_val)

  -- Unpack the hypothesis h_lemma61_new_cond.
  -- h_lemma61_new_cond.1 is N ≥ N₁ (implicitly used as a condition for .2)
  -- h_lemma61_new_cond.2 is the per-term inequality.
  have h_term_bound_prop := h_lemma61_new_cond.2

  -- To apply h_term_bound_prop, we need to show r_val ≥ 1.
  -- This follows from r_val ∈ Finset.Icc 1 (Nat.floor K0).
  have hr_val_ge_1 : r_val ≥ 1 := by
    rw [Finset.mem_Icc] at hr_val_in_Icc
    exact hr_val_in_Icc.1

  -- Apply the per-term inequality from h_lemma61_new_cond.
  exact h_term_bound_prop r_val hr_val_ge_1
lemma lemma65_step4_factor_out_power (N : ℕ) (ε : ℝ) (δ_half : ℝ)
    (h_exp_pos : (2 : ℝ) / 3 * (1 - ε) > 0) :
  let K0 := (N : ℝ) ^ ((2 : ℝ) / 3 * (1 - ε))
  let Sum_Term_C_val := ∑ r_val in Finset.Icc 1 (Nat.floor K0), (N : ℝ)^δ_half * ((((Finset.Icc 1 (N*N)).filter (fun n' => rad n' = r_val)).card) : ℝ)
  let Factored_Term_D_val := (N : ℝ)^δ_half * (∑ r_val in Finset.Icc 1 (Nat.floor K0), ((((Finset.Icc 1 (N*N)).filter (fun n' => rad n' = r_val)).card) : ℝ))
  Sum_Term_C_val = Factored_Term_D_val := by
  simp_rw [← Finset.mul_sum] -- This is for ℝ, sum of casted Nat should be cast of sum of Nat first.
  -- The sum is ∑ (N^δ/2 * cast card). This is N^δ/2 * ∑ (cast card).
  -- Need to be careful with types.
  -- ∑ r, ( (N:ℝ)^δ_half * ( (T_r:ℕ) : ℝ) ) = (N:ℝ)^δ_half * ∑ r, ( (T_r:ℕ) : ℝ)

lemma lemma65_step5_apply_lemma64 (N : ℕ) (ε : ℝ) (hN : N ≥ 1) (hε : ε > 0) (hε_small : ε < 1/100) (h_exp_pos : (2 : ℝ) / 3 * (1 - ε) > 0) :
  let K0 := (N : ℝ) ^ ((2 : ℝ) / 3 * (1 - ε))
  let Sum_r_S_n_eq_r_NN_card := ∑ r_val in Finset.Icc 1 (Nat.floor K0), (((Finset.Icc 1 (N * N)).filter (fun n' => rad n' = r_val)).card)
  let S_n_le_K0_NN_card := ((Finset.Icc 1 (N*N)).filter (fun n => (rad n : ℝ) ≤ K0)).card
  (Sum_r_S_n_eq_r_NN_card : ℝ) = (S_n_le_K0_NN_card : ℝ) := by
  simp [lemma64 N ε hN hε hε_small h_exp_pos]

lemma lemma65_step6_apply_absorption (N : ℕ) (δ : ℝ)
    (h_δ_pos : δ > 0)
    (N_abs : ℕ) (h_absorption_cond : N ≥ N_abs ∧ (3 : ℝ) * (N : ℝ)^(δ/2) ≤ (N : ℝ)^δ)
    (Term_E_factor : ℝ) (h_factor_nonneg : Term_E_factor ≥ 0) :
  (3 : ℝ) * (N : ℝ)^(δ/2) * Term_E_factor ≤ (N : ℝ)^δ * Term_E_factor := by
  exact mul_le_mul_of_nonneg_right h_absorption_cond.2 h_factor_nonneg


lemma lemma65 (ε : ℝ) (hε : ε > 0) (hε_small : ε < 1/100) (h_exp_pos : (2 : ℝ) / 3 * (1 - ε) > 0) :
  ∀ δ : ℝ, δ > 0 → ∃ N₀ : ℕ, ∀ (N : ℕ) [Fintype ↑(exceptionalSet N ε)], N ≥ N₀ →
    ((exceptionalSet N ε).toFinset.card : ℝ) ≤ (N : ℝ) ^ δ * (((Finset.Icc 1 (N * N)).filter (fun n => (rad n : ℝ) ≤ (N : ℝ) ^ ((2 : ℝ) / 3 * (1 - ε)))).card : ℝ) := by
  intro δ hδ

  have hδ_half : δ / 2 > 0 := by linarith [hδ]
  obtain ⟨N₁, hN₁_cond⟩ := lemma61_new ε hε hε_small (δ / 2) hδ_half

  obtain ⟨hN_abs_const_cond, N_abs_const, n⟩ := adaptive_constant_absorption (δ/2) hδ_half
  -- The N_abs_const from adaptive_constant_absorption is N₂ in the informal proof.
  -- The δ_small from adaptive_constant_absorption is not directly used here,
  -- as we are applying the result of adaptive_constant_absorption which already incorporates it.

  let N_for_final_abs := Nat.ceil ((3 : ℝ) ^ (2 / δ))
  have hN_for_final_abs_ge_1 : N_for_final_abs ≥ 1 := by
    have : (3 : ℝ) ^ (2 / δ) > 0 := by  exact Real.rpow_pos_of_pos (by linarith) (2 / δ)
    exact Nat.one_le_ceil_iff.mpr this

  -- Adjust N₀_final to include N_for_final_abs
  let N₀_final := max N₁ N_for_final_abs -- Or max (max N₁ N_abs_const_from_adaptive) N_for_final_abs if adaptive is used elsewhere
  use N₀_final
  intro N inst_Fintype hN_ge_N₀_final

  have hN_ge_1 : N ≥ 1 := by -- This proof needs N₀_final ≥ 1
    apply le_trans _ hN_ge_N₀_final
    exact le_trans hN_for_final_abs_ge_1 (le_max_right N₁ N_for_final_abs)
  have direct_absorption_inequality : (3 : ℝ) * (N : ℝ)^(δ/2) ≤ (N : ℝ)^δ := by
    have h_N_large : (N : ℝ) ≥ (3 : ℝ) ^ (2 / δ) := by
      -- have : (N_for_final_abs : ℝ) ≤ N:= by
      have h1: (N_for_final_abs : ℝ) ≤ (N₀_final : ℝ) := by convert Nat.le_max_right N₁ N_for_final_abs; aesop
      have h2: (3 ^ (2 / δ) : ℝ) ≤ N_for_final_abs := by exact Nat.le_ceil (3 ^ (2 / δ))
      rw [GE.ge] at hN_ge_N₀_final
      have h3: (N₀_final : ℝ) ≤ (N : ℝ) := by aesop
      linarith
    have hNReal_ge1 : (N : ℝ) ≥ 1:= by exact Nat.one_le_cast.mpr hN_ge_1
    -- Step 2: Deduce properties of δ/2 and 2/δ.
    have h_delta_div_two_gt_zero : δ / 2 > 0 := hδ_half -- from h_delta_gt_zero
    have h_two_div_delta_gt_zero : 2 / δ > 0 := by aesop -- from h_delta_gt_zero

    -- Step 3: Establish that the base of the power in h_N_large, 3^(2/δ), is greater than 1.
    have h_base_of_rhs_power_gt_one : (3 : ℝ) > 1 := by simp -- 3 > 1
    have h_three_pow_two_div_delta_gt_one : (3 : ℝ) ^ (2 / δ) > 1 := by exact Real.one_lt_rpow h_base_of_rhs_power_gt_one h_two_div_delta_gt_zero
 -- from h_base_of_rhs_power_gt_one, h_two_div_delta_gt_zero

    -- Step 4: Establish that ↑N > 1.
    have h_upN_gt_one : (N : ℝ) > 1 := by exact gt_of_ge_of_gt h_N_large h_three_pow_two_div_delta_gt_one
  -- from h_N_large and h_three_pow_two_div_delta_gt_one

    -- Step 5: Establish that (↑N)^(δ/2) is positive, allowing it to be a divisor or multiplier in inequalities.
    have h_upN_pow_delta_div_two_gt_zero : (N : ℝ) ^ (δ / 2) > 0 := by
      have h_N_real_pos : (N : ℝ) > 0 := by linarith [h_upN_gt_one] -- (N : ℝ) > 1 > 0
      exact Real.rpow_pos_of_pos h_N_real_pos (δ / 2) -- from h_upN_gt_one and h_delta_div_two_gt_zero (or ↑N > 0 which is implied)

    -- Step 6: Show equivalence of the goal with its simplified form.
    -- (↑N)^δ can be rewritten as (↑N)^(δ/2) * (↑N)^(δ/2).
    have h_upN_pow_delta_eq_prod : (N : ℝ) ^ δ = (N : ℝ) ^ (δ / 2) * (N : ℝ) ^ (δ / 2) := by
      have : N > 0 := by linarith
      nth_rewrite 1 [← add_halves δ]
      -- Apply the real power rule x^(y+z) = x^y * x^z for x > 0.
      -- Real.rpow_add_of_pos requires the base to be positive (hN_pos).
      -- The exponents (δ / 2) and (δ / 2) are inferred by Lean.
      refine Real.rpow_add' ?_ ?_ -- by rpow_add_left_basis (needs ↑N ≥ 0), as δ = δ/2 + δ/2. From h_upN_gt_one, ↑N > 0.
      <;> aesop

    have h_goal_iff_simplified : (3 * (↑N) ^ (δ / 2) ≤ (N : ℝ) ^ δ) ↔ (3 ≤ (N : ℝ) ^ (δ / 2)) := by
      rw [h_upN_pow_delta_eq_prod]
      exact mul_le_mul_right h_upN_pow_delta_div_two_gt_zero

 -- using h_upN_pow_delta_eq_prod and properties of inequalities with positive multipliers (h_upN_pow_delta_div_two_gt_zero).

    -- Step 7: Apply the exponent δ/2 to both sides of h_N_large.
    -- Since δ/2 > 0 and bases are positive (↑N > 1 and 3^(2/δ) > 1), the inequality direction is preserved.
    have h_upN_pow_ge_intermediate_pow : (N : ℝ) ^ (δ / 2) ≥ (3 ^ (2 / δ)) ^ (δ / 2) := by
      apply Real.rpow_le_rpow
      · linarith [h_three_pow_two_div_delta_gt_one]
      · exact h_N_large
      · linarith [hδ_half]
      -- from h_N_large, h_delta_div_two_gt_zero, h_upN_gt_one, h_three_pow_two_div_delta_gt_one

    -- Step 8: Simplify the right-hand side of the new inequality: (3^(2/δ))^(δ/2).
    have h_exponent_product_is_one : (2 / δ) * (δ / 2) = 1 := by ring_nf; apply mul_inv_cancel₀; linarith-- by field rules, using h_delta_gt_zero (so δ ≠ 0).
    have h_rhs_pow_eq_three_pow_one : ((3 : ℝ) ^ (2 / δ)) ^ (δ / 2) = 3 ^ ((2 / δ) * (δ / 2)) := by rw [Real.rpow_mul]; linarith -- by
    have h_rhs_simplified_to_three : ((3 : ℝ) ^ (2 / δ)) ^ (δ / 2) = (3 : ℝ) := by
      aesop -- from h_rhs_pow_eq_three_pow_one, h_exponent_product_is_one, and Real.rpow_one.

    -- Step 9: Conclude the simplified inequality.
    have h_simplified_ineq_proved : (3 : ℝ) ≤ (N : ℝ) ^ (δ / 2) := by
      exact ge_trans h_upN_pow_ge_intermediate_pow (Eq.ge h_rhs_simplified_to_three)

       -- from h_upN_pow_ge_intermediate_pow and h_rhs_simplified_to_three, using transitivity of ≥.
    have ex (a b c : ℝ) (h : 0 < a) : (b ≤ c) → (b * a ≤ c * a) := by
      apply (mul_le_mul_iff_of_pos_right h).mpr
    have h₅ := ex ((N : ℝ) ^ (δ / 2)) 3 ((N : ℝ) ^ (δ / 2)) h_upN_pow_delta_div_two_gt_zero h_simplified_ineq_proved
    convert h₅



  have h_exp_identity : ((3 : ℝ) ^ (2 / δ)) ^ (δ / 2) = 3 := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]; field_simp [ne_of_gt hδ, show (2:ℝ)≠0 by norm_num]


  have hN_ge_N₁ := le_trans (le_max_left N₁ N_for_final_abs) hN_ge_N₀_final
  have hN_ge_N_for_final_abs := le_trans (le_max_right N₁ N_for_final_abs) hN_ge_N₀_final

  let K0_val N ε := (N : ℝ) ^ ((2 : ℝ) / 3 * (1 - ε))
  let S_pairs_le_K0_card N ε := (((Finset.Icc (1 : ℕ) N) ×ˢ (Finset.Icc 1 N)).filter (fun p : ℕ × ℕ => Nat.Coprime p.fst p.snd ∧ ((rad (p.fst * p.snd)) : ℝ) ≤ K0_val N ε)).card
  let Sum_r_S_pairs_eq_r_card (N : ℕ) ε := ∑ r_val in Finset.Icc 1 (Nat.floor (K0_val N ε)), (((Finset.Icc (1 : ℕ) (N : ℕ)) ×ˢ (Finset.Icc (1 : ℕ) (N : ℕ))).filter (fun p : ℕ × ℕ => Nat.Coprime p.fst p.snd ∧ rad (p.fst * p.snd) = r_val)).card
  let Sum_r_S_n_eq_r_NN_card (N : ℕ) ε := ∑ r_val in Finset.Icc 1 (Nat.floor (K0_val N ε)), (((Finset.Icc 1 ((N * N) : ℕ)).filter (fun n' => rad n' = r_val)).card)
  let S_n_le_K0_NN_card N ε := ((Finset.Icc 1 ((N*N) : ℕ)).filter (fun n => (rad n : ℝ) ≤ K0_val N ε)).card

  calc
    ((exceptionalSet N ε).toFinset.card : ℝ)
    _ ≤ (3 : ℝ) * (S_pairs_le_K0_card N ε : ℝ) := by
        exact lemma65_step1_apply_lemma59 N ε hN_ge_1 hε hε_small
    _ = (3 : ℝ) * (Sum_r_S_pairs_eq_r_card N ε : ℝ) := by
        rw [lemma65_step2_apply_lemma60 N ε hN_ge_1 hε h_exp_pos]
    _ ≤ (3 : ℝ) * ((N : ℝ)^(δ/2) * (Sum_r_S_n_eq_r_NN_card N ε : ℝ)) := by
        apply mul_le_mul_of_nonneg_left
        · exact lemma65_step3_apply_lemma61_new N ε (δ/2) hN_ge_1 hε hε_small h_exp_pos hδ_half N₁ ⟨hN_ge_N₁, hN₁_cond N hN_ge_N₁⟩
        · norm_num -- 3 ≥ 0
    _ = ((3 : ℝ) * (N : ℝ)^(δ/2)) * (Sum_r_S_n_eq_r_NN_card N ε : ℝ) := by ring
    _ = ((3 : ℝ) * (N : ℝ)^(δ/2)) * (S_n_le_K0_NN_card N ε : ℝ) := by
        rw [lemma65_step5_apply_lemma64 N ε hN_ge_1 hε hε_small h_exp_pos]
    _ ≤ (N : ℝ)^δ * (S_n_le_K0_NN_card N ε : ℝ) := by
        have h_factor_nonneg : (S_n_le_K0_NN_card N ε : ℝ) ≥ 0 := by exact Nat.cast_nonneg _
        exact lemma65_step6_apply_absorption N δ hδ N_for_final_abs ⟨hN_ge_N_for_final_abs, direct_absorption_inequality⟩ _ h_factor_nonneg

lemma lemma66 (ε : ℝ) (hε : ε > 0) (hε_small : ε < 1/100) (h_exp_pos : (2 : ℝ) / 3 * (1 - ε) > 0) :
  ∀ δ : ℝ, δ > 0 → δ < 1/100 → ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
    ((Finset.Icc 1 (N*N)).filter (fun n => (rad n : ℝ) ≤ (N : ℝ) ^ ((2 : ℝ) / 3 * (1 - ε)))).card ≤ (N : ℝ) ^ ((2 : ℝ) / 3 * (1 - ε) + δ) := by
  intro δ hδ hδmax
  -- Apply corollary52 with ε' = δ/2
  obtain ⟨N₀', hN₀'⟩ := corollary52 (δ / 2) (by linarith) (by linarith [hδmax])
  -- Choose N₀ to ensure N ≥ 1
  use max N₀' 1
  intro N hN
  -- Set lambda = (1 : ℝ) / 3 - ε / 2
  set lambda := (1 : ℝ) / 3 - ε / 3 with hlambda_def
  -- Verify lambda satisfies the conditions
  have hlambda_pos : 0 < lambda := by
    rw [hlambda_def]
    linarith [h_exp_pos]
  have hlambda_lt_one : lambda < 1 := by
    rw [hlambda_def]
    linarith
  -- N ≥ 1
  have hN_ge_1 : N ≥ 1 := by linarith [Nat.le_max_right N₀' 1, hN]
  -- N*N ≥ N₀'
  have hNN_ge : N * N ≥ N₀' := by
    have : N ≥ N₀' := by linarith [Nat.le_max_left N₀' 1, hN]
    calc N * N ≥ N * 1 := Nat.mul_le_mul_left N hN_ge_1
    _ = N := by ring
    _ ≥ N₀' := this
  -- Apply corollary52 to N²
  have h_cor52 := hN₀' (N * N) hNN_ge lambda hlambda_pos hlambda_lt_one
  -- The key observation: we need to relate the powers
  have h_power_eq : ((N : ℝ) * (N : ℝ)) ^ lambda = (N : ℝ) ^ ((2 : ℝ) / 3 * (1 - ε)) := by
    have hN_nonneg : (0 : ℝ) ≤ N := by norm_cast; exact Nat.zero_le N
    rw [hlambda_def]
    rw [← sq (N : ℝ)]
    rw [← Real.rpow_natCast (N : ℝ) 2]
    rw [← Real.rpow_mul hN_nonneg]
    congr 1
    ring
  -- Apply the equality
  have h_cast : ((N * N : ℕ) : ℝ) = (N : ℝ) * (N : ℝ) := by norm_cast
  rw [h_cast] at h_cor52
  rw [h_power_eq] at h_cor52
  -- Show the final bound
  convert h_cor52 using 1
  -- Show ((N : ℝ) * (N : ℝ)) ^ (lambda + δ / 2) = (N : ℝ) ^ ((2 : ℝ) / 3 - ε + δ)
  have hN_nonneg : (0 : ℝ) ≤ N := by norm_cast; exact Nat.zero_le N
  rw [← sq (N : ℝ)]
  rw [← Real.rpow_natCast (N : ℝ) 2]
  rw [← Real.rpow_mul hN_nonneg]
  congr 1
  rw [hlambda_def]
  ring

theorem theorem67 (ε : ℝ) (hε : ε > 0) (hε_small : ε < 1/100)  :
  ∃ (C : ℝ), C > 0 ∧ ∃ (N₀ : ℕ), ∀ (N : ℕ) [Fintype ↑(exceptionalSet N ε)], N ≥ N₀ →
    ((exceptionalSet N ε).toFinset.card : ℝ) ≤ C * (N : ℝ) ^ ((2: ℝ) / 3) := by
  -- Choose δ small enough so that 2δ < ε/2
  set δ := ε / 4 with hδ_def
  have hδ_pos : δ > 0 := by rw [hδ_def]; linarith
  have hδ_small : δ < 1/100 := by rw [hδ_def]; linarith [hε_small]

  -- Need the condition that 2/3 - ε > 0
  have h_exp_pos : (2 : ℝ) / 3 * (1 - ε) > 0 := by linarith [hε_small]

  -- Apply lemma65 to get bound on exceptional set
  obtain ⟨N₁, h₁⟩ := lemma65 ε hε hε_small h_exp_pos δ hδ_pos

  -- Apply lemma66 to get bound on radical set
  obtain ⟨N₂, h₂⟩ := lemma66 ε hε hε_small h_exp_pos δ hδ_pos hδ_small

  -- Choose C = 1
  use 1
  constructor
  · -- Show 1 > 0
    norm_num
  · -- Choose N₀ = max N₁ N₂, but at least 1
    use max (max N₁ N₂) 1
    -- Main bound
    intro N hN_inst hN_ge

    -- Apply lemma65
    have h_N1_ge : N ≥ N₁ := by
      calc N ≥ max (max N₁ N₂) 1 := hN_ge
      _ ≥ max N₁ N₂ := le_max_left _ _
      _ ≥ N₁ := le_max_left _ _
    have h_le_65 := h₁ N h_N1_ge

    -- Apply lemma66
    have h_N2_ge : N ≥ N₂ := by
      calc N ≥ max (max N₁ N₂) 1 := hN_ge
      _ ≥ max N₁ N₂ := le_max_left _ _
      _ ≥ N₂ := le_max_right _ _
    have h_le_66 := h₂ N h_N2_ge

    -- Establish that N ≥ 1
    have hN_pos : 1 ≤ N := by
      calc N ≥ max (max N₁ N₂) 1 := hN_ge
      _ ≥ 1 := le_max_right _ _

    -- For Real.rpow_add we need 0 < N
    have hN_pos_real : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hN_pos))

    -- For Real.rpow_le_rpow_of_exponent_le we need 1 ≤ (N : ℝ)
    have hN_one_le : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr hN_pos

    -- Key inequality for exponents
    have h_exp_ineq : (2 : ℝ) / 3 * (1 - ε) + 2 * δ ≤ (2 : ℝ) / 3 := by
      rw [hδ_def]
      linarith

    -- Use 1 * x = x
    rw [one_mul]

    -- Prove the bound directly
    calc ((exceptionalSet N ε).toFinset.card : ℝ)
        ≤ (N : ℝ) ^ δ * (((Finset.Icc 1 (N * N)).filter (fun n => rad n ≤ (N : ℝ) ^ ((2 : ℝ) / 3 * (1 - ε)))).card : ℝ) := h_le_65
      _ ≤ (N : ℝ) ^ δ * (N : ℝ) ^ ((2 : ℝ) / 3 * (1 - ε) + δ) := by
        apply mul_le_mul_of_nonneg_left h_le_66
        apply Real.rpow_nonneg (le_of_lt hN_pos_real)
      _ = (N : ℝ) ^ (δ + ((2 : ℝ) / 3 * (1 - ε) + δ)) := by
        rw [← Real.rpow_add hN_pos_real]
      _ = (N : ℝ) ^ ((2 : ℝ) / 3 * (1 - ε) + 2 * δ) := by ring_nf
      _ ≤ (N : ℝ) ^ ((2 : ℝ) / 3) := by
        apply Real.rpow_le_rpow_of_exponent_le hN_one_le h_exp_ineq
