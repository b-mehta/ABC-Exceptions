import ABCExceptions.TrivialBound
import ABCExceptions.Section2

section compat


lemma rad_eq (n : ℕ) (hn : n ≠ 0) : rad n = UniqueFactorizationMonoid.radical n := by
  rw [rad, if_neg hn, UniqueFactorizationMonoid.radical,
    UniqueFactorizationMonoid.primeFactors_eq_natPrimeFactors]

lemma exceptionalSet_eq (N : ℕ) (ε : ℝ) :
    Finset.abcExceptionsBelow ε N = exceptionalSet N ε := by
  ext ⟨a, b, c⟩
  simp only [Finset.abcExceptionsBelow, Finset.coe_filter, Finset.mem_Icc, Set.mem_setOf_eq,
    Prod.mk_le_mk, exceptionalSet]
  constructor
  · simp only [and_imp]
    intro hab hac hbc habc hrad ha1 hb1 hc1 haN hbN hcN
    rw [rad_eq]
    · simpa [*]
    simp
    omega
  · simp only [and_imp]
    intro ha1 haN hb1 hbN hc1 hcN habc hab
    rw [rad_eq]
    · simp_all [Nat.Coprime]
      simp [← habc, hab, Nat.gcd_comm]
    · simp
      omega

lemma finite_exceptionalSet {N ε} : (exceptionalSet N ε).Finite := by
  rw [← exceptionalSet_eq]
  simp

theorem theorem67' (ε : ℝ) (hε : ε > 0) (hε_small : ε < 1/100)  :
    ∃ (C : ℝ), C > 0 ∧ ∃ (N₀ : ℕ), ∀ (N : ℕ), N ≥ N₀ →
    ((exceptionalSet N ε).ncard : ℝ) ≤ C * (N : ℝ) ^ ((2 : ℝ) / 3) := by
  obtain ⟨C, hC, N₀, hN₀⟩ := theorem67 ε hε hε_small
  use C, hC, N₀
  intro N hN
  have : Finite (exceptionalSet N ε) := finite_exceptionalSet
  have : Fintype (exceptionalSet N ε) := Fintype.ofFinite _
  refine (hN₀ N hN).trans_eq' (by rw [Set.ncard_eq_toFinset_card'])

theorem theorem67'' (ε : ℝ) (hε : ε > 0) (hε_small : ε < 1/100) :
    (fun N ↦ ((exceptionalSet N ε).ncard : ℝ)) =O[Filter.atTop]
    (fun N : ℕ ↦ (N : ℝ) ^ (2 / 3 : ℝ)) := by
  rw [Asymptotics.isBigO_iff]
  obtain ⟨C, hC₀, hC⟩ := theorem67' ε hε hε_small
  use C
  simpa [Real.abs_rpow_of_nonneg]

end compat

open Finset UniqueFactorizationMonoid

namespace demo

theorem mem_abcExceptions (ε : ℝ) (a b c : ℕ) :
    (a, b, c) ∈ abcExceptions ε ↔
      0 < a ∧ 0 < b ∧ 0 < c ∧
      a.Coprime b ∧ a.Coprime c ∧ b.Coprime c ∧
      a + b = c ∧
      radical (a * b * c) ^ (1 + ε) < (c : ℝ) :=
  _root_.mem_abcExceptions ..

theorem mem_abcExceptionsBelow (X : ℕ) (ε : ℝ) (a b c : ℕ) :
    (a, b, c) ∈ Finset.abcExceptionsBelow ε X ↔
      a.Coprime b ∧ a.Coprime c ∧ b.Coprime c ∧
      a + b = c ∧
      radical (a * b * c) < (c : ℝ) ^ (1 - ε) ∧
      (a, b, c) ∈ Set.Icc (1, 1, 1) (X, X, X) :=
  Finset.mem_abcExceptionsBelow ..

theorem countTriples_def {ε : ℝ} {X : ℕ} : countTriples ε X = #(abcExceptionsBelow ε X) := rfl

theorem abcConjecture_def :
  abcConjecture ↔ ∀ ε > 0, (abcExceptions ε).Finite := Iff.rfl

open Filter Topology

theorem abcConjecture_equivalence_bigO :
    abcConjecture ↔
    ∀ᶠ ε in 𝓝[>] 0,
      (countTriples ε · : ℕ → ℝ) =O[atTop] (fun _ ↦ (1 : ℝ)) :=
  abcConjecture_iff_eventually_countTriples

theorem deBruijn (ε : ℝ) (hε : ε > 0) (hε_small : ε < 1 / 100) :
    (countTriples ε · : ℕ → ℝ) =O[atTop] (fun N ↦ (N : ℝ) ^ (2 / 3 : ℝ)) := by
  simpa [countTriples, ← exceptionalSet_eq] using theorem67'' ε hε hε_small

theorem new_bound (ε : ℝ) (hε : ε > 0) (hε_small : ε < 1 / 100000) :
    (countTriples ε · : ℕ → ℝ) =O[atTop] (fun N ↦ (N : ℝ) ^ (0.66 : ℝ)) := by
  sorry

end demo
