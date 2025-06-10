import ABCExceptions.TrivialBound
import ABCExceptions.Section2

section compat

lemma finite_exceptionalSet {N ε} : (exceptionalSet N ε).Finite :=
  (Set.finite_Icc (1, 1, 1) (N, N, N)).subset (by simp +contextual [Set.subset_def, exceptionalSet])

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

lemma rad_eq (n : ℕ) (hn : n ≠ 0) : rad n = UniqueFactorizationMonoid.radical n := by
  rw [rad, if_neg hn, UniqueFactorizationMonoid.radical,
    UniqueFactorizationMonoid.primeFactors_eq_natPrimeFactors]

lemma exceptionalSet_eq (N : ℕ) (ε : ℝ) :
    Set.ABCExceptionsBelow (1 - ε) N = exceptionalSet N ε := by
  ext ⟨a, b, c⟩
  simp only [Set.ABCExceptionsBelow, Prod.mk.eta, Set.mem_Icc, Set.mem_setOf_eq, Prod.mk_le_mk,
    exceptionalSet]
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

end compat

open UniqueFactorizationMonoid

namespace demo

theorem mem_ABCExceptions (ε : ℝ) (a b c : ℕ) :
    (a, b, c) ∈ ABCExceptions ε ↔
      0 < a ∧ 0 < b ∧ 0 < c ∧
      a.Coprime b ∧ a.Coprime c ∧ b.Coprime c ∧
      a + b = c ∧
      radical (a * b * c) ^ (1 + ε) < (c : ℝ) :=
  Set.mem_ABCExceptions ..

theorem mem_ABCExceptionsBelow (X : ℕ) (μ : ℝ) (a b c : ℕ) :
    (a, b, c) ∈ Set.ABCExceptionsBelow μ X ↔
      a.Coprime b ∧ a.Coprime c ∧ b.Coprime c ∧
      a + b = c ∧
      radical (a * b * c) < (c : ℝ) ^ μ ∧
      (a, b, c) ∈ Set.Icc (1, 1, 1) (X, X, X) :=
  Set.mem_ABCExceptionsBelow ..

theorem ABCConjecture_equivalence : ABCConjecture ↔ ∀ ε > 0, (ABCExceptions ε).Finite := Iff.rfl

open Filter

theorem ABCConjecture_equivalence_bigO :
    ABCConjecture ↔ ∀ μ > 0, μ < 1 → (countTriples μ · : ℕ → ℝ) =O[atTop] (fun _ ↦ (1 : ℝ)) :=
  abcConjecture_iff

theorem deBruijn (ε : ℝ) (hε : ε > 0) (hε_small : ε < 1/100) :
    (countTriples (1 - ε) · : ℕ → ℝ) =O[Filter.atTop]
    (fun N ↦ (N : ℝ) ^ (2 / 3 : ℝ)) := by
  simpa only [countTriples, exceptionalSet_eq] using theorem67'' ε hε hε_small

end demo
