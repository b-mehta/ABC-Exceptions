import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Radical
import Mathlib.RingTheory.UniqueFactorizationDomain.Nat

lemma Nat.primeFactors_eq (n : ℕ) :
    UniqueFactorizationMonoid.primeFactors n = Nat.primeFactors n := by
  rw [UniqueFactorizationMonoid.primeFactors, Nat.factors_eq, Nat.primeFactors]
  simp only [List.toFinset_coe]
  convert rfl

namespace UniqueFactorizationMonoid

variable {M : Type*} [CancelCommMonoidWithZero M] [NormalizationMonoid M]
  [UniqueFactorizationMonoid M]

variable {R : Type*} [CommSemiring R] [IsDomain R] [NormalizationMonoid R]
  [UniqueFactorizationMonoid R]

@[simp] lemma mem_primeFactors {x y : M} : x ∈ primeFactors y ↔ x ∈ normalizedFactors y := by
  rw [primeFactors]
  simp only [Multiset.mem_toFinset]

/--
An irreducible `a` divides the radical of `b` if and only if it divides `b` itself.
Note this generalises to radical elements `a`, see `dvd_radical_iff`.
-/
lemma dvd_radical_iff_of_irreducible {a b : M} (ha : Irreducible a) (hb : b ≠ 0) :
    a ∣ radical b ↔ a ∣ b := by
  constructor
  · intro ha
    exact ha.trans (radical_dvd_self b)
  · intro ha'
    obtain ⟨c, hc, hc'⟩ := exists_mem_normalizedFactors_of_dvd hb ha ha'
    exact hc'.dvd.trans (Finset.dvd_prod_of_mem _ (by simpa))

lemma mem_normalizedFactors_iff' {a b : M} (ha : a ≠ 0) :
    b ∈ normalizedFactors a ↔ b ∣ a ∧ normalize b = b ∧ Irreducible b := by
  constructor
  · intro hb
    exact ⟨dvd_of_mem_normalizedFactors hb, normalize_normalized_factor b hb,
      irreducible_of_normalized_factor b hb⟩
  · rintro ⟨h₁, h₂, h₃⟩
    obtain ⟨q, hq, hq'⟩ := exists_mem_normalizedFactors_of_dvd ha h₃ h₁
    cases hq'.eq_of_normalized h₂ (normalize_normalized_factor q hq)
    exact hq

@[simp] lemma primeFactors_zero : primeFactors (0 : M) = ∅ := by simp [primeFactors]

@[simp] lemma primeFactors_one : primeFactors (1 : M) = ∅ := by simp [primeFactors]

lemma primeFactors_pairwise_isRelPrime {a : M} :
    (primeFactors a).toSet.Pairwise IsRelPrime := by
  obtain rfl | ha₀ := eq_or_ne a 0
  · simp
  intro x hx y hy hxy
  simp only [Finset.mem_coe, mem_primeFactors, mem_normalizedFactors_iff' ha₀] at hx hy
  rw [hx.2.2.isRelPrime_iff_not_dvd]
  contrapose! hxy
  have : Associated x y := hx.2.2.associated_of_dvd hy.2.2 hxy
  exact this.eq_of_normalized hx.2.1 hy.2.1

lemma isRadical_radical {a : M} : IsRadical (radical a) := by
  intro n p ha
  rw [radical]
  apply Finset.prod_dvd_of_isRelPrime
  · exact primeFactors_pairwise_isRelPrime
  intro i hi
  simp only [mem_primeFactors] at hi
  have : i ∣ radical a := by
    rw [dvd_radical_iff_of_irreducible]
    · exact dvd_of_mem_normalizedFactors hi
    · exact irreducible_of_normalized_factor i hi
    · rintro rfl
      simp only [normalizedFactors_zero, Multiset.not_mem_zero] at hi
  exact (prime_of_normalized_factor i hi).isRadical n p (this.trans ha)

lemma squarefree_radical {a : M} : Squarefree (radical a) := by
  nontriviality M
  exact isRadical_radical.squarefree (by simp [radical_ne_zero])

lemma normalizedFactors_nodup {a : M} (ha : IsRadical a) : (normalizedFactors a).Nodup := by
  obtain rfl | ha₀ := eq_or_ne a 0
  · simp
  rwa [← squarefree_iff_nodup_normalizedFactors ha₀, ← isRadical_iff_squarefree_of_ne_zero ha₀]

lemma primeFactors_val_eq_normalizedFactors {a : M} (ha : IsRadical a) :
    (primeFactors a).val = normalizedFactors a := by
  classical
  rw [primeFactors, Multiset.toFinset_val, Multiset.dedup_eq_self]
  exact normalizedFactors_nodup ha

lemma radical_associated {a : M} (ha : IsRadical a) (ha' : a ≠ 0) :
    Associated (radical a) a := by
  rw [radical, ← Finset.prod_val, primeFactors_val_eq_normalizedFactors ha]
  exact normalizedFactors_prod ha'

lemma dvd_radical_of_isRadical {a : M} (ha : IsRadical a) (ha' : a ≠ 0) : a ∣ radical a :=
  (radical_associated ha ha').dvd'

lemma radical_eq_of_primeFactors_eq {a b : M} (h : primeFactors a = primeFactors b) :
    radical a = radical b := by
  simp only [radical, h]

lemma primeFactors_radical (a : M) : primeFactors (radical a) = primeFactors a := by
  obtain rfl | ha₀ := eq_or_ne a 0
  · simp [primeFactors]
  have : Nontrivial M := ⟨a, 0, ha₀⟩
  ext p
  have : radical a ≠ 0 := radical_ne_zero _
  simp only [mem_primeFactors, mem_normalizedFactors_iff' ha₀, mem_normalizedFactors_iff' this,
    and_congr_left_iff, and_imp]
  intro hp hp'
  rw [dvd_radical_iff_of_irreducible hp' ha₀]

lemma radical_radical {a : M} : radical (radical a) = radical a :=
  radical_eq_of_primeFactors_eq (primeFactors_radical _)

lemma radical_dvd_radical_iff_normalizedFactors_subset_normalizedFactors {a b : M} :
    radical a ∣ radical b ↔ normalizedFactors a ⊆ normalizedFactors b := by
  obtain rfl | ha₀ := eq_or_ne a 0
  · simp
  have : Nontrivial M := ⟨a, 0, ha₀⟩
  rw [dvd_iff_normalizedFactors_le_normalizedFactors (radical_ne_zero _) (radical_ne_zero _),
    Multiset.le_iff_subset (normalizedFactors_nodup isRadical_radical)]
  simp only [Multiset.subset_iff, ← mem_primeFactors, primeFactors_radical]

lemma radical_dvd_radical_iff_primeFactors_subset_primeFactors {a b : M} :
    radical a ∣ radical b ↔ primeFactors a ⊆ primeFactors b := by
  classical
  rw [radical_dvd_radical_iff_normalizedFactors_subset_normalizedFactors, primeFactors,
    primeFactors, Multiset.toFinset_subset]

lemma radical_dvd_radical {a b : M} (h : a ∣ b) (hb₀ : b ≠ 0) : radical a ∣ radical b := by
  obtain rfl | ha₀ := eq_or_ne a 0
  · simp
  rw [dvd_iff_normalizedFactors_le_normalizedFactors ha₀ hb₀] at h
  rw [radical_dvd_radical_iff_normalizedFactors_subset_normalizedFactors]
  exact Multiset.subset_of_le h

lemma dvd_radical_iff' {a b : M} (ha : IsRadical a) (hb₀ : b ≠ 0) : a ∣ radical b ↔ a ∣ b := by
  refine ⟨fun ha' ↦ ha'.trans (radical_dvd_self _), fun hab ↦ ?_⟩
  obtain rfl | ha₀ := eq_or_ne a 0
  · simp_all
  · exact (dvd_radical_of_isRadical ha ha₀).trans (radical_dvd_radical hab hb₀)

/-- Coprime elements have disjoint prime factors (as multisets). -/
theorem disjoint_normalizedFactors {a b : M} (hc : IsRelPrime a b) :
    Disjoint (normalizedFactors a) (normalizedFactors b) := by
  rw [Multiset.disjoint_left]
  intro x hxa hxb
  have x_dvd_a := dvd_of_mem_normalizedFactors hxa
  have x_dvd_b := dvd_of_mem_normalizedFactors hxb
  have xp := prime_of_normalized_factor x hxa
  exact xp.not_unit (hc x_dvd_a x_dvd_b)

theorem disjoint_normalizedFactors' {a b : R} (hc : IsCoprime a b) :
    Disjoint (normalizedFactors a) (normalizedFactors b) :=
  disjoint_normalizedFactors hc.isRelPrime


/- The following three theorems exist in mathlib but in the generality of a CommRing instead of
  a CommSemiring. -/
theorem disjoint_primeFactors {a b : R} (hc : IsRelPrime a b) :
    Disjoint (primeFactors a) (primeFactors b) := by
  classical
  exact Multiset.disjoint_toFinset.mpr (disjoint_normalizedFactors hc)

theorem mul_primeFactors_disjUnion {a b : R} (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : IsRelPrime a b) :
    primeFactors (a * b) =
    (primeFactors a).disjUnion (primeFactors b) (disjoint_primeFactors hc) := by
  classical
  rw [Finset.disjUnion_eq_union]
  simp_rw [primeFactors]
  rw [normalizedFactors_mul ha hb, Multiset.toFinset_add]

theorem radical_mul {a b : R} (hc : IsRelPrime a b) :
    radical (a * b) = radical a * radical b := by
  by_cases ha : a = 0
  · subst ha; rw [isRelPrime_zero_left] at hc
    simp only [zero_mul, radical_zero_eq, one_mul, radical_of_isUnit hc]
  by_cases hb : b = 0
  · subst hb; rw [isRelPrime_zero_right] at hc
    simp only [mul_zero, radical_zero_eq, mul_one, radical_of_isUnit hc]
  simp_rw [radical]
  rw [mul_primeFactors_disjUnion ha hb hc]
  rw [Finset.prod_disjUnion (disjoint_primeFactors hc)]

theorem primeFactors_mul_eq_union [DecidableEq R] {a b  : R} (ha : a ≠ 0) (hb : b ≠ 0)  :
    primeFactors (a * b) = primeFactors a ∪ primeFactors b := by
  ext p
  simp [mem_normalizedFactors_iff', ha, hb]

theorem radical_dvd_iff_primeFactors_subset (a b : R) (hb : b ≠ 0):
    radical a ∣ b ↔ primeFactors a ⊆ primeFactors b := by
  by_cases ha : a = 0
  · simp [ha]
  constructor
  · intro h
    intro p
    simp only [mem_primeFactors, mem_normalizedFactors_iff']
    rw [mem_normalizedFactors_iff', mem_normalizedFactors_iff']
    · simp only [and_imp]
      intro hpa hpn hp
      have : p ∣ radical a := (dvd_radical_iff_of_irreducible hp ha).mpr hpa
      refine ⟨this.trans h, hpn, hp⟩
    · exact hb
    · exact ha
  · intro hab
    refine (dvd_radical_iff' ?_ hb).mp ?_
    · exact isRadical_radical
    simp_rw [radical]
    apply Finset.prod_dvd_prod_of_subset
    exact hab

theorem radical_mul_dvd {a b : R} :
    radical (a * b) ∣ radical a * radical b := by
  classical
  by_cases ha : a = 0
  · subst ha; simp
  by_cases hb : b = 0
  · subst hb; simp
  simp [radical_dvd_iff_primeFactors_subset, primeFactors_mul_eq_union, ha, hb, radical_ne_zero,
    primeFactors_radical]

end UniqueFactorizationMonoid
