import Mathlib

noncomputable section

open Set

variable {d : ℕ} {a b c : ℕ → ℝ}

structure baseAssumptions (d : ℕ) (a : ℕ → ℝ) : Prop where
(nonneg : ∀ i ≤ d, 0 ≤ a i)
(zero : a 0 = 0)
(sum_bound : ∑ i ≤ d, i * a i ≤ 1)

-- todo: improve the api for proofs like this one
example : ∑ i ≤ d, i * a i = ∑ i in Finset.Icc 1 d, i * a i := by sorry

lemma baseAssumptions.sum_restrict_bound (h : baseAssumptions d a) :
    ∑ i in Finset.Icc 1 d, i * a i ≤ 1 := by
  simpa [Finset.Iic_eq_Icc, ← Nat.Icc_insert_succ_left] using h.sum_bound

def Bound4Point3 (d : ℕ) (ε : ℝ) (a b : ℕ → ℝ) : Prop :=
  0.66 - ε ^ 2 ≤ ∑ i ≤ d, (a i + b i)

def Bound4Point4 (d : ℕ) (δ ε : ℝ) (a b c : ℕ → ℝ) : Prop :=
  ∑ i ≤ d, (a i + b i + c i) ≤ 1 + δ - ε

-- we will later show that 4.5 can be safely assumed in context, after we've assumed 1.2 and 4.4
structure Bound4Point5 (d : ℕ) (δ ε : ℝ) (a : ℕ → ℝ) : Prop where
(lower : 0.32 - δ ≤ ∑ i ≤ d, a i)
(upper : ∑ i ≤ d, a i ≤ 0.34 + δ - ε / 2)

def FourierBound (d : ℕ) (δ ν : ℝ) (a b : ℕ → ℝ) : Prop :=
  ν < 1/2 * (1 + δ + ∑ i ≤ d, max (a i) (b i) - sSup {max (a i) (b i) | i ∈ Ioc 1 d})

def DeterminantBound (d : ℕ) (δ ν : ℝ) (a b : ℕ → ℝ) : Prop :=
  ν < sInf {1 + δ - a p - b q + min (a p / q) (b q / p) |
    (p : ℕ) (q : ℕ) (_ : p ∈ Ioc 1 d) (_ : q ∈ Ioc 1 d)}

def ThueBound (d : ℕ) (δ ν : ℝ) (a b : ℕ → ℝ) : Prop :=
  ν < 1 + δ - sSup {∑ i ≤ d with p ∣ i, (a i + b i) | p ∈ Ioc 1 d}

def GeometryBound (d : ℕ) (δ ν : ℝ) (a b c : ℕ → ℝ) : Prop :=
  ν < δ + sInf
    {max 1 (∑ i ∈ I, i * a i + ∑ i ∈ I', i * b i + ∑ i ∈ I'', i * c i) -
      (∑ i ∈ I, a i + ∑ i ∈ I', b i + ∑ i ∈ I'', c i) |
      (I : Finset ℕ) (I' : Finset ℕ) (I'' : Finset ℕ)
      (_ : I ⊆ Finset.Icc 1 d) (_ : I' ⊆ Finset.Icc 1 d) (_ : I'' ⊆ Finset.Icc 1 d)}

-- variable (hδ_upper : δ ≤ 0.001)

def δ_ (d : ℕ) (f : ℕ → ℝ) : ℝ := 1 / 3 - ∑ i ≤ d, f i
lemma sum_eq_δ_ (d : ℕ) (f : ℕ → ℝ) : ∑ i ≤ d, f i = 1 / 3 - δ_ d f := by simp [δ_]

-- def delta_ac : ℝ := delta_a + delta_c
-- def delta_bc : ℝ := delta_b + delta_c

-- def δ_abc : ℝ := δ_ a + δ_ b + δ_ c

variable {δ ε : ℝ}

lemma bound_4_point_8 (h43 : Bound4Point3 d ε a b) : δ_ d a + δ_ d b ≤ 2 / 300 + ε ^ 2 := by
  simp only [δ_, sub_add_sub_comm, ← Finset.sum_add_distrib, Bound4Point3] at h43 ⊢
  norm_num at h43 ⊢
  linarith

lemma bound_4_point_9_lower (hε : 0 < ε) (f : ℕ → ℝ) (h45 : Bound4Point5 d δ ε f) :
    - 2 / 300 - δ ≤ δ_ d f := by
  replace h45 := h45.upper
  norm_num [δ_] at h45 ⊢
  linarith

lemma bound_4_point_9_upper (hε : 0 < ε) (f : ℕ → ℝ) (h45 : Bound4Point5 d δ ε f) :
    δ_ d f ≤ 1 / 75 + δ + ε := by
  replace h45 := h45.lower
  norm_num [δ_] at h45 ⊢
  linarith

lemma bound_4_point_10_lower (hε : 0 < ε) (h44 : Bound4Point4 d δ ε a b c) :
    - δ < δ_ d a + δ_ d b + δ_ d c := by
  simp only [Bound4Point4, Finset.sum_add_distrib, δ_] at h44 ⊢
  linarith

lemma bound_4_point_10_upper (hε : 0 < ε) (hε₁ : ε ≤ 2 / 3)
    (h43ab : Bound4Point3 d ε a b)
    (h43ac : Bound4Point3 d ε a c)
    (h43bc : Bound4Point3 d ε b c) :
    δ_ d a + δ_ d b + δ_ d c ≤ 0.01 + ε := by
  have := bound_4_point_8 h43ab
  have := bound_4_point_8 h43ac
  have := bound_4_point_8 h43bc
  have : 2 * (δ_ d a + δ_ d b + δ_ d c) ≤ 0.02 + 3 * ε ^ 2 := by
    norm_num1 at *
    linarith
  have : 3 * ε ^ 2 ≤ 2 * ε := by nlinarith
  norm_num1 at *
  linarith

#exit

lemma eq_4_10_upper : δ_ a + δ_ b + δ_ c ≤ 0.01 + ε :=
  sorry

theorem thm43 : ν ≤ 0.66 :=
  sorry
