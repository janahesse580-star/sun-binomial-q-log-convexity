import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import SunBinomial.CubicAlgebra

/-! The binomial-power conjecture fails for every exponent at least four.

Zhi-Wei Sun posed the conjecture in [Conjecture 1.1(i)](https://arxiv.org/abs/2505.02767).
Qiping Zhou gave the exponent-five counterexample on
[MathOverflow](https://mathoverflow.net/questions/479301/).
Shivam Patel gave the exponent-four counterexample at index 23 and proved eventual failure
for each fixed exponent at least four in a
[public proof note](https://mathdb.com/p/368293/sun-s-q-log-convexity-conjecture-for-binomial-sums-and-the-p).
The verification below proves the uniform threshold 23 for all exponents at least four.
-/

open Finset Polynomial Set
open scoped BigOperators

namespace SunBinomial

noncomputable section

/-- The polynomial in Sun's binomial-power question. -/
noncomputable def rising (m n : ℕ) : Polynomial ℝ :=
  ∑ k ∈ Finset.range (n + 1), monomial k ((Nat.choose (n + k) k : ℝ) ^ m)

/-- The coefficientwise difference used to define q-log-convexity. -/
noncomputable def delta (m n : ℕ) : Polynomial ℝ :=
  rising m (n - 1) * rising m (n + 1) - (rising m n) ^ 2

/-- Coefficientwise q-log-convexity for the family at exponent m. -/
def QLogConvex (m : ℕ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 0 ≤ (delta m n).coeff k

theorem coeff_rising (m n k : ℕ) :
    (rising m n).coeff k = if k ≤ n then (Nat.choose (n + k) k : ℝ) ^ m else 0 := by
  simp [rising, finset_sum_coeff, coeff_monomial, Finset.sum_ite_eq',
    Nat.lt_succ_iff]

private lemma choose_two_real (n : ℕ) :
    (Nat.choose (n + 2) 2 : ℝ) = ((n : ℝ) + 2) * ((n : ℝ) + 1) / 2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [show n.succ + 2 = n + 2 + 1 by omega, Nat.choose_succ_succ' (n + 2) 1,
      Nat.choose_one_right, Nat.cast_add, ih]
    push_cast
    ring

private lemma coeff_rising_zero (m n : ℕ) : (rising m n).coeff 0 = 1 := by
  simp [coeff_rising]

private lemma coeff_rising_one (m n : ℕ) (hn : 1 ≤ n) :
    (rising m n).coeff 1 = ((n : ℝ) + 1) ^ m := by
  simp [coeff_rising, hn]

private lemma coeff_rising_two (m n : ℕ) (hn : 2 ≤ n) :
    (rising m n).coeff 2 = (((n : ℝ) + 2) * ((n : ℝ) + 1) / 2) ^ m := by
  simp [coeff_rising, hn, choose_two_real]

private lemma coeff_mul_two_real (p q : Polynomial ℝ) :
    (p * q).coeff 2 = p.coeff 0 * q.coeff 2 + p.coeff 1 * q.coeff 1 +
      p.coeff 2 * q.coeff 0 := by
  rw [Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => p.coeff i * q.coeff j) 2]
  norm_num [Finset.sum_range_succ]

private def a (t : ℝ) : ℝ := t * (t - 1) / 2
private def b (t : ℝ) : ℝ := t * (t + 1) / 2
private def c (t : ℝ) : ℝ := (t + 1) * (t + 2) / 2
private def d (t : ℝ) : ℝ := t ^ 2 - 1
private def e (t : ℝ) : ℝ := t ^ 2

private noncomputable def loss (m : ℕ) (t : ℝ) : ℝ :=
  a t ^ m + c t ^ m - 2 * b t ^ m + d t ^ m - e t ^ m

private theorem coeff_two_delta (m n : ℕ) (hn : 3 ≤ n) :
    (delta m n).coeff 2 = loss m ((n : ℝ) + 1) := by
  simp only [delta, pow_two (rising m n), coeff_sub, coeff_mul_two_real,
    coeff_rising_zero, one_mul, mul_one]
  rw [coeff_rising_one m (n - 1) (by omega), coeff_rising_one m (n + 1) (by omega),
    coeff_rising_one m n (by omega),
    coeff_rising_two m (n - 1) (by omega), coeff_rising_two m (n + 1) (by omega),
    coeff_rising_two m n (by omega), Nat.cast_sub (show 1 ≤ n by omega)]
  push_cast
  unfold loss a b c d e
  rw [← mul_pow, ← mul_pow]
  have hA : ((n : ℝ) - 1 + 2) * ((n : ℝ) - 1 + 1) / 2 =
      ((n : ℝ) + 1) * ((n : ℝ) + 1 - 1) / 2 := by ring
  have hC : ((n : ℝ) + 1 + 2) * ((n : ℝ) + 1 + 1) / 2 =
      ((n : ℝ) + 1 + 1) * ((n : ℝ) + 1 + 2) / 2 := by ring
  have hD : ((n : ℝ) - 1 + 1) * ((n : ℝ) + 1 + 1) = ((n : ℝ) + 1) ^ 2 - 1 := by ring
  have hE : ((n : ℝ) + 1) * ((n : ℝ) + 1) = ((n : ℝ) + 1) ^ 2 := by ring
  rw [hA, hC, hD, hE]
  have hB : ((n : ℝ) + 2) * ((n : ℝ) + 1) / 2 =
      ((n : ℝ) + 1) * ((n : ℝ) + 1 + 1) / 2 := by ring
  rw [hB]
  ring

private theorem loss_four_expansion (x : ℝ) :
    16 * loss 4 (x + 24) =
      -(8*x^6 + 984*x^5 + 48544*x^4 + 1203864*x^3 +
        15125000*x^2 + 79879968*x + 47999200) := by
  unfold loss a b c d e
  ring

private lemma loss_four_neg (t : ℝ) (ht : 24 ≤ t) : loss 4 t < 0 := by
  let x : ℝ := t - 24
  have hx : 0 ≤ x := sub_nonneg.mpr ht
  have hxt : x + 24 = t := sub_add_cancel t 24
  have hp : 0 ≤ 8*x^6 + 984*x^5 + 48544*x^4 + 1203864*x^3 +
        15125000*x^2 + 79879968*x := by positivity
  have h := loss_four_expansion x
  rw [hxt] at h
  linarith

private noncomputable def g (k : ℕ) (E u : ℝ) : ℝ := (E - u) * u ^ (k + 4)
private noncomputable def g' (k : ℕ) (E u : ℝ) : ℝ :=
  u ^ (k + 3) * (((k : ℝ) + 4) * E - ((k : ℝ) + 5) * u)

private lemma hasDerivAt_g (k : ℕ) (E u : ℝ) : HasDerivAt (g k E) (g' k E u) u := by
  unfold g g'
  convert ((hasDerivAt_const u E).sub (hasDerivAt_id u)).mul
    ((hasDerivAt_id u).pow (k + 4)) using 1
  simp only [id_eq, zero_sub, one_mul, Nat.cast_add, Nat.cast_ofNat,
    show k + 4 - 1 = k + 3 by omega]
  rw [show k + 4 = (k + 3) + 1 by omega, pow_succ]
  ring

private lemma hasDerivAt_g' (k : ℕ) (E u : ℝ) :
    HasDerivAt (g' k E)
      (((k : ℝ) + 4) * u ^ (k + 2) * (((k : ℝ) + 3) * E - ((k : ℝ) + 5) * u)) u := by
  unfold g'
  convert ((hasDerivAt_id u).pow (k + 3)).mul
    ((hasDerivAt_const u (((k : ℝ) + 4) * E)).sub
      ((hasDerivAt_const u ((k : ℝ) + 5)).mul (hasDerivAt_id u))) using 1
  simp only [id_eq, zero_mul, zero_add, zero_sub, one_mul, mul_one, Nat.cast_add, Nat.cast_ofNat,
    show k + 3 - 1 = k + 2 by omega]
  rw [show k + 3 = (k + 2) + 1 by omega, pow_succ]
  ring

private lemma bracket_nonneg (k : ℕ) {E u : ℝ} (hE : 0 ≤ E) (hu : u ≤ 3 * E / 5) :
    0 ≤ ((k : ℝ) + 3) * E - ((k : ℝ) + 5) * u := by
  have hk : 0 ≤ (k : ℝ) := by positivity
  have hdiff : 0 ≤ E - u := by linarith
  nlinarith only [mul_nonneg hk hdiff, hu]

private lemma g_midpoint (k : ℕ) {A B C E : ℝ}
    (hA : 0 ≤ A) (hAB : A ≤ B) (hBC : B ≤ C) (hCE : C ≤ 3 * E / 5)
    (hB : B ≤ (A + C) / 2) :
    2 * g k E B ≤ g k E A + g k E C := by
  let I := Set.Icc A C
  have hE : 0 ≤ E := by linarith
  have hI : Convex ℝ I := convex_Icc A C
  have hd : Differentiable ℝ (g k E) := fun u => (hasDerivAt_g k E u).differentiableAt
  have hderiv : deriv (g k E) = g' k E := funext fun u => (hasDerivAt_g k E u).deriv
  have hdd : Differentiable ℝ (deriv (g k E)) := by
    rw [hderiv]
    exact fun u => (hasDerivAt_g' k E u).differentiableAt
  have hc : ConvexOn ℝ I (g k E) := by
    apply convexOn_of_deriv2_nonneg' hI hd.differentiableOn hdd.differentiableOn
    intro u hu
    change A ≤ u ∧ u ≤ C at hu
    have h0 : 0 ≤ u := hA.trans hu.1
    have h1 := bracket_nonneg k hE (hu.2.trans hCE)
    change 0 ≤ deriv (deriv (g k E)) u
    rw [hderiv, (hasDerivAt_g' k E u).deriv]
    exact mul_nonneg (mul_nonneg (by positivity) (pow_nonneg h0 _)) h1
  have hm : MonotoneOn (g k E) I := by
    apply monotoneOn_of_deriv_nonneg hI hd.continuous.continuousOn hd.differentiableOn
    intro u hu
    have hu' : u ∈ I := interior_subset hu
    change A ≤ u ∧ u ≤ C at hu'
    have h0 : 0 ≤ u := hA.trans hu'.1
    have h1 := bracket_nonneg k hE (hu'.2.trans hCE)
    rw [hderiv]
    unfold g'
    exact mul_nonneg (pow_nonneg h0 _) (by linarith)
  have ha : A ∈ I := ⟨le_rfl, hAB.trans hBC⟩
  have hb : B ∈ I := ⟨hAB, hBC⟩
  have hc' : C ∈ I := ⟨hAB.trans hBC, le_rfl⟩
  have hz : (A + C) / 2 ∈ I := ⟨by linarith, by linarith⟩
  have hmono := hm hb hz hB
  have hconv := hc.2 ha hc' (show 0 ≤ (1/2 : ℝ) by norm_num)
    (show 0 ≤ (1/2 : ℝ) by norm_num) (show (1/2 : ℝ) + 1/2 = 1 by norm_num)
  simp only [smul_eq_mul] at hconv
  rw [show (1/2 : ℝ) * A + (1/2 : ℝ) * C = (A + C) / 2 by ring] at hconv
  linarith

private lemma loss_step (k : ℕ) {t : ℝ} (ht : 24 ≤ t)
    (ih : loss (k + 4) t < 0) : loss (k + 1 + 4) t < 0 := by
  have ht0 : 0 ≤ t := by linarith
  have ha : 0 ≤ a t := by
    unfold a
    exact div_nonneg (mul_nonneg ht0 (by linarith)) (by norm_num)
  have hab : a t ≤ b t := by unfold a b; linarith
  have hbc : b t ≤ c t := by unfold b c; nlinarith
  have hce : c t ≤ 3 * e t / 5 := by
    unfold c e
    nlinarith only [ht, sq_nonneg (t - 24)]
  have hb : b t ≤ (a t + c t) / 2 := by unfold a b c; nlinarith
  have hg := g_midpoint k ha hab hbc hce hb
  have he : 0 < e t := by unfold e; positivity
  have hd : 0 < d t := by unfold d; nlinarith only [ht, sq_nonneg (t - 24)]
  have hed : e t - d t = 1 := by unfold d e; ring
  have hdiff : loss (k + 1 + 4) t - e t * loss (k + 4) t =
      2 * g k (e t) (b t) - g k (e t) (a t) - g k (e t) (c t) -
        (e t - d t) * d t ^ (k + 4) := by
    unfold loss g
    rw [show k + 1 + 4 = (k + 4) + 1 by omega]
    simp only [pow_succ]
    ring
  have hneg := mul_neg_of_pos_of_neg he ih
  rw [hed, one_mul] at hdiff
  have hp : 0 < d t ^ (k + 4) := pow_pos hd _
  linarith

private theorem loss_neg (k : ℕ) (t : ℝ) (ht : 24 ≤ t) : loss (k + 4) t < 0 := by
  induction k with
  | zero => simpa using loss_four_neg t ht
  | succ k ih => exact loss_step k ht ih

/-- A single threshold works for all exponents at least four. -/
theorem coeff_two_negative (m n : ℕ) (hm : 4 ≤ m) (hn : 23 ≤ n) :
    (delta m n).coeff 2 < 0 := by
  rw [coeff_two_delta m n (by omega)]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [Nat.add_comm 4 k]
  apply loss_neg
  have h : (23 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  linarith

/-- Shivam Patel's explicit fourth-power counterexample at index 23. -/
theorem fourth_counterexample : (delta 4 23).coeff 2 = -2999950 := by
  rw [coeff_two_delta 4 23 (by decide)]
  norm_num [loss, a, b, c, d, e]

/-- In particular, the original all-powers assertion is false. -/
theorem not_qLogConvex (m : ℕ) (hm : 4 ≤ m) : ¬ QLogConvex m := by
  intro h
  exact (not_lt_of_ge (h 23 (by decide) 2)) (coeff_two_negative m 23 hm (by decide))

/-- The degree-two coefficient is positive for the two surviving exponents. -/
theorem coeff_two_positive_square_or_cube (m n : ℕ) (hm : m = 2 ∨ m = 3)
    (hn : 1 ≤ n) : 0 < (delta m n).coeff 2 := by
  by_cases h : 3 ≤ n
  · rw [coeff_two_delta m n h]
    rcases hm with rfl | rfl
    · have heq : loss 2 ((n : ℝ) + 1) = ((n : ℝ) + 2) * ((n : ℝ) + 3) := by
        unfold loss a b c d e
        ring
      rw [heq]
      positivity
    · have heq : loss 3 ((n : ℝ) + 1) =
          3 * ((n : ℝ) + 1) * ((n : ℝ) + 2) *
            ((n : ℝ)^2 + 11 * (n : ℝ) + 16) / 4 := by
        unfold loss a b c d e
        ring
      rw [heq]
      positivity
  · have hs : n = 1 ∨ n = 2 := by omega
    rcases hm with rfl | rfl <;> rcases hs with rfl | rfl <;>
      simp only [delta, pow_two (rising _ _), coeff_sub, coeff_mul_two_real, coeff_rising] <;>
      norm_num [Nat.choose]

#print axioms coeff_two_negative
#print axioms fourth_counterexample
#print axioms not_qLogConvex
#print axioms coeff_two_positive_square_or_cube

end

end SunBinomial
