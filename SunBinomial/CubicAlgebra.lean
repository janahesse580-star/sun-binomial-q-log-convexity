import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The cubic cancellation identity used in the written proof.

These lemmas verify the elimination of the constant and quadratic terms.
-/

namespace SunBinomial.Cubic

noncomputable section

private structure Elimination where
  H : ℝ
  C : ℝ
  F : ℝ
  J2 : ℝ
  R4 : ℝ
  R6 : ℝ
  R8 : ℝ

private def elimination (n z : ℝ) : Elimination :=
  let a := n + z
  let b := a * z
  let center := a * (a + 1)
  let slope := 2 * a + 1
  let A2 := n^3 * (3 * center^2 + 3 * center * slope^2) + 3 * (n+1)^3 * a^4
  let A4 := n^3 * (3 * center + 3 * slope^2) - 3 * (n+1)^3 * a^2
  let A6 := n^3 + (n+1)^3
  let even0 := 2 * b^3
  let even2 := -6 * b^2 + 6 * b * n^2
  let even4 := 6 * b - 6 * n^2
  let even6 := -2
  let odd1 := -6 * b^2 * n
  let odd3 := 12 * b * n - 2 * n^3
  let odd5 := -6 * n
  let D2 := even2 + 2 * odd1
  let D4 := even4 + 2 * odd3
  let D6 := even6 + 2 * odd5
  let E2 := 12 * even0 + 4 * odd1
  let E4 := 12 * even2 + 8 * odd1 + 4 * odd3
  let E6 := 12 * even4 + 8 * odd3 + 4 * odd5
  let E8 := 12 * even6 + 8 * odd5
  let H := 2 * z^2
  let u := (n + 1) * a
  let C := 3 * u^2 - 3 * u * z + z^2
  let J2 := H * A2 + C * D2
  let R4 := E2 * (H * A4 + C * D4) - J2 * E4
  let R6 := E2 * (H * A6 + C * D6) - J2 * E6
  let R8 := -J2 * E8
  ⟨H, C, E2, J2, R4, R6, R8⟩

private def pairedDifference (n z t : ℝ) : ℝ :=
  let a := n + z
  n^3 / 2 * (((a+t)*(a+1+t))^3 + ((a-t)*(a+1-t))^3)
    - (n+1)^3 * (a^2-t^2)^3

private def forward (n z t : ℝ) : ℝ := ((n+z)*z-t^2-n*t)^3
private def backward (n z t : ℝ) : ℝ := ((n+z)*z-t^2+n*t)^3

private def telescoper (n z t : ℝ) : ℝ :=
  forward n z t * (2*t+1) - backward n z t * (2*t-1)

private def telescoperThree (n z t : ℝ) : ℝ :=
  forward n z t * ((2*t+1)^3-(2*t+1)) - backward n z t * ((2*t-1)^3-(2*t-1))

/-- The cancellation identity used in both coefficient ranges. -/
theorem residual_identity (n z t : ℝ) :
    let p := elimination n z
    p.F * (p.H * pairedDifference n z t + p.C * telescoper n z t) -
      p.J2 * telescoperThree n z t = t^4 * (p.R4 + p.R6*t^2 + p.R8*t^4) := by
  dsimp [elimination, pairedDifference, telescoper, telescoperThree, forward, backward]
  ring

theorem scaling_factor_positive {n z : ℝ} (hn : 0 ≤ n) (hz : 1 ≤ z) :
    0 < (elimination n z).F := by
  have hz0 : 0 < z := by linarith
  have hanz : 0 < n + z := add_pos_of_nonneg_of_pos hn hz0
  have hdiff : 0 < (n + z) * z - n := by
    nlinarith only [mul_nonneg hn (sub_nonneg.mpr hz), pow_pos hz0 2]
  calc
    0 < 24 * ((n + z) * z)^2 * ((n + z) * z - n) := by positivity
    _ = (elimination n z).F := by dsimp [elimination]; ring

/-- The three negative terms in the boundary certificate are absorbed by six
positive terms of that certificate. -/
theorem boundary_negative_terms_absorbed (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ (294912*x*y^18 + (36864/5)*x^5*y^16 - 24576*x^3*y^17)
      + (3317760*x^2*y^17 + 82944*x^6*y^15 - 190464*x^4*y^16)
      + (17160192*x^3*y^16 + (3050112/7)*x^7*y^14 - (1491456/5)*x^5*y^15) := by
  calc
    0 ≤ (x*y^16*(256*y-48*x^2)^2 + 229376*x*y^18 + (25344/5)*x^5*y^16)
        + (x^2*y^15*(768*y-124*x^2)^2 + 2727936*x^2*y^17 + 67568*x^6*y^15)
        + (x^3*y^14*(256*y-(2913/5)*x^2)^2 + 17094656*x^3*y^16
          + (16853817/175)*x^7*y^14) := by positivity
    _ = _ := by ring

#print axioms residual_identity
#print axioms scaling_factor_positive
#print axioms boundary_negative_terms_absorbed

end

end SunBinomial.Cubic
