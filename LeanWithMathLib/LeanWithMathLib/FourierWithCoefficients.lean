import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Algebra.Group.EvenFunction

/-!
# Fourier coefficients over the reals

This file formalizes the parity arguments from `LaTeX/main.tex` using Mathlib's
real interval integral.  The coefficients below are the actual Fourier
coefficients from the written proof:

* `aCoeff f n = (1 / π) ∫ x in -π..π, f x * cos (n * x)`
* `bCoeff f n = (1 / π) ∫ x in -π..π, f x * sin (n * x)`

The main verified claims are:

* the integral of an odd real function over symmetric bounds is zero;
* all cosine coefficients of an odd function vanish;
* all sine coefficients of an even function vanish.

The last section records the closed forms computed in the paper for `x` and
`x^2` as real-valued coefficient formulae.
-/

open Real
open scoped Real

namespace FourierWithCoefficients

noncomputable section

/-!
## Definitions from the first page of the write-up

The LaTeX proof starts by defining the Fourier coefficients on `[-π, π]`.
The next three definitions are direct Lean translations of those displayed
formulae.  The only small Lean-specific detail is that `n : ℕ` must be coerced
to a real number before it can be multiplied by `x : ℝ`.
-/

/-- The cosine Fourier coefficient on `[-π, π]`. -/
def aCoeff (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  (1 / π) * ∫ x in -π..π, f x * cos ((n : ℝ) * x)

/-- The sine Fourier coefficient on `[-π, π]`. -/
def bCoeff (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  (1 / π) * ∫ x in -π..π, f x * sin ((n : ℝ) * x)

/-- The Fourier polynomial from the coefficients above. -/
def fourierPolynomial (f : ℝ → ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  aCoeff f 0 / 2 +
    (Finset.Icc 1 N).sum
      (fun n => aCoeff f n * cos ((n : ℝ) * x) + bCoeff f n * sin ((n : ℝ) * x))

/-!
## Parity facts used throughout the proof

Part (a) uses that `x` is odd and that `x * cos (n*x)` is odd.  Part (d) uses
that `x^2` is even and that `x^2 * sin (n*x)` is odd.  These small theorems
isolate exactly those parity facts before the integral argument begins.
-/

theorem id_odd : Function.Odd (fun x : ℝ => x) := by
  intro x
  rfl

theorem square_even : Function.Even (fun x : ℝ => x ^ 2) := by
  intro x
  ring

theorem cosTerm_even (n : ℕ) :
    Function.Even (fun x : ℝ => cos ((n : ℝ) * x)) := by
  intro x
  simp [mul_neg]

theorem sinTerm_odd (n : ℕ) :
    Function.Odd (fun x : ℝ => sin ((n : ℝ) * x)) := by
  intro x
  simp [mul_neg]

theorem odd_mul_even_is_odd {f g : ℝ → ℝ}
    (hf : Function.Odd f) (hg : Function.Even g) :
    Function.Odd (fun x => f x * g x) := by
  simpa only [Pi.mul_apply] using hf.mul_even hg

theorem even_mul_odd_is_odd {f g : ℝ → ℝ}
    (hf : Function.Even f) (hg : Function.Odd g) :
    Function.Odd (fun x => f x * g x) := by
  simpa only [Pi.mul_apply] using hf.mul_odd hg

/-!
## Part (b): odd functions integrate to zero on symmetric intervals

The non-Mathlib file had to assume this as a field of `SymmetricIntegral`.
Here Mathlib lets us prove the analytic statement over the real numbers.  The
proof follows the written proof's substitution `u = -x`: Mathlib's
`intervalIntegral.integral_comp_neg` is the formal change-of-variables step.
-/

/--
An odd real function integrates to zero over symmetric bounds.

This is the analytic fact used in part (b) of the written proof.  It is proved
from Mathlib's change-of-variables lemma for `x ↦ -x` and linearity of the
interval integral.
-/
theorem integral_odd_symmetric (f : ℝ → ℝ) (c : ℝ) (hf : Function.Odd f) :
    ∫ x in -c..c, f x = 0 := by
  let I : ℝ := ∫ x in -c..c, f x
  have hcomp : (∫ x in -c..c, f (-x)) = I := by
    simp [I, intervalIntegral.integral_comp_neg (f := f) (a := -c) (b := c)]
  have hneg : (∫ x in -c..c, f (-x)) = -I := by
    calc
      (∫ x in -c..c, f (-x)) = ∫ x in -c..c, -f x := by
        apply intervalIntegral.integral_congr
        intro x _
        exact hf x
      _ = -I := by
        simp [I]
  have hI : I = -I := hcomp.symm.trans hneg
  have : (2 : ℝ) * I = 0 := by linarith
  have htwo : (2 : ℝ) ≠ 0 := by norm_num
  exact (mul_eq_zero.mp this).resolve_left htwo

/-!
## Parts (c) and (d): the general coefficient conjectures

These are the real-interval-integral versions of the two general theorems from
the no-Mathlib file:

* odd `f` implies every cosine coefficient `a_n` is zero;
* even `f` implies every sine coefficient `b_n` is zero.

The written proof's key move is now visible in the argument: `f` times the
trigonometric factor is proved odd, so `integral_odd_symmetric` applies.
-/

theorem cosine_coeff_zero_of_odd {f : ℝ → ℝ}
    (hf : Function.Odd f) (n : ℕ) :
    aCoeff f n = 0 := by
  unfold aCoeff
  rw [integral_odd_symmetric
    (fun x : ℝ => f x * cos ((n : ℝ) * x)) π
    (odd_mul_even_is_odd hf (cosTerm_even n))]
  ring

theorem sine_coeff_zero_of_even {f : ℝ → ℝ}
    (hf : Function.Even f) (n : ℕ) :
    bCoeff f n = 0 := by
  unfold bCoeff
  rw [integral_odd_symmetric
    (fun x : ℝ => f x * sin ((n : ℝ) * x)) π
    (even_mul_odd_is_odd hf (sinTerm_odd n))]
  ring

/--
Part (a)'s first conclusion: for `f(x) = x`, every cosine coefficient vanishes.
This is just the general odd-function theorem specialized to the identity
function.
-/
theorem x_aCoeff_eq_zero (n : ℕ) :
    aCoeff (fun x : ℝ => x) n = 0 :=
  cosine_coeff_zero_of_odd id_odd n

/--
Part (d)'s vanishing conclusion for the check function `f(x) = x^2`: every
sine coefficient vanishes because `x^2` is even.
-/
theorem x2_bCoeff_eq_zero (n : ℕ) :
    bCoeff (fun x : ℝ => x ^ 2) n = 0 :=
  sine_coeff_zero_of_even square_even n

/-!
## Explicit coefficient patterns from parts (a) and (d)

The next definitions record the closed forms identified in the write-up after
the integration-by-parts computations:

* for `f(x) = x`, `b_n = 2*(-1)^(n+1)/n` for `n ≥ 1`;
* for `f(x) = x^2`, `a_0 = 2π^2/3` and
  `a_n = 4*(-1)^n/n^2` for `n ≥ 1`.

The file currently checks these formulae and the listed examples algebraically.
It does not yet prove the integration-by-parts evaluations equaling the
integral definitions of `bCoeff (fun x => x) n` and
`aCoeff (fun x => x^2) n`.
-/

/-- The closed form for the nonzero sine coefficients of `f(x) = x`. -/
def xBFormula (n : ℕ) : ℝ :=
  if n = 0 then 0 else 2 * (-1 : ℝ) ^ (n + 1) / n

/-- The closed form for the cosine coefficients of `f(x) = x^2`. -/
def x2AFormula (n : ℕ) : ℝ :=
  if n = 0 then 2 * π ^ 2 / 3 else 4 * (-1 : ℝ) ^ n / n ^ 2

theorem xBFormula_of_pos {n : ℕ} (hn : n ≠ 0) :
    xBFormula n = 2 * (-1 : ℝ) ^ (n + 1) / n := by
  simp [xBFormula, hn]

theorem x2AFormula_zero :
    x2AFormula 0 = 2 * π ^ 2 / 3 := by
  simp [x2AFormula]

theorem x2AFormula_of_pos {n : ℕ} (hn : n ≠ 0) :
    x2AFormula n = 4 * (-1 : ℝ) ^ n / n ^ 2 := by
  simp [x2AFormula, hn]

theorem x_b1 : xBFormula 1 = 2 := by norm_num [xBFormula]
theorem x_b2 : xBFormula 2 = -1 := by norm_num [xBFormula]
theorem x_b3 : xBFormula 3 = (2 : ℝ) / 3 := by norm_num [xBFormula]
theorem x_b4 : xBFormula 4 = (-1 : ℝ) / 2 := by norm_num [xBFormula]
theorem x_b5 : xBFormula 5 = (2 : ℝ) / 5 := by norm_num [xBFormula]
theorem x_b6 : xBFormula 6 = (-1 : ℝ) / 3 := by norm_num [xBFormula]

theorem x2_a0 : x2AFormula 0 = 2 * π ^ 2 / 3 := by
  simp [x2AFormula]

theorem x2_a1 : x2AFormula 1 = -4 := by norm_num [x2AFormula]
theorem x2_a2 : x2AFormula 2 = 1 := by norm_num [x2AFormula]
theorem x2_a3 : x2AFormula 3 = (-4 : ℝ) / 9 := by norm_num [x2AFormula]
theorem x2_a4 : x2AFormula 4 = (1 : ℝ) / 4 := by norm_num [x2AFormula]
theorem x2_a5 : x2AFormula 5 = (-4 : ℝ) / 25 := by norm_num [x2AFormula]

/-!
## First five polynomials in part (a)

The LaTeX proof lists `P_1` through `P_5` after observing that every `a_n`
vanishes for `f(x) = x`.  This theorem checks that the displayed list is exactly
what comes from substituting the first five values of `xBFormula`.
-/

/-- The first five Fourier polynomials for `f(x) = x`, as written in the LaTeX proof. -/
theorem x_first_five_polynomials :
    (fun x : ℝ =>
      (2 * sin x,
       2 * sin x - sin (2 * x),
       2 * sin x - sin (2 * x) + (2 / 3) * sin (3 * x),
       2 * sin x - sin (2 * x) + (2 / 3) * sin (3 * x) - (1 / 2) * sin (4 * x),
       2 * sin x - sin (2 * x) + (2 / 3) * sin (3 * x) - (1 / 2) * sin (4 * x)
         + (2 / 5) * sin (5 * x)))
    =
    (fun x : ℝ =>
      (xBFormula 1 * sin x,
       xBFormula 1 * sin x + xBFormula 2 * sin (2 * x),
       xBFormula 1 * sin x + xBFormula 2 * sin (2 * x)
         + xBFormula 3 * sin (3 * x),
       xBFormula 1 * sin x + xBFormula 2 * sin (2 * x)
         + xBFormula 3 * sin (3 * x) + xBFormula 4 * sin (4 * x),
       xBFormula 1 * sin x + xBFormula 2 * sin (2 * x)
         + xBFormula 3 * sin (3 * x) + xBFormula 4 * sin (4 * x)
         + xBFormula 5 * sin (5 * x))) := by
  funext x
  norm_num [xBFormula]
  constructor <;> ring

end

end FourierWithCoefficients
