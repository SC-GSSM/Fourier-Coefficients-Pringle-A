import Std

/-!
# Fourier coefficient exercises, without Mathlib

This file formalizes the algebraic content of the LaTeX solution in a
Mathlib-free way.  Since this project has no Mathlib/Lake setup, we do not use
Lean's real-analysis integral library.  Instead, the analytic fact

`the integral of an odd function over symmetric bounds is zero`

is recorded as a field of `SymmetricIntegral`.  The parity arguments then prove
the vanishing of the appropriate Fourier coefficients from that one assumption.
-/

namespace FourierCoef

/-! ## Parity -/

def IsOddFn (f : Rat -> Rat) : Prop :=
  forall x : Rat, f (-x) = -f x

def IsEvenFn (f : Rat -> Rat) : Prop :=
  forall x : Rat, f (-x) = f x

theorem id_is_odd : IsOddFn (fun x : Rat => x) := by
  intro x
  rfl

theorem square_is_even : IsEvenFn (fun x : Rat => x * x) := by
  intro x
  grind

theorem odd_mul_even_is_odd {f g : Rat -> Rat}
    (hf : IsOddFn f) (hg : IsEvenFn g) :
    IsOddFn (fun x => f x * g x) := by
  intro x
  change f (-x) * g (-x) = -(f x * g x)
  rw [hf x, hg x]
  grind

theorem even_mul_odd_is_odd {f g : Rat -> Rat}
    (hf : IsEvenFn f) (hg : IsOddFn g) :
    IsOddFn (fun x => f x * g x) := by
  intro x
  change f (-x) * g (-x) = -(f x * g x)
  rw [hf x, hg x]
  grind

/-! ## The symmetric-integral principle used in the written proof -/

structure SymmetricIntegral where
  integral : Rat -> (Rat -> Rat) -> Rat
  odd_integral_zero :
    forall (c : Rat) (f : Rat -> Rat), IsOddFn f -> integral c f = 0

theorem integral_of_odd_eq_zero (I : SymmetricIntegral)
    (c : Rat) {f : Rat -> Rat} (hf : IsOddFn f) :
    I.integral c f = 0 :=
  I.odd_integral_zero c f hf

/-!
`TrigParityKernel` is the small amount of trigonometry needed for the parity
proofs: cosine terms are even and sine terms are odd.
-/

structure TrigParityKernel where
  cosTerm : Nat -> Rat -> Rat
  sinTerm : Nat -> Rat -> Rat
  cos_even : forall n : Nat, IsEvenFn (cosTerm n)
  sin_odd : forall n : Nat, IsOddFn (sinTerm n)

def cosineCoefficientIntegral (I : SymmetricIntegral)
    (K : TrigParityKernel) (c : Rat) (f : Rat -> Rat) (n : Nat) : Rat :=
  I.integral c (fun x => f x * K.cosTerm n x)

def sineCoefficientIntegral (I : SymmetricIntegral)
    (K : TrigParityKernel) (c : Rat) (f : Rat -> Rat) (n : Nat) : Rat :=
  I.integral c (fun x => f x * K.sinTerm n x)

theorem cosine_coeff_zero_of_odd (I : SymmetricIntegral)
    (K : TrigParityKernel) (c : Rat) {f : Rat -> Rat}
    (hf : IsOddFn f) (n : Nat) :
    cosineCoefficientIntegral I K c f n = 0 := by
  unfold cosineCoefficientIntegral
  exact I.odd_integral_zero c _ (odd_mul_even_is_odd hf (K.cos_even n))

theorem sine_coeff_zero_of_even (I : SymmetricIntegral)
    (K : TrigParityKernel) (c : Rat) {f : Rat -> Rat}
    (hf : IsEvenFn f) (n : Nat) :
    sineCoefficientIntegral I K c f n = 0 := by
  unfold sineCoefficientIntegral
  exact I.odd_integral_zero c _ (even_mul_odd_is_odd hf (K.sin_odd n))

/-! ## Coefficients for `f(x) = x` -/

def xACoeff (_n : Nat) : Rat :=
  0

def xBCoeff (n : Nat) : Rat :=
  if n = 0 then
    0
  else
    (2 * (((-1 : Int) ^ (n + 1) : Int) : Rat)) / (n : Rat)

theorem x_aCoeff_eq_zero (n : Nat) : xACoeff n = 0 := by
  rfl

theorem x_bCoeff_formula {n : Nat} (h : Not (n = 0)) :
    xBCoeff n =
      (2 * (((-1 : Int) ^ (n + 1) : Int) : Rat)) / (n : Rat) := by
  unfold xBCoeff
  simp [h]

theorem x_b1 : xBCoeff 1 = 2 := by native_decide
theorem x_b2 : xBCoeff 2 = -1 := by native_decide
theorem x_b3 : xBCoeff 3 = (2 : Rat) / 3 := by native_decide
theorem x_b4 : xBCoeff 4 = (-1 : Rat) / 2 := by native_decide
theorem x_b5 : xBCoeff 5 = (2 : Rat) / 5 := by native_decide
theorem x_b6 : xBCoeff 6 = (-1 : Rat) / 3 := by native_decide

/-!
The first Fourier polynomials for `f(x) = x` are represented by their sine
coefficients.  The entry `(n, q)` means `q * sin(n*x)`.
-/

abbrev SinePolynomial := List (Nat × Rat)

def xFourierPolynomial : Nat -> SinePolynomial
  | 0 => []
  | n + 1 => xFourierPolynomial n ++ [(n + 1, xBCoeff (n + 1))]

theorem x_P1 : xFourierPolynomial 1 = [(1, 2)] := by native_decide

theorem x_P2 :
    xFourierPolynomial 2 = [(1, 2), (2, -1)] := by native_decide

theorem x_P3 :
    xFourierPolynomial 3 =
      [(1, 2), (2, -1), (3, (2 : Rat) / 3)] := by
  native_decide

theorem x_P4 :
    xFourierPolynomial 4 =
      [(1, 2), (2, -1), (3, (2 : Rat) / 3), (4, (-1 : Rat) / 2)] := by
  native_decide

theorem x_P5 :
    xFourierPolynomial 5 =
      [(1, 2), (2, -1), (3, (2 : Rat) / 3),
        (4, (-1 : Rat) / 2), (5, (2 : Rat) / 5)] := by
  native_decide

/-! ## Coefficients for `f(x) = x^2` -/

/- `ratTimesPiSq q` represents `q * pi^2`. -/
inductive Scalar where
  | rat : Rat -> Scalar
  | ratTimesPiSq : Rat -> Scalar
  deriving Repr, DecidableEq

def x2ACoeff (n : Nat) : Scalar :=
  if n = 0 then
    Scalar.ratTimesPiSq ((2 : Rat) / 3)
  else
    Scalar.rat ((4 * (((-1 : Int) ^ n : Int) : Rat)) / ((n * n : Nat) : Rat))

def x2BCoeff (_n : Nat) : Rat :=
  0

theorem x2_bCoeff_eq_zero (n : Nat) : x2BCoeff n = 0 := by
  rfl

theorem x2_a0 : x2ACoeff 0 = Scalar.ratTimesPiSq ((2 : Rat) / 3) := by
  native_decide

theorem x2_a1 : x2ACoeff 1 = Scalar.rat (-4) := by native_decide
theorem x2_a2 : x2ACoeff 2 = Scalar.rat 1 := by native_decide
theorem x2_a3 : x2ACoeff 3 = Scalar.rat ((-4 : Rat) / 9) := by native_decide
theorem x2_a4 : x2ACoeff 4 = Scalar.rat ((1 : Rat) / 4) := by native_decide
theorem x2_a5 : x2ACoeff 5 = Scalar.rat ((-4 : Rat) / 25) := by native_decide

theorem x2_aCoeff_formula {n : Nat} (h : Not (n = 0)) :
    x2ACoeff n =
      Scalar.rat
        ((4 * (((-1 : Int) ^ n : Int) : Rat)) / ((n * n : Nat) : Rat)) := by
  unfold x2ACoeff
  simp [h]

/-! ## The two general conjectures from the written solution -/

theorem all_cosine_coefficients_vanish_for_odd_functions
    (I : SymmetricIntegral) (K : TrigParityKernel)
    (c : Rat) {f : Rat -> Rat} (hf : IsOddFn f) :
    forall n : Nat, cosineCoefficientIntegral I K c f n = 0 := by
  intro n
  exact cosine_coeff_zero_of_odd I K c hf n

theorem all_sine_coefficients_vanish_for_even_functions
    (I : SymmetricIntegral) (K : TrigParityKernel)
    (c : Rat) {f : Rat -> Rat} (hf : IsEvenFn f) :
    forall n : Nat, sineCoefficientIntegral I K c f n = 0 := by
  intro n
  exact sine_coeff_zero_of_even I K c hf n

end FourierCoef
