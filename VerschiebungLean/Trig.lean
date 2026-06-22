import VerschiebungLean.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Data.Complex.BigOperators
import Mathlib.RingTheory.RootsOfUnity.Complex

set_option linter.style.header false

namespace VerschiebungLean

open Finset Real
open scoped BigOperators

/-!
# The square-root-free finite Verlinde identity

This file records the trigonometric identity used in the level-one count in a
Lean-friendly normalization.

The paper notation uses coefficients
`N_{ab}^c`, equal to `1` when `(a,b,c)` is an admissible level-one triple for
the parameter `2p`, and equal to `0` otherwise.  The square-root-free form of
the finite Verlinde identity is the statement that this coefficient is equal to
a finite sine sum plus the endpoint contribution.

The final identity is encoded below as the proposition
`finiteVerlindeKernelIdentity`.  The surrounding lemmas prove the elementary
parts of the setup: the level-one predicate agrees with the local definition
from `Defs.lean`, and the denominators in the finite sine sum are nonzero on
the summation range.

Here is the proof strategy in ordinary mathematical language.

1.  We first evaluate the elementary finite cosine sums
    \[
      \sum_{j=1}^{p-1}\cos(qj\pi/p).
    \]
    Even modes are handled by roots of unity; odd modes vanish by the
    reflection symmetry `j ↦ p-j`.

2.  These cosine sums imply an endpoint-corrected sine orthogonality relation:
    the kernel `sineKernel p r s` is `1` on the diagonal `r=s`, is `-1` at the
    reflected index `r+s+1=2p`, and is `0` otherwise.

3.  A finite Clebsch-Gordan identity rewrites the product of two odd sine modes
    as a telescoping sum.  This turns the Verlinde kernel into a finite sum of
    the orthogonality kernels.

4.  The final step is purely arithmetic: the interval
    `[|a-b|, a+b]` contains `c` exactly when the triangle inequalities hold,
    while the reflected index `2p-1-c` records the failure of the upper bound
    `a+b+c+2 ≤ 2p`.
-/

/--
The level-one admissibility condition for labels `a,b,c` at parameter `2p`.

We write the upper bound as `a + b + c + 2 ≤ 2 * p` instead of
`a + b + c ≤ 2 * p - 2`, avoiding subtraction on natural numbers.
-/
def C1Even (p a b c : ℕ) : Prop :=
  a + b + c + 2 ≤ 2 * p ∧
  a ≤ b + c ∧
  b ≤ a + c ∧
  c ≤ a + b

/-- The coefficient `N_{ab}^c`, valued in `ℝ`. -/
noncomputable def fusionN (p a b c : ℕ) : ℝ :=
  by
    classical
    exact if h : C1Even p a b c then 1 else 0

/-- The angle `jπ/(2p)` used in the finite sine sum. -/
noncomputable def theta (p j : ℕ) : ℝ :=
  (j : ℝ) * π / (2 * (p : ℝ))

/--
The square-root-free finite Verlinde kernel.

This is the expression
\[
\frac{2}{p}\sum_{j=1}^{p-1}
\frac{\sin((2a+1)\theta_j)\sin((2b+1)\theta_j)\sin((2c+1)\theta_j)}
{\sin(\theta_j)}
+\frac{(-1)^{a+b+c}}{p}.
\]
-/
noncomputable def verlindeKernel (p a b c : ℕ) : ℝ :=
  (2 / (p : ℝ)) *
    (Finset.Icc 1 (p - 1)).sum (fun j =>
      sin (((2 * a + 1 : ℕ) : ℝ) * theta p j) *
      sin (((2 * b + 1 : ℕ) : ℝ) * theta p j) *
      sin (((2 * c + 1 : ℕ) : ℝ) * theta p j) /
      sin (theta p j))
  + ((-1 : ℝ) ^ (a + b + c)) / (p : ℝ)

/--
The finite Verlinde identity in the square-root-free normalization.

This is the precise theorem to prove:
`fusionN p a b c = verlindeKernel p a b c` for labels `a,b,c < p`.
-/
def finiteVerlindeKernelIdentity (p a b c : ℕ) : Prop :=
  0 < p → a < p → b < p → c < p →
    fusionN p a b c = verlindeKernel p a b c

/-- The standalone universal statement of the finite Verlinde kernel identity. -/
def finiteVerlindeKernelTheorem : Prop :=
  ∀ p a b c : ℕ, finiteVerlindeKernelIdentity p a b c

/--
Compatibility with the local combinatorial predicate from `Defs.lean`.

At level one and parameter `2p`, the folded residue conditions are vacuous, so
the local predicate `C` is exactly the four inequalities packaged in `C1Even`.
-/
lemma C1Even_iff_C (p a b c : ℕ) :
    C1Even p a b c ↔
      C (2 * p) 1 (fun i : Fin 3 =>
        match i with
        | 0 => a
        | 1 => b
        | 2 => c) := by
  constructor
  · intro h
    constructor
    · simpa [Upper, C1Even] using h
    · intro M _ hM
      omega
  · intro h
    simpa [C, Upper, C1Even] using h.1

lemma theta_pos {p j : ℕ} (hp : 0 < p) (hj : 1 ≤ j) :
    0 < theta p j := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hjR : 0 < (j : ℝ) := by exact_mod_cast hj
  unfold theta
  positivity

lemma theta_eq_ratio_mul (p j : ℕ) (hp : 0 < p) :
    theta p j = ((j : ℝ) / (p : ℝ)) * (π / 2) := by
  have hpR : (p : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hp)
  unfold theta
  field_simp [hpR]

lemma theta_lt_pi_div_two {p j : ℕ} (hp : 0 < p) (hj : j ≤ p - 1) :
    theta p j < π / 2 := by
  have hpRpos : 0 < (p : ℝ) := by exact_mod_cast hp
  have hjlt : j < p := Nat.lt_of_le_pred hp hj
  have hjltR : (j : ℝ) < (p : ℝ) := by exact_mod_cast hjlt
  rw [theta_eq_ratio_mul p j hp]
  have hratio : (j : ℝ) / (p : ℝ) < 1 := (div_lt_one hpRpos).mpr hjltR
  nlinarith [pi_pos]

lemma theta_lt_pi {p j : ℕ} (hp : 0 < p) (hj : j ≤ p - 1) :
    theta p j < π := by
  have h := theta_lt_pi_div_two hp hj
  nlinarith [pi_pos]

lemma sin_theta_pos {p j : ℕ} (hp : 0 < p) (hj1 : 1 ≤ j) (hjp : j ≤ p - 1) :
    0 < sin (theta p j) := by
  exact sin_pos_of_mem_Ioo ⟨theta_pos hp hj1, theta_lt_pi hp hjp⟩

lemma sin_theta_ne_zero {p j : ℕ} (hp : 0 < p) (hj1 : 1 ≤ j) (hjp : j ≤ p - 1) :
    sin (theta p j) ≠ 0 :=
  ne_of_gt (sin_theta_pos hp hj1 hjp)

/-!
## Elementary cosine sums

The sine orthogonality calculation is reduced to finite sums of cosine modes.
For even modes we use the geometric series for a nontrivial root of unity.  For
odd modes we use the involution `j ↦ p-j`, under which the cosine changes sign.
-/

/-- The cosine mode `cos(q j π / p)` used in the finite sine-transform calculation. -/
noncomputable def cosMode (p q j : ℕ) : ℝ :=
  cos (((q : ℝ) * (j : ℝ) * π) / (p : ℝ))

/-- The odd sine mode `sin((2r+1)jπ/(2p))`. -/
noncomputable def sinOdd (p r j : ℕ) : ℝ :=
  sin (((2 * r + 1 : ℕ) : ℝ) * theta p j)

lemma complex_exp_mul_I_re (x : ℝ) :
    (Complex.exp ((x : ℂ) * Complex.I)).re = cos x := by
  rw [Complex.exp_mul_I]
  change (Complex.cos (x : ℂ)).re + (Complex.sin (x : ℂ) * Complex.I).re = cos x
  rw [show (Complex.sin (x : ℂ) * Complex.I).re = 0 by simp]
  simp only [add_zero]
  have hcos := congrArg Complex.re (Complex.ofReal_cos x)
  change (Complex.cos (x : ℂ)).re = ((cos x : ℝ) : ℂ).re
  exact hcos.symm

lemma exp_root_re_cosMode (p m j : ℕ) :
    ((Complex.exp (2 * ↑π * Complex.I / (p : ℂ)) ^ m) ^ j).re =
      cosMode p (2 * m) j := by
  rw [← pow_mul]
  rw [← Complex.exp_nat_mul]
  unfold cosMode
  conv_lhs =>
    rw [show
        ((m * j : ℕ) : ℂ) * (2 * ↑π * Complex.I / ↑p) =
          ((((2 * m : ℕ) : ℝ) * (j : ℝ) * π) / (p : ℝ) : ℝ) * Complex.I by
      rw [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_natCast]
      norm_num
      ring_nf]
  exact complex_exp_mul_I_re _

lemma complex_geom_sum_root {p m : ℕ} (hp : p ≠ 0) (hpm : ¬ p ∣ m) :
    (∑ j ∈ Finset.range p, (Complex.exp (2 * ↑π * Complex.I / (p : ℂ)) ^ m) ^ j) = 0 := by
  let ζ : ℂ := Complex.exp (2 * ↑π * Complex.I / (p : ℂ))
  have hζ : IsPrimitiveRoot ζ p := Complex.isPrimitiveRoot_exp p hp
  have hpow : (ζ ^ m) ^ p = (1 : ℂ) := by
    rw [← pow_mul, mul_comm m p, pow_mul, hζ.pow_eq_one]
    simp
  have hne : ζ ^ m ≠ (1 : ℂ) := by
    intro h
    exact hpm (hζ.dvd_of_pow_eq_one m h)
  have hgeom := geom_sum_eq hne p
  simpa [ζ, hpow] using hgeom

lemma range_eq_insert_Icc_one_pred {p : ℕ} (hp : p ≠ 0) :
    Finset.range p = insert 0 (Finset.Icc 1 (p - 1)) := by
  ext j
  simp only [mem_range, mem_insert, mem_Icc]
  omega

lemma Icc_one_pred_eq_Ico_one {p : ℕ} (_hp : p ≠ 0) :
    Finset.Icc 1 (p - 1) = Finset.Ico 1 p := by
  ext j
  simp only [mem_Icc, mem_Ico]
  omega

lemma nat_pred_cast_eq_sub_one {p : ℕ} (hp : p ≠ 0) :
    ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
  have hp1 : 1 ≤ p := Nat.pos_of_ne_zero hp
  have h : (p - 1 : ℕ) + 1 = p := Nat.sub_add_cancel hp1
  have hR : ((p - 1 : ℕ) : ℝ) + 1 = (p : ℝ) := by exact_mod_cast h
  linarith

lemma not_dvd_of_pos_lt {p m : ℕ} (hm0 : 0 < m) (hmp : m < p) : ¬ p ∣ m := by
  rintro ⟨k, rfl⟩
  cases k with
  | zero => omega
  | succ k => nlinarith [Nat.le_mul_of_pos_right p (Nat.succ_pos k)]

lemma not_dvd_of_pos_lt_two_mul_ne {p m : ℕ} (hm0 : 0 < m) (hm2 : m < 2 * p)
    (hmp : m ≠ p) : ¬ p ∣ m := by
  rintro ⟨k, rfl⟩
  cases k with
  | zero => omega
  | succ k =>
      cases k with
      | zero => omega
      | succ k => nlinarith [Nat.mul_le_mul_left p (show 2 ≤ Nat.succ (Nat.succ k) by omega)]

/--
The basic even-mode cosine sum.

The full sum from `j=0` to `p-1` is a nontrivial geometric series and hence is
zero.  Removing the `j=0` term leaves `-1`.
-/
lemma cosMode_even_sum_Icc_nonmultiple {p m : ℕ} (hp : p ≠ 0) (hpm : ¬ p ∣ m) :
    (∑ j ∈ Finset.Icc 1 (p - 1), cosMode p (2 * m) j) = -1 := by
  have h := congrArg Complex.re (complex_geom_sum_root (p := p) (m := m) hp hpm)
  rw [Complex.re_sum] at h
  simp_rw [exp_root_re_cosMode] at h
  rw [range_eq_insert_Icc_one_pred (p := p) hp] at h
  rw [Finset.sum_insert] at h
  · unfold cosMode at h ⊢
    simp only [Nat.cast_mul, Nat.cast_ofNat] at h ⊢
    simp at h
    linarith
  · simp

lemma cosMode_zero_sum_Icc (p : ℕ) :
    (∑ j ∈ Finset.Icc 1 (p - 1), cosMode p 0 j) = ((p - 1 : ℕ) : ℝ) := by
  simp [cosMode]

lemma cosMode_two_mul_self_sum_Icc {p : ℕ} (hp : p ≠ 0) :
    (∑ j ∈ Finset.Icc 1 (p - 1), cosMode p (2 * p) j) = ((p - 1 : ℕ) : ℝ) := by
  have hterm : ∀ j ∈ Finset.Icc 1 (p - 1), cosMode p (2 * p) j = 1 := by
    intro j _hj
    unfold cosMode
    have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp
    have hangle : ((↑(2 * p) * ↑j * π) / ↑p : ℝ) = (j : ℕ) * (2 * π) := by
      field_simp [hpR]
      norm_num
      ring_nf
    rw [hangle]
    exact cos_nat_mul_two_pi j
  calc
    (∑ j ∈ Finset.Icc 1 (p - 1), cosMode p (2 * p) j)
        = ∑ j ∈ Finset.Icc 1 (p - 1), (1 : ℝ) := by
          exact Finset.sum_congr rfl hterm
    _ = ((p - 1 : ℕ) : ℝ) := by simp

/--
Odd cosine modes are anti-invariant under the reflection `j ↦ p-j`.

This is the elementary reason the odd-mode sum below vanishes.
-/
lemma cosMode_reflect_odd {p q j : ℕ} (hp : p ≠ 0) (hj : j ≤ p) (hqodd : q % 2 = 1) :
    cosMode p q (p - j) = -cosMode p q j := by
  unfold cosMode
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp
  obtain ⟨k, hk⟩ : ∃ k, q = 2 * k + 1 := by
    refine ⟨q / 2, ?_⟩
    have hdiv := Nat.div_add_mod q 2
    omega
  subst q
  have hangle :
      (((2 * k + 1 : ℕ) : ℝ) * ((p - j : ℕ) : ℝ) * π) / (p : ℝ) =
        ((2 * k + 1 : ℕ) : ℝ) * π -
          (((2 * k + 1 : ℕ) : ℝ) * (j : ℝ) * π) / (p : ℝ) := by
    rw [Nat.cast_sub hj]
    field_simp [hpR]
  rw [hangle, cos_sub, cos_nat_mul_pi, sin_nat_mul_pi]
  have hpow : ((-1 : ℝ) ^ (2 * k + 1)) = -1 := by
    rw [neg_one_pow_eq_neg_one_iff_odd (by norm_num : (-1 : ℝ) ≠ 1)]
    exact ⟨k, by omega⟩
  rw [hpow]
  ring

lemma cosMode_odd_sum_Icc {p q : ℕ} (hp : p ≠ 0) (hqodd : q % 2 = 1) :
    (∑ j ∈ Finset.Icc 1 (p - 1), cosMode p q j) = 0 := by
  rw [Icc_one_pred_eq_Ico_one (p := p) hp]
  have hreflect := Finset.sum_Ico_reflect (fun j => cosMode p q j) 1 (m := p) (n := p) (by omega)
  have hleft :
      (∑ j ∈ Finset.Ico 1 p, cosMode p q (p - j)) =
        ∑ j ∈ Finset.Ico 1 p, -cosMode p q j := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hjle : j ≤ p := (Finset.mem_Ico.mp hj).2.le
    exact cosMode_reflect_odd hp hjle hqodd
  rw [hleft, Finset.sum_neg_distrib] at hreflect
  simp at hreflect
  linarith

/--
The elementary product-to-sum identity for odd sine modes.

This is just `2 sin A sin B = cos(A-B)-cos(A+B)`, rewritten in the indexing
used in the finite Verlinde formula.
-/
lemma two_sinOdd_mul_sinOdd_eq_cos_sub_of_le {p r s j : ℕ} (hsr : s ≤ r) :
    2 * sinOdd p r j * sinOdd p s j =
      cosMode p (r - s) j - cosMode p (r + s + 1) j := by
  let A : ℝ := ((2 * r + 1 : ℕ) : ℝ) * theta p j
  let B : ℝ := ((2 * s + 1 : ℕ) : ℝ) * theta p j
  have hdiff : cosMode p (r - s) j = cos (A - B) := by
    unfold cosMode A B theta
    rw [Nat.cast_sub hsr]
    congr 1
    field_simp
    ring_nf
    norm_num
    ring
  have hsum : cosMode p (r + s + 1) j = cos (A + B) := by
    unfold cosMode A B theta
    congr 1
    field_simp
    ring_nf
    norm_num
    ring
  calc
    2 * sinOdd p r j * sinOdd p s j = 2 * sin A * sin B := by rfl
    _ = cos (A - B) - cos (A + B) := by
      rw [cos_sub, cos_add]
      ring
    _ = cosMode p (r - s) j - cosMode p (r + s + 1) j := by rw [hdiff, hsum]

lemma two_sinOdd_mul_sinOdd_eq_cos_sub_of_ge {p r s j : ℕ} (hrs : r ≤ s) :
    2 * sinOdd p r j * sinOdd p s j =
      cosMode p (s - r) j - cosMode p (r + s + 1) j := by
  have h := two_sinOdd_mul_sinOdd_eq_cos_sub_of_le (p := p) (r := s) (s := r) (j := j) hrs
  rw [add_comm s r] at h
  nlinarith [h]

lemma two_mul_sum_sinOdd_mul_eq_of_le {p r s : ℕ} (hsr : s ≤ r) :
    2 * (∑ j ∈ Finset.Icc 1 (p - 1), sinOdd p r j * sinOdd p s j) =
      (∑ j ∈ Finset.Icc 1 (p - 1), cosMode p (r - s) j) -
        (∑ j ∈ Finset.Icc 1 (p - 1), cosMode p (r + s + 1) j) := by
  calc
    2 * (∑ j ∈ Finset.Icc 1 (p - 1), sinOdd p r j * sinOdd p s j)
        = ∑ j ∈ Finset.Icc 1 (p - 1), 2 * (sinOdd p r j * sinOdd p s j) := by
          rw [Finset.mul_sum]
    _ = ∑ j ∈ Finset.Icc 1 (p - 1),
          (cosMode p (r - s) j - cosMode p (r + s + 1) j) := by
          refine Finset.sum_congr rfl ?_
          intro j _hj
          have h := two_sinOdd_mul_sinOdd_eq_cos_sub_of_le (p := p) (r := r) (s := s) (j := j) hsr
          nlinarith [h]
    _ = (∑ j ∈ Finset.Icc 1 (p - 1), cosMode p (r - s) j) -
        (∑ j ∈ Finset.Icc 1 (p - 1), cosMode p (r + s + 1) j) := by
          rw [Finset.sum_sub_distrib]

lemma two_mul_sum_sinOdd_mul_eq_of_ge {p r s : ℕ} (hrs : r ≤ s) :
    2 * (∑ j ∈ Finset.Icc 1 (p - 1), sinOdd p r j * sinOdd p s j) =
      (∑ j ∈ Finset.Icc 1 (p - 1), cosMode p (s - r) j) -
        (∑ j ∈ Finset.Icc 1 (p - 1), cosMode p (r + s + 1) j) := by
  calc
    2 * (∑ j ∈ Finset.Icc 1 (p - 1), sinOdd p r j * sinOdd p s j)
        = ∑ j ∈ Finset.Icc 1 (p - 1), 2 * (sinOdd p r j * sinOdd p s j) := by
          rw [Finset.mul_sum]
    _ = ∑ j ∈ Finset.Icc 1 (p - 1),
          (cosMode p (s - r) j - cosMode p (r + s + 1) j) := by
          refine Finset.sum_congr rfl ?_
          intro j _hj
          have h := two_sinOdd_mul_sinOdd_eq_cos_sub_of_ge (p := p) (r := r) (s := s) (j := j) hrs
          nlinarith [h]
    _ = (∑ j ∈ Finset.Icc 1 (p - 1), cosMode p (s - r) j) -
        (∑ j ∈ Finset.Icc 1 (p - 1), cosMode p (r + s + 1) j) := by
          rw [Finset.sum_sub_distrib]

/-- The endpoint-corrected finite sine inner product. -/
noncomputable def sineKernel (p r s : ℕ) : ℝ :=
  (2 / (p : ℝ)) * (∑ j ∈ Finset.Icc 1 (p - 1), sinOdd p r j * sinOdd p s j) +
    ((-1 : ℝ) ^ (r + s)) / (p : ℝ)

/-!
## Endpoint-corrected sine orthogonality

The usual finite sine transform is almost orthogonal.  In this odd-label
normalization there is also a reflected index: `r` pairs with `2p-1-r`.
The endpoint correction `(-1)^(r+s)/p` is exactly what makes the final answer
take the clean values `1`, `-1`, and `0`.
-/

lemma neg_one_pow_add_self (r : ℕ) : ((-1 : ℝ) ^ (r + r)) = 1 := by
  rw [neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℝ) ≠ 1)]
  exact ⟨r, by omega⟩

lemma neg_one_pow_of_reflect {p r s : ℕ} (_hp : p ≠ 0) (h : r + s + 1 = 2 * p) :
    ((-1 : ℝ) ^ (r + s)) = -1 := by
  rw [neg_one_pow_eq_neg_one_iff_odd (by norm_num : (-1 : ℝ) ≠ 1)]
  exact ⟨p - 1, by omega⟩

lemma diff_mod_two_one_of_reflect_left {p r s : ℕ} (hrs : r ≤ s)
    (h : r + s + 1 = 2 * p) :
    (s - r) % 2 = 1 := by
  omega

lemma diff_mod_two_one_of_reflect_right {p r s : ℕ} (hsr : s ≤ r)
    (h : r + s + 1 = 2 * p) :
    (r - s) % 2 = 1 := by
  omega

lemma sineKernel_same {p r : ℕ} (hp : p ≠ 0) : sineKernel p r r = 1 := by
  let S := ∑ j ∈ Finset.Icc 1 (p - 1), sinOdd p r j * sinOdd p r j
  have htwo := two_mul_sum_sinOdd_mul_eq_of_le (p := p) (r := r) (s := r) (le_rfl)
  change 2 * S = _ - _ at htwo
  have hzero := cosMode_zero_sum_Icc p
  have hodd : (2 * r + 1) % 2 = 1 := by omega
  have hsumodd := cosMode_odd_sum_Icc (p := p) (q := 2 * r + 1) hp hodd
  rw [Nat.sub_self, hzero] at htwo
  rw [show r + r + 1 = 2 * r + 1 by omega, hsumodd, sub_zero] at htwo
  unfold sineKernel
  change (2 / (p : ℝ)) * S + ((-1 : ℝ) ^ (r + r)) / (p : ℝ) = 1
  rw [neg_one_pow_add_self]
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp
  have hpPred : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := nat_pred_cast_eq_sub_one hp
  rw [hpPred] at htwo
  field_simp [hpR]
  nlinarith

lemma sineKernel_reflect {p r s : ℕ} (hp : p ≠ 0) (href : r + s + 1 = 2 * p) :
    sineKernel p r s = -1 := by
  let S := ∑ j ∈ Finset.Icc 1 (p - 1), sinOdd p r j * sinOdd p s j
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp
  have hpPred : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := nat_pred_cast_eq_sub_one hp
  have hsign := neg_one_pow_of_reflect hp href
  rcases le_total r s with hrs | hsr
  · have htwo := two_mul_sum_sinOdd_mul_eq_of_ge (p := p) (r := r) (s := s) hrs
    change 2 * S = _ - _ at htwo
    have hdiffodd := cosMode_odd_sum_Icc (p := p) (q := s - r) hp
      (diff_mod_two_one_of_reflect_left hrs href)
    have hsum := cosMode_two_mul_self_sum_Icc (p := p) hp
    rw [hdiffodd] at htwo
    rw [href, hsum] at htwo
    unfold sineKernel
    change (2 / (p : ℝ)) * S + ((-1 : ℝ) ^ (r + s)) / (p : ℝ) = -1
    rw [hsign]
    rw [hpPred] at htwo
    field_simp [hpR]
    nlinarith
  · have htwo := two_mul_sum_sinOdd_mul_eq_of_le (p := p) (r := r) (s := s) hsr
    change 2 * S = _ - _ at htwo
    have hdiffodd := cosMode_odd_sum_Icc (p := p) (q := r - s) hp
      (diff_mod_two_one_of_reflect_right hsr href)
    have hsum := cosMode_two_mul_self_sum_Icc (p := p) hp
    rw [hdiffodd] at htwo
    rw [href, hsum] at htwo
    unfold sineKernel
    change (2 / (p : ℝ)) * S + ((-1 : ℝ) ^ (r + s)) / (p : ℝ) = -1
    rw [hsign]
    rw [hpPred] at htwo
    field_simp [hpR]
    nlinarith

/--
The zero cases for `sineKernel` are split into parity and order cases.

Mathematically all four auxiliary lemmas say the same thing: away from the
diagonal and the reflected diagonal, the two cosine sums cancel the endpoint
term.  The split keeps the natural-number subtraction in Lean manageable.
-/
lemma sineKernel_zero_aux_left_even {p r s : ℕ} (hp : 1 < p) (hrs : r ≤ s)
    (hs : s < p) (hne : r ≠ s) (heven : (r + s) % 2 = 0) :
    sineKernel p r s = 0 := by
  let S := ∑ j ∈ Finset.Icc 1 (p - 1), sinOdd p r j * sinOdd p s j
  have hp0 : p ≠ 0 := by omega
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp0
  have htwo := two_mul_sum_sinOdd_mul_eq_of_ge (p := p) (r := r) (s := s) hrs
  change 2 * S = _ - _ at htwo
  have hdiffEven : (s - r) % 2 = 0 := by omega
  let m := (s - r) / 2
  have hdiffEq : s - r = 2 * m := by
    dsimp [m]
    have hdiv := Nat.div_add_mod (s - r) 2
    omega
  have hmpos : 0 < m := by
    dsimp [m]
    have : r < s := lt_of_le_of_ne hrs hne
    have hdiv := Nat.div_add_mod (s - r) 2
    omega
  have hmlt : m < p := by
    dsimp [m]
    omega
  have hdiffsum := cosMode_even_sum_Icc_nonmultiple (p := p) (m := m) hp0
    (not_dvd_of_pos_lt hmpos hmlt)
  have hsumodd : (r + s + 1) % 2 = 1 := by omega
  have hsum := cosMode_odd_sum_Icc (p := p) (q := r + s + 1) hp0 hsumodd
  rw [hdiffEq, hdiffsum, hsum] at htwo
  have hsign : ((-1 : ℝ) ^ (r + s)) = 1 := by
    rw [neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℝ) ≠ 1)]
    exact ⟨(r + s) / 2, by
      have hdiv := Nat.div_add_mod (r + s) 2
      omega⟩
  unfold sineKernel
  change (2 / (p : ℝ)) * S + ((-1 : ℝ) ^ (r + s)) / (p : ℝ) = 0
  rw [hsign]
  field_simp [hpR]
  nlinarith

lemma sineKernel_zero_aux_left_odd {p r s : ℕ} (hp : 1 < p) (hrs : r ≤ s)
    (hs : s < p) (hodd : (r + s) % 2 = 1) :
    sineKernel p r s = 0 := by
  let S := ∑ j ∈ Finset.Icc 1 (p - 1), sinOdd p r j * sinOdd p s j
  have hp0 : p ≠ 0 := by omega
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp0
  have htwo := two_mul_sum_sinOdd_mul_eq_of_ge (p := p) (r := r) (s := s) hrs
  change 2 * S = _ - _ at htwo
  have hdiffOdd : (s - r) % 2 = 1 := by omega
  have hdiffsum := cosMode_odd_sum_Icc (p := p) (q := s - r) hp0 hdiffOdd
  have hsumEven : (r + s + 1) % 2 = 0 := by omega
  let m := (r + s + 1) / 2
  have hsumEq : r + s + 1 = 2 * m := by
    dsimp [m]
    have hdiv := Nat.div_add_mod (r + s + 1) 2
    omega
  have hmpos : 0 < m := by
    dsimp [m]
    omega
  have hmlt : m < p := by
    dsimp [m]
    omega
  have hsum := cosMode_even_sum_Icc_nonmultiple (p := p) (m := m) hp0
    (not_dvd_of_pos_lt hmpos hmlt)
  rw [hdiffsum, hsumEq, hsum] at htwo
  have hsign : ((-1 : ℝ) ^ (r + s)) = -1 := by
    rw [neg_one_pow_eq_neg_one_iff_odd (by norm_num : (-1 : ℝ) ≠ 1)]
    exact ⟨(r + s) / 2, by
      have hdiv := Nat.div_add_mod (r + s) 2
      omega⟩
  unfold sineKernel
  change (2 / (p : ℝ)) * S + ((-1 : ℝ) ^ (r + s)) / (p : ℝ) = 0
  rw [hsign]
  field_simp [hpR]
  nlinarith

lemma sineKernel_zero_aux_right_even {p r s : ℕ} (hp : 1 < p) (hsr : s ≤ r)
    (hr : r ≤ 2 * p - 2) (hne : r ≠ s) (heven : (r + s) % 2 = 0) :
    sineKernel p r s = 0 := by
  let S := ∑ j ∈ Finset.Icc 1 (p - 1), sinOdd p r j * sinOdd p s j
  have hp0 : p ≠ 0 := by omega
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp0
  have htwo := two_mul_sum_sinOdd_mul_eq_of_le (p := p) (r := r) (s := s) hsr
  change 2 * S = _ - _ at htwo
  have hdiffEven : (r - s) % 2 = 0 := by omega
  let m := (r - s) / 2
  have hdiffEq : r - s = 2 * m := by
    dsimp [m]
    have hdiv := Nat.div_add_mod (r - s) 2
    omega
  have hmpos : 0 < m := by
    dsimp [m]
    have : s < r := lt_of_le_of_ne hsr hne.symm
    have hdiv := Nat.div_add_mod (r - s) 2
    omega
  have hmlt : m < p := by
    dsimp [m]
    omega
  have hdiffsum := cosMode_even_sum_Icc_nonmultiple (p := p) (m := m) hp0
    (not_dvd_of_pos_lt hmpos hmlt)
  have hsumodd : (r + s + 1) % 2 = 1 := by omega
  have hsum := cosMode_odd_sum_Icc (p := p) (q := r + s + 1) hp0 hsumodd
  rw [hdiffEq, hdiffsum, hsum] at htwo
  have hsign : ((-1 : ℝ) ^ (r + s)) = 1 := by
    rw [neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℝ) ≠ 1)]
    exact ⟨(r + s) / 2, by
      have hdiv := Nat.div_add_mod (r + s) 2
      omega⟩
  unfold sineKernel
  change (2 / (p : ℝ)) * S + ((-1 : ℝ) ^ (r + s)) / (p : ℝ) = 0
  rw [hsign]
  field_simp [hpR]
  nlinarith

lemma sineKernel_zero_aux_right_odd {p r s : ℕ} (hp : 1 < p) (hsr : s ≤ r)
    (hr : r ≤ 2 * p - 2) (_hs : s < p) (hnotref : r + s + 1 ≠ 2 * p)
    (hodd : (r + s) % 2 = 1) :
    sineKernel p r s = 0 := by
  let S := ∑ j ∈ Finset.Icc 1 (p - 1), sinOdd p r j * sinOdd p s j
  have hp0 : p ≠ 0 := by omega
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp0
  have htwo := two_mul_sum_sinOdd_mul_eq_of_le (p := p) (r := r) (s := s) hsr
  change 2 * S = _ - _ at htwo
  have hdiffOdd : (r - s) % 2 = 1 := by omega
  have hdiffsum := cosMode_odd_sum_Icc (p := p) (q := r - s) hp0 hdiffOdd
  have hsumEven : (r + s + 1) % 2 = 0 := by omega
  let m := (r + s + 1) / 2
  have hsumEq : r + s + 1 = 2 * m := by
    dsimp [m]
    have hdiv := Nat.div_add_mod (r + s + 1) 2
    omega
  have hmpos : 0 < m := by
    dsimp [m]
    omega
  have hmlt2 : m < 2 * p := by
    dsimp [m]
    omega
  have hmne : m ≠ p := by
    intro hm
    apply hnotref
    rw [hsumEq, hm]
  have hsum := cosMode_even_sum_Icc_nonmultiple (p := p) (m := m) hp0
    (not_dvd_of_pos_lt_two_mul_ne hmpos hmlt2 hmne)
  rw [hdiffsum, hsumEq, hsum] at htwo
  have hsign : ((-1 : ℝ) ^ (r + s)) = -1 := by
    rw [neg_one_pow_eq_neg_one_iff_odd (by norm_num : (-1 : ℝ) ≠ 1)]
    exact ⟨(r + s) / 2, by
      have hdiv := Nat.div_add_mod (r + s) 2
      omega⟩
  unfold sineKernel
  change (2 / (p : ℝ)) * S + ((-1 : ℝ) ^ (r + s)) / (p : ℝ) = 0
  rw [hsign]
  field_simp [hpR]
  nlinarith

lemma sineKernel_zero_of_ne_of_not_reflect {p r s : ℕ} (hp : 1 < p)
    (hr : r ≤ 2 * p - 2) (hs : s < p) (hne : r ≠ s)
    (hnotref : r + s + 1 ≠ 2 * p) :
    sineKernel p r s = 0 := by
  rcases le_total r s with hrs | hsr
  · rcases Nat.mod_two_eq_zero_or_one (r + s) with heven | hodd
    · exact sineKernel_zero_aux_left_even hp hrs hs hne heven
    · exact sineKernel_zero_aux_left_odd hp hrs hs hodd
  · rcases Nat.mod_two_eq_zero_or_one (r + s) with heven | hodd
    · exact sineKernel_zero_aux_right_even hp hsr hr hne heven
    · exact sineKernel_zero_aux_right_odd hp hsr hr hs hnotref hodd

/--
The finite sine orthogonality relation in endpoint-corrected form.

For `0 ≤ r ≤ 2p-2` and `0 ≤ s < p`, the kernel is:
* `1` if `r=s`;
* `-1` if `r` is the reflected label `2p-1-s`;
* `0` otherwise.
-/
lemma sineKernel_orthogonality {p r s : ℕ} (hp : 1 < p)
    (hr : r ≤ 2 * p - 2) (hs : s < p) :
    sineKernel p r s =
      if r = s then 1 else if r + s + 1 = 2 * p then -1 else 0 := by
  by_cases hrs : r = s
  · subst s
    simp [sineKernel_same (p := p) (r := r) (by omega)]
  · by_cases href : r + s + 1 = 2 * p
    · simp [hrs, href, sineKernel_reflect (p := p) (r := r) (s := s) (by omega) href]
    · simp [hrs, href, sineKernel_zero_of_ne_of_not_reflect hp hr hs hrs href]

/-!
## Clebsch-Gordan telescoping

The next group of lemmas formalizes the elementary finite Clebsch-Gordan
identity.  The key point is that
\[
  2\sin((2a+1)\theta)\sin((2b+1)\theta)
\]
is a telescoping sum of terms
\[
  2\sin((2d+1)\theta)\sin(\theta)
\]
as `d` runs through the interval `[|a-b|,a+b]`.
-/

lemma sum_Ico_sub_succ (f : ℕ → ℝ) {L U : ℕ} (hLU : L ≤ U) :
    (∑ d ∈ Finset.Ico L (U + 1), (f d - f (d + 1))) = f L - f (U + 1) := by
  rw [Finset.sum_sub_distrib]
  have hL : L < U + 1 := by omega
  have hU : L + 1 ≤ U + 1 := by omega
  have hshift :
      (∑ d ∈ Finset.Ico L (U + 1), f (d + 1)) =
        ∑ d ∈ Finset.Ico (L + 1) (U + 2), f d := by
    simpa [add_comm, add_left_comm, add_assoc] using
      (Finset.sum_Ico_add' (fun x => f x) L (U + 1) 1)
  rw [hshift]
  have hA := Finset.sum_eq_sum_Ico_succ_bot hL f
  have hB := Finset.sum_Ico_succ_sub_top f (m := L + 1) (n := U + 1) hU
  rw [hA]
  nlinarith [hB]

lemma sum_Icc_sub_succ (f : ℕ → ℝ) {L U : ℕ} (hLU : L ≤ U) :
    (∑ d ∈ Finset.Icc L U, (f d - f (d + 1))) = f L - f (U + 1) := by
  rw [← Finset.Ico_add_one_right_eq_Icc L U]
  exact sum_Ico_sub_succ f hLU

lemma clebschGordan_two_mul_sin_of_le {p a b j : ℕ} (hab : a ≤ b) :
    2 * sinOdd p a j * sinOdd p b j =
      ∑ d ∈ Finset.Icc (b - a) (a + b), 2 * sinOdd p d j * sinOdd p 0 j := by
  have hleft := two_sinOdd_mul_sinOdd_eq_cos_sub_of_ge (p := p) (r := a) (s := b) (j := j) hab
  have hright :
      (∑ d ∈ Finset.Icc (b - a) (a + b), 2 * sinOdd p d j * sinOdd p 0 j) =
        ∑ d ∈ Finset.Icc (b - a) (a + b), (cosMode p d j - cosMode p (d + 1) j) := by
    refine Finset.sum_congr rfl ?_
    intro d _hd
    have h := two_sinOdd_mul_sinOdd_eq_cos_sub_of_le (p := p) (r := d) (s := 0) (j := j)
      (Nat.zero_le d)
    simpa using h
  rw [hright]
  have htel := sum_Icc_sub_succ (fun d => cosMode p d j) (L := b - a) (U := a + b) (by omega)
  rw [htel]
  have hupper : a + b + 1 = (a + b) + 1 := by omega
  rw [← hupper]
  exact hleft

lemma clebschGordan_two_mul_sin_of_ge {p a b j : ℕ} (hba : b ≤ a) :
    2 * sinOdd p a j * sinOdd p b j =
      ∑ d ∈ Finset.Icc (a - b) (a + b), 2 * sinOdd p d j * sinOdd p 0 j := by
  have h := clebschGordan_two_mul_sin_of_le (p := p) (a := b) (b := a) (j := j) hba
  rw [add_comm b a] at h
  nlinarith [h]

lemma sinOdd_zero (p j : ℕ) : sinOdd p 0 j = sin (theta p j) := by
  simp [sinOdd]

/--
The divided Clebsch-Gordan identity.

This is the exact form needed inside the Verlinde kernel: after dividing by
`sin(theta)`, the product of the `a` and `b` sine modes becomes a sum over the
intermediate labels `d`.
-/
lemma clebschGordan_div_of_le {p a b j : ℕ} (hp : 0 < p) (hj1 : 1 ≤ j)
    (hjp : j ≤ p - 1) (hab : a ≤ b) :
    sinOdd p a j * sinOdd p b j / sin (theta p j) =
      ∑ d ∈ Finset.Icc (b - a) (a + b), sinOdd p d j := by
  let S := ∑ d ∈ Finset.Icc (b - a) (a + b), sinOdd p d j
  have hne : sin (theta p j) ≠ 0 := sin_theta_ne_zero hp hj1 hjp
  have htwo := clebschGordan_two_mul_sin_of_le (p := p) (a := a) (b := b) (j := j) hab
  have hsum :
      (∑ d ∈ Finset.Icc (b - a) (a + b), 2 * sinOdd p d j * sinOdd p 0 j) =
        2 * sin (theta p j) * S := by
    dsimp [S]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro d _hd
    rw [sinOdd_zero]
    ring
  have hmain : sinOdd p a j * sinOdd p b j = sin (theta p j) * S := by
    rw [hsum] at htwo
    nlinarith [htwo]
  rw [hmain]
  field_simp [hne]
  dsimp [S]

/-- The same divided Clebsch-Gordan identity, with `a` and `b` ordered the other way. -/
lemma clebschGordan_div_of_ge {p a b j : ℕ} (hp : 0 < p) (hj1 : 1 ≤ j)
    (hjp : j ≤ p - 1) (hba : b ≤ a) :
    sinOdd p a j * sinOdd p b j / sin (theta p j) =
      ∑ d ∈ Finset.Icc (a - b) (a + b), sinOdd p d j := by
  let S := ∑ d ∈ Finset.Icc (a - b) (a + b), sinOdd p d j
  have hne : sin (theta p j) ≠ 0 := sin_theta_ne_zero hp hj1 hjp
  have htwo := clebschGordan_two_mul_sin_of_ge (p := p) (a := a) (b := b) (j := j) hba
  have hsum :
      (∑ d ∈ Finset.Icc (a - b) (a + b), 2 * sinOdd p d j * sinOdd p 0 j) =
        2 * sin (theta p j) * S := by
    dsimp [S]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro d _hd
    rw [sinOdd_zero]
    ring
  have hmain : sinOdd p a j * sinOdd p b j = sin (theta p j) * S := by
    rw [hsum] at htwo
    nlinarith [htwo]
  rw [hmain]
  field_simp [hne]
  dsimp [S]

/--
An alternating sum over an interval of odd length.

The interval `[L,L+2n]` has `2n+1` terms, so all signs cancel in adjacent pairs
except the first one.
-/
lemma sum_neg_one_pow_Icc_even_length (L n c : ℕ) :
    (∑ d ∈ Finset.Icc L (L + 2 * n), ((-1 : ℝ) ^ (d + c))) =
      (-1 : ℝ) ^ (L + c) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      let U := L + 2 * n
      have htop : L + 2 * Nat.succ n = (U + 1) + 1 := by
        dsimp [U]
        omega
      rw [htop]
      rw [Finset.sum_Icc_succ_top (by omega)]
      rw [Finset.sum_Icc_succ_top (by omega)]
      change (∑ d ∈ Finset.Icc L (L + 2 * n), (-1 : ℝ) ^ (d + c)) +
          (-1 : ℝ) ^ (U + 1 + c) + (-1 : ℝ) ^ ((U + 1) + 1 + c) =
        (-1 : ℝ) ^ (L + c)
      rw [ih]
      have hpair :
          (-1 : ℝ) ^ (U + 1 + c) + (-1 : ℝ) ^ ((U + 1) + 1 + c) = 0 := by
        rw [show (U + 1) + 1 + c = (U + 1 + c) + 1 by omega, pow_succ]
        ring
      nlinarith

lemma neg_one_pow_add_even (m n : ℕ) :
    ((-1 : ℝ) ^ (m + 2 * n)) = (-1 : ℝ) ^ m := by
  rw [pow_add]
  have htwo : ((-1 : ℝ) ^ (2 * n)) = 1 := by
    rw [show 2 * n = n + n by omega]
    exact neg_one_pow_add_self n
  rw [htwo, mul_one]

lemma sum_neg_one_pow_interval_of_le {a b c : ℕ} (hab : a ≤ b) :
    (∑ d ∈ Finset.Icc (b - a) (a + b), ((-1 : ℝ) ^ (d + c))) =
      (-1 : ℝ) ^ (a + b + c) := by
  have htop : a + b = (b - a) + 2 * a := by omega
  rw [htop]
  have h := sum_neg_one_pow_Icc_even_length (L := b - a) (n := a) (c := c)
  rw [h]
  rw [show b - a + 2 * a + c = (b - a + c) + 2 * a by omega]
  exact (neg_one_pow_add_even (b - a + c) a).symm

lemma sum_neg_one_pow_interval_of_ge {a b c : ℕ} (hba : b ≤ a) :
    (∑ d ∈ Finset.Icc (a - b) (a + b), ((-1 : ℝ) ^ (d + c))) =
      (-1 : ℝ) ^ (a + b + c) := by
  have htop : a + b = (a - b) + 2 * b := by omega
  rw [htop]
  have h := sum_neg_one_pow_Icc_even_length (L := a - b) (n := b) (c := c)
  rw [h]
  rw [show a - b + 2 * b + c = (a - b + c) + 2 * b by omega]
  exact (neg_one_pow_add_even (a - b + c) b).symm

/-!
## Rewriting the Verlinde kernel

Using the divided Clebsch-Gordan identity, the three-sine expression in
`verlindeKernel` becomes a sum over intermediate labels `d`.  After swapping
the two finite sums, each `d`-summand is exactly `sineKernel p d c`.
-/

lemma sum_sineKernel_expand (p c : ℕ) (D : Finset ℕ) :
    (∑ d ∈ D, sineKernel p d c) =
      (2 / (p : ℝ)) *
        (∑ d ∈ D, ∑ j ∈ Finset.Icc 1 (p - 1), sinOdd p d j * sinOdd p c j) +
      (∑ d ∈ D, ((-1 : ℝ) ^ (d + c))) / (p : ℝ) := by
  unfold sineKernel
  rw [Finset.sum_add_distrib]
  rw [Finset.mul_sum]
  rw [Finset.sum_div]

lemma verlindeKernel_eq_sum_sineKernel_of_le {p a b c : ℕ} (hp : 0 < p) (hab : a ≤ b) :
    verlindeKernel p a b c =
      ∑ d ∈ Finset.Icc (b - a) (a + b), sineKernel p d c := by
  let D := Finset.Icc (b - a) (a + b)
  have hsumj :
      (∑ j ∈ Finset.Icc 1 (p - 1),
        sinOdd p a j * sinOdd p b j * sinOdd p c j / sin (theta p j)) =
      (∑ d ∈ D, ∑ j ∈ Finset.Icc 1 (p - 1), sinOdd p d j * sinOdd p c j) := by
    calc
      (∑ j ∈ Finset.Icc 1 (p - 1),
        sinOdd p a j * sinOdd p b j * sinOdd p c j / sin (theta p j))
          = ∑ j ∈ Finset.Icc 1 (p - 1),
              ∑ d ∈ D, sinOdd p d j * sinOdd p c j := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
            have hjp : j ≤ p - 1 := (Finset.mem_Icc.mp hj).2
            have hcg := clebschGordan_div_of_le
              (p := p) (a := a) (b := b) (j := j) hp hj1 hjp hab
            calc
              sinOdd p a j * sinOdd p b j * sinOdd p c j / sin (theta p j)
                  = (sinOdd p a j * sinOdd p b j / sin (theta p j)) *
                      sinOdd p c j := by ring
              _ = (∑ d ∈ D, sinOdd p d j) * sinOdd p c j := by
                    rw [hcg]
              _ = ∑ d ∈ D, sinOdd p d j * sinOdd p c j := by
                    rw [Finset.sum_mul]
      _ = ∑ d ∈ D, ∑ j ∈ Finset.Icc 1 (p - 1), sinOdd p d j * sinOdd p c j := by
            rw [Finset.sum_comm]
  unfold verlindeKernel
  change (2 / (p : ℝ)) *
      (∑ j ∈ Finset.Icc 1 (p - 1),
        sinOdd p a j * sinOdd p b j * sinOdd p c j / sin (theta p j)) +
      (-1 : ℝ) ^ (a + b + c) / (p : ℝ) =
    ∑ d ∈ D, sineKernel p d c
  rw [hsumj]
  have hend := sum_neg_one_pow_interval_of_le (a := a) (b := b) (c := c) hab
  change (2 / (p : ℝ)) *
      (∑ d ∈ D, ∑ j ∈ Finset.Icc 1 (p - 1), sinOdd p d j * sinOdd p c j) +
      (-1 : ℝ) ^ (a + b + c) / (p : ℝ) =
    ∑ d ∈ D, sineKernel p d c
  rw [← hend]
  rw [sum_sineKernel_expand]

lemma verlindeKernel_eq_sum_sineKernel_of_ge {p a b c : ℕ} (hp : 0 < p) (hba : b ≤ a) :
    verlindeKernel p a b c =
      ∑ d ∈ Finset.Icc (a - b) (a + b), sineKernel p d c := by
  let D := Finset.Icc (a - b) (a + b)
  have hsumj :
      (∑ j ∈ Finset.Icc 1 (p - 1),
        sinOdd p a j * sinOdd p b j * sinOdd p c j / sin (theta p j)) =
      (∑ d ∈ D, ∑ j ∈ Finset.Icc 1 (p - 1), sinOdd p d j * sinOdd p c j) := by
    calc
      (∑ j ∈ Finset.Icc 1 (p - 1),
        sinOdd p a j * sinOdd p b j * sinOdd p c j / sin (theta p j))
          = ∑ j ∈ Finset.Icc 1 (p - 1),
              ∑ d ∈ D, sinOdd p d j * sinOdd p c j := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
            have hjp : j ≤ p - 1 := (Finset.mem_Icc.mp hj).2
            have hcg := clebschGordan_div_of_ge
              (p := p) (a := a) (b := b) (j := j) hp hj1 hjp hba
            calc
              sinOdd p a j * sinOdd p b j * sinOdd p c j / sin (theta p j)
                  = (sinOdd p a j * sinOdd p b j / sin (theta p j)) *
                      sinOdd p c j := by ring
              _ = (∑ d ∈ D, sinOdd p d j) * sinOdd p c j := by
                    rw [hcg]
              _ = ∑ d ∈ D, sinOdd p d j * sinOdd p c j := by
                    rw [Finset.sum_mul]
      _ = ∑ d ∈ D, ∑ j ∈ Finset.Icc 1 (p - 1), sinOdd p d j * sinOdd p c j := by
            rw [Finset.sum_comm]
  unfold verlindeKernel
  change (2 / (p : ℝ)) *
      (∑ j ∈ Finset.Icc 1 (p - 1),
        sinOdd p a j * sinOdd p b j * sinOdd p c j / sin (theta p j)) +
      (-1 : ℝ) ^ (a + b + c) / (p : ℝ) =
    ∑ d ∈ D, sineKernel p d c
  rw [hsumj]
  have hend := sum_neg_one_pow_interval_of_ge (a := a) (b := b) (c := c) hba
  change (2 / (p : ℝ)) *
      (∑ d ∈ D, ∑ j ∈ Finset.Icc 1 (p - 1), sinOdd p d j * sinOdd p c j) +
      (-1 : ℝ) ^ (a + b + c) / (p : ℝ) =
    ∑ d ∈ D, sineKernel p d c
  rw [← hend]
  rw [sum_sineKernel_expand]

/-!
## Collapsing the interval sum

The final step is arithmetic.  Orthogonality says that summing `sineKernel p d c`
over the interval `[|a-b|,a+b]` counts the label `d=c` with weight `1` and the
reflected label `d=2p-1-c` with weight `-1`.

Membership of `c` in the interval is exactly the two triangle inequalities
involving `c`.  If `c` is in the interval but the upper bound
`a+b+c+2 ≤ 2p` fails, then the reflected label is also in the interval, and
the two contributions cancel.
-/

lemma sum_sineKernel_interval_eq_fusion_of_le {p a b c : ℕ} (hp : 1 < p)
    (_ha : a < p) (hb : b < p) (hc : c < p) (hab : a ≤ b) :
    (∑ d ∈ Finset.Icc (b - a) (a + b), sineKernel p d c) = fusionN p a b c := by
  classical
  let D := Finset.Icc (b - a) (a + b)
  let r := 2 * p - 1 - c
  have hcr : c ≠ r := by
    dsimp [r]
    omega
  have hsumOrth :
      (∑ d ∈ D, sineKernel p d c) =
        ∑ d ∈ D, (if d = c then (1 : ℝ) else if d = r then -1 else 0) := by
    refine Finset.sum_congr rfl ?_
    intro d hd
    have hdle : d ≤ 2 * p - 2 := by
      have hdU : d ≤ a + b := (Finset.mem_Icc.mp hd).2
      omega
    have horth := sineKernel_orthogonality (p := p) (r := d) (s := c) hp hdle hc
    have href : (d + c + 1 = 2 * p) ↔ d = r := by
      dsimp [r]
      omega
    rw [horth]
    by_cases hdc : d = c
    · simp [hdc]
    · simp [hdc, href]
  have hsplit :
      (∑ d ∈ D, (if d = c then (1 : ℝ) else if d = r then -1 else 0)) =
        (∑ d ∈ D, (if d = c then (1 : ℝ) else 0)) +
          (∑ d ∈ D, (if d = r then (-1 : ℝ) else 0)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro d _hd
    by_cases hdc : d = c
    · subst d
      simp [hcr]
    · by_cases hdr : d = r
      · simp [hdr, hcr.symm]
      · simp [hdc, hdr]
  rw [hsumOrth, hsplit]
  rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
  unfold fusionN
  by_cases hC : C1Even p a b c
  · have hcD : c ∈ D := by
      dsimp [D]
      rw [Finset.mem_Icc]
      unfold C1Even at hC
      omega
    have hrNot : r ∉ D := by
      intro hrD
      dsimp [D, r] at hrD
      rw [Finset.mem_Icc] at hrD
      unfold C1Even at hC
      omega
    simp [hC, hcD, hrNot]
  · by_cases hcD : c ∈ D
    · have hrD : r ∈ D := by
        dsimp [D, r] at hcD ⊢
        rw [Finset.mem_Icc] at hcD ⊢
        have hnotupper : ¬ a + b + c + 2 ≤ 2 * p := by
          intro hupper
          apply hC
          unfold C1Even
          omega
        omega
      simp [hC, hcD, hrD]
    · have hrNot : r ∉ D := by
        intro hrD
        apply hcD
        dsimp [D, r] at hrD ⊢
        rw [Finset.mem_Icc] at hrD ⊢
        omega
      simp [hC, hcD, hrNot]

lemma sum_sineKernel_interval_eq_fusion_of_ge {p a b c : ℕ} (hp : 1 < p)
    (ha : a < p) (hb : b < p) (hc : c < p) (hba : b ≤ a) :
    (∑ d ∈ Finset.Icc (a - b) (a + b), sineKernel p d c) = fusionN p a b c := by
  classical
  let D := Finset.Icc (a - b) (a + b)
  let r := 2 * p - 1 - c
  have hcr : c ≠ r := by
    dsimp [r]
    omega
  have hsumOrth :
      (∑ d ∈ D, sineKernel p d c) =
        ∑ d ∈ D, (if d = c then (1 : ℝ) else if d = r then -1 else 0) := by
    refine Finset.sum_congr rfl ?_
    intro d hd
    have hdle : d ≤ 2 * p - 2 := by
      have hdU : d ≤ a + b := (Finset.mem_Icc.mp hd).2
      omega
    have horth := sineKernel_orthogonality (p := p) (r := d) (s := c) hp hdle hc
    have href : (d + c + 1 = 2 * p) ↔ d = r := by
      dsimp [r]
      omega
    rw [horth]
    by_cases hdc : d = c
    · simp [hdc]
    · simp [hdc, href]
  have hsplit :
      (∑ d ∈ D, (if d = c then (1 : ℝ) else if d = r then -1 else 0)) =
        (∑ d ∈ D, (if d = c then (1 : ℝ) else 0)) +
          (∑ d ∈ D, (if d = r then (-1 : ℝ) else 0)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro d _hd
    by_cases hdc : d = c
    · subst d
      simp [hcr]
    · by_cases hdr : d = r
      · simp [hdr, hcr.symm]
      · simp [hdc, hdr]
  rw [hsumOrth, hsplit]
  rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
  unfold fusionN
  by_cases hC : C1Even p a b c
  · have hcD : c ∈ D := by
      dsimp [D]
      rw [Finset.mem_Icc]
      unfold C1Even at hC
      omega
    have hrNot : r ∉ D := by
      intro hrD
      dsimp [D, r] at hrD
      rw [Finset.mem_Icc] at hrD
      unfold C1Even at hC
      omega
    simp [hC, hcD, hrNot]
  · by_cases hcD : c ∈ D
    · have hrD : r ∈ D := by
        dsimp [D, r] at hcD ⊢
        rw [Finset.mem_Icc] at hcD ⊢
        have hnotupper : ¬ a + b + c + 2 ≤ 2 * p := by
          intro hupper
          apply hC
          unfold C1Even
          omega
        omega
      simp [hC, hcD, hrD]
    · have hrNot : r ∉ D := by
        intro hrD
        apply hcD
        dsimp [D, r] at hrD ⊢
        rw [Finset.mem_Icc] at hrD ⊢
        omega
      simp [hC, hcD, hrNot]

/-!
## The finite Verlinde identity

The theorem below combines the two rewritings:
`verlindeKernel` is a sum of orthogonality kernels, and that sum is exactly
the indicator function `fusionN`.
-/

theorem finiteVerlindeKernelIdentity_of_one_lt {p a b c : ℕ} (hp : 1 < p)
    (ha : a < p) (hb : b < p) (hc : c < p) :
    fusionN p a b c = verlindeKernel p a b c := by
  symm
  rcases le_total a b with hab | hba
  · calc
      verlindeKernel p a b c =
          ∑ d ∈ Finset.Icc (b - a) (a + b), sineKernel p d c :=
            verlindeKernel_eq_sum_sineKernel_of_le (p := p) (a := a) (b := b) (c := c)
              (by omega) hab
      _ = fusionN p a b c :=
            sum_sineKernel_interval_eq_fusion_of_le (p := p) (a := a) (b := b) (c := c)
              hp ha hb hc hab
  · calc
      verlindeKernel p a b c =
          ∑ d ∈ Finset.Icc (a - b) (a + b), sineKernel p d c :=
            verlindeKernel_eq_sum_sineKernel_of_ge (p := p) (a := a) (b := b) (c := c)
              (by omega) hba
      _ = fusionN p a b c :=
            sum_sineKernel_interval_eq_fusion_of_ge (p := p) (a := a) (b := b) (c := c)
              hp ha hb hc hba

/--
The square-root-free finite Verlinde identity.

This proves the proposition `finiteVerlindeKernelIdentity`: for labels
`a,b,c < p`, the trigonometric kernel `verlindeKernel` is equal to the
admissibility coefficient `fusionN`.
-/
theorem finiteVerlindeKernelIdentity_proved (p a b c : ℕ) :
    finiteVerlindeKernelIdentity p a b c := by
  intro hp ha hb hc
  by_cases hp1 : 1 < p
  · exact finiteVerlindeKernelIdentity_of_one_lt hp1 ha hb hc
  · have hp_eq : p = 1 := by omega
    subst p
    have ha0 : a = 0 := by omega
    have hb0 : b = 0 := by omega
    have hc0 : c = 0 := by omega
    subst a
    subst b
    subst c
    simp [fusionN, verlindeKernel, C1Even]

/-- The universal wrapper around `finiteVerlindeKernelIdentity_proved`. -/
theorem finiteVerlindeKernelTheorem_proved : finiteVerlindeKernelTheorem := by
  intro p a b c
  exact finiteVerlindeKernelIdentity_proved p a b c

end VerschiebungLean
