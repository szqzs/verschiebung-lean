import VerschiebungLean.Defs

set_option linter.style.header false

namespace VerschiebungLean

/-!
# Local factorization for admissible triples

This file proves the local, three-coordinate factorization statement.

An element of `C P N` is a triple of natural numbers satisfying two kinds of
conditions.  First, it satisfies the four triangle-type upper inequalities in
`Upper (P^N)`.  Second, at every lower level `M < N`, its residues modulo
`P^M`, after allowing the folded replacement `r ↦ P^M - 1 - r`, again contain
an admissible triple.

The map `Phi` combines two pieces of data in one coordinate: a level-one label
`n`, and a lower-level label `b`.  If `n` is even, `b` is placed in the lower
`P^(N-1)`-block; if `n` is odd, the folded complement of `b` is placed there.
The maps `SplitN` and `SplitB` recover these two pieces by looking at the
quotient and the folded remainder modulo `P^(N-1)`.

The main results are:

* `local_forward`: admissible `n` and `b` combine to an admissible triple.
* `local_split_mem`: an admissible triple splits into admissible `n` and `b`.
* `localFactorization`: these two constructions are inverse bijections.

The proof is elementary arithmetic.  The lower-level residue conditions are
handled by divisibility of powers of `P`; the upper inequalities are checked
after rewriting them in the odd form `2a_i + 1`.
-/

/-- The first component of the edgewise inverse to `Phi` on admissible labels. -/
def SplitN (P N A : ℕ) : ℕ :=
  let Q := P^(N - 1)
  let r := A % Q
  let q := A / Q
  if r ≤ (Q - 3) / 2 then 2 * q else 2 * q + 1

/-- The second component of the edgewise inverse to `Phi` on admissible labels. -/
def SplitB (P N A : ℕ) : ℕ :=
  let Q := P^(N - 1)
  let r := A % Q
  if r ≤ (Q - 3) / 2 then r else Q - 1 - r

/-- The same one-coordinate split as `SplitN`, with `Q = P^(N-1)` exposed. -/
def SplitNQ (Q A : ℕ) : ℕ :=
  let r := A % Q
  let q := A / Q
  if r ≤ (Q - 3) / 2 then 2 * q else 2 * q + 1

/-- The same one-coordinate split as `SplitB`, with `Q = P^(N-1)` exposed. -/
def SplitBQ (Q A : ℕ) : ℕ :=
  let r := A % Q
  if r ≤ (Q - 3) / 2 then r else Q - 1 - r

/-- The same one-coordinate map as `Phi`, with `Q = P^(N-1)` exposed. -/
def PhiQ (Q n b : ℕ) : ℕ :=
  if n % 2 = 0 then
    (n / 2) * Q + b
  else
    ((n + 1) / 2) * Q - 1 - b

lemma upper_two_mul_coord_add_two_le {L : ℕ} {a : Triple} (ha : Upper L a) (i : Fin 3) :
    2 * a i + 2 ≤ L := by
  fin_cases i <;> simp [Upper] at ha ⊢ <;> omega

/-- The four upper inequalities rewritten in the odd variables `2a_i + 1`. -/
def UpperOdd (L : ℕ) (a : Triple) : Prop :=
  (2 * a 0 + 1) + (2 * a 1 + 1) + (2 * a 2 + 1) < 2 * L ∧
  2 * a 0 + 1 < (2 * a 1 + 1) + (2 * a 2 + 1) ∧
  2 * a 1 + 1 < (2 * a 0 + 1) + (2 * a 2 + 1) ∧
  2 * a 2 + 1 < (2 * a 0 + 1) + (2 * a 1 + 1)

lemma upper_iff_upperOdd {L : ℕ} {a : Triple} : Upper L a ↔ UpperOdd L a := by
  simp [Upper, UpperOdd]
  constructor <;> intro h <;> omega

lemma odd_pow_mod_two {P N : ℕ} (hOdd : P % 2 = 1) : P^N % 2 = 1 := by
  induction N with
  | zero =>
      simp
  | succ N ih =>
      rw [pow_succ]
      simp [Nat.mul_mod, hOdd, ih]

lemma half_bound_of_two_mul_add_two_le {x Q : ℕ} (hQodd : Q % 2 = 1)
    (h : 2 * x + 2 ≤ Q) :
    x ≤ (Q - 3) / 2 := by
  have hQ : Q = 2 * (Q / 2) + 1 := by
    calc
      Q = 2 * (Q / 2) + Q % 2 := (Nat.div_add_mod Q 2).symm
      _ = 2 * (Q / 2) + 1 := by rw [hQodd]
  omega

lemma even_id_of_mod_two_eq_zero {n : ℕ} (h : n % 2 = 0) :
    2 * (n / 2) = n := by
  have hdiv := Nat.div_add_mod n 2
  omega

lemma odd_mod_of_not_even {n : ℕ} (h : n % 2 ≠ 0) : n % 2 = 1 := by
  have h01 := Nat.mod_two_eq_zero_or_one n
  omega

lemma odd_id_of_mod_two_eq_one {n : ℕ} (h : n % 2 = 1) :
    2 * (n / 2) + 1 = n := by
  have hdiv := Nat.div_add_mod n 2
  omega

lemma odd_half_of_mod_two_eq_one {n : ℕ} (h : n % 2 = 1) :
    (n + 1) / 2 = n / 2 + 1 := by
  have hn : n = 2 * (n / 2) + 1 := by
    have hdiv := Nat.div_add_mod n 2
    omega
  rw [hn]
  omega

lemma odd_branch_rewrite {c Q b : ℕ} (hc : 1 ≤ c) (hb : b < Q) :
    c * Q - 1 - b = (c - 1) * Q + (Q - 1 - b) := by
  have hc' : c = (c - 1) + 1 := by omega
  have h1 : c * Q = (c - 1) * Q + Q := by
    rw [hc']
    rw [Nat.add_mul]
    simp
  omega

lemma odd_branch_two_mul_add_one {q Q b : ℕ} (hQge : 3 ≤ Q)
    (hb : b ≤ (Q - 3) / 2) :
    2 * (q * Q + (Q - 1 - b)) + 1 =
      Q * (2 * q + 1) + (Q - (2 * b + 1)) := by
  apply Nat.add_right_cancel (m := 2 * b + 1)
  have hb2 : 2 * b + 1 ≤ Q := by omega
  have hsub2 : Q - (2 * b + 1) + (2 * b + 1) = Q := Nat.sub_add_cancel hb2
  have hsub1 : 2 * (Q - 1 - b) + 1 + (2 * b + 1) = 2 * Q := by omega
  nlinarith

lemma two_phiQ_add_one_even {Q n b : ℕ} (he : n % 2 = 0) :
    2 * PhiQ Q n b + 1 = Q * n + (2 * b + 1) := by
  unfold PhiQ
  rw [he]
  simp
  have hn : 2 * (n / 2) = n := even_id_of_mod_two_eq_zero he
  nlinarith

lemma two_phiQ_add_one_odd {Q n b : ℕ} (hQge : 3 ≤ Q)
    (hb : b ≤ (Q - 3) / 2) (ho : n % 2 ≠ 0) :
    2 * PhiQ Q n b + 1 = Q * n + (Q - (2 * b + 1)) := by
  unfold PhiQ
  have hmod1 : n % 2 = 1 := odd_mod_of_not_even ho
  rw [if_neg ho]
  have hhalf : (n + 1) / 2 = n / 2 + 1 := odd_half_of_mod_two_eq_one hmod1
  have hn : n = 2 * (n / 2) + 1 := by
    have h' := odd_id_of_mod_two_eq_one hmod1
    omega
  have hbQ' : b < Q := by omega
  have hbrewrite :
      ((n + 1) / 2) * Q - 1 - b = (n / 2) * Q + (Q - 1 - b) := by
    rw [hhalf]
    have hc : 1 ≤ n / 2 + 1 := by omega
    simpa using (odd_branch_rewrite (c := n / 2 + 1) (Q := Q) (b := b) hc hbQ')
  rw [hbrewrite]
  calc
    2 * (n / 2 * Q + (Q - 1 - b)) + 1
        = Q * (2 * (n / 2) + 1) + (Q - (2 * b + 1)) :=
          odd_branch_two_mul_add_one (q := n / 2) (Q := Q) (b := b) hQge hb
    _ = Q * n + (Q - (2 * b + 1)) := by rw [← hn]

lemma split_phiQ_even {Q n b : ℕ} (hQ : 0 < Q) (hb : b ≤ (Q - 3) / 2)
    (he : n % 2 = 0) :
    SplitNQ Q (PhiQ Q n b) = n ∧ SplitBQ Q (PhiQ Q n b) = b := by
  have hbQ : b < Q := by omega
  have hbdiv : b / Q = 0 := Nat.div_eq_of_lt hbQ
  have hbmod : b % Q = b := Nat.mod_eq_of_lt hbQ
  have hmod : ((n / 2) * Q + b) % Q = b := by
    rw [Nat.mul_add_mod_self_right]
    exact hbmod
  have hdiv : ((n / 2) * Q + b) / Q = n / 2 := by
    rw [mul_comm (n / 2) Q]
    rw [Nat.mul_add_div hQ]
    rw [hbdiv]
    omega
  constructor
  · simp [SplitNQ, PhiQ, he, hmod, hdiv, hb, even_id_of_mod_two_eq_zero he]
  · simp [SplitBQ, PhiQ, he, hmod, hb]

lemma split_phiQ_odd {Q n b : ℕ} (hQpos : 0 < Q) (hQge : 3 ≤ Q)
    (hb : b ≤ (Q - 3) / 2) (ho : n % 2 ≠ 0) :
    SplitNQ Q (PhiQ Q n b) = n ∧ SplitBQ Q (PhiQ Q n b) = b := by
  have hmod1 : n % 2 = 1 := odd_mod_of_not_even ho
  have hbQ : b < Q := by omega
  have hrQ : Q - 1 - b < Q := by omega
  have hrdiv : (Q - 1 - b) / Q = 0 := Nat.div_eq_of_lt hrQ
  have hrmod : (Q - 1 - b) % Q = Q - 1 - b := Nat.mod_eq_of_lt hrQ
  have hhalf : (n + 1) / 2 = n / 2 + 1 := odd_half_of_mod_two_eq_one hmod1
  have hA : ((n + 1) / 2) * Q - 1 - b = (n / 2) * Q + (Q - 1 - b) := by
    rw [hhalf]
    have hc : 1 ≤ n / 2 + 1 := by omega
    simpa using (odd_branch_rewrite (c := n / 2 + 1) (Q := Q) (b := b) hc hbQ)
  have hrem_gt : ¬ Q - 1 - b ≤ (Q - 3) / 2 := by omega
  have hmod : (((n + 1) / 2) * Q - 1 - b) % Q = Q - 1 - b := by
    rw [hA]
    rw [Nat.mul_add_mod_self_right]
    exact hrmod
  have hdiv : (((n + 1) / 2) * Q - 1 - b) / Q = n / 2 := by
    rw [hA]
    rw [mul_comm (n / 2) Q]
    rw [Nat.mul_add_div hQpos]
    rw [hrdiv]
    omega
  constructor
  · simp [SplitNQ, PhiQ, ho, hmod, hdiv, hrem_gt, odd_id_of_mod_two_eq_one hmod1]
  · simp [SplitBQ, PhiQ, ho, hmod, hrem_gt]
    omega

lemma phiQ_split {Q A : ℕ} (hQ : 0 < Q) :
    PhiQ Q (SplitNQ Q A) (SplitBQ Q A) = A := by
  unfold SplitNQ SplitBQ PhiQ
  by_cases h : A % Q ≤ (Q - 3) / 2
  · simp [h]
    rw [mul_comm (A / Q) Q]
    exact Nat.div_add_mod A Q
  · simp [h]
    have hhalf : (2 * (A / Q) + 1 + 1) / 2 = A / Q + 1 := by omega
    rw [hhalf]
    have hrlt : A % Q < Q := Nat.mod_lt A hQ
    have hrew :
        (A / Q + 1) * Q - 1 - (Q - 1 - A % Q) = (A / Q) * Q + A % Q := by
      have h1 : (A / Q + 1) * Q = (A / Q) * Q + Q := by
        rw [Nat.add_mul]
        simp
      omega
    rw [hrew]
    rw [mul_comm (A / Q) Q]
    exact Nat.div_add_mod A Q

lemma mod_complement_of_dvd {R Q b : ℕ} (hR : 0 < R) (hdvd : R ∣ Q) (hb : b < Q) :
    (Q - 1 - b) % R = R - 1 - b % R := by
  rcases hdvd with ⟨d, rfl⟩
  have hbdiv : b / R < d := Nat.div_lt_of_lt_mul hb
  have hbdecomp : b = R * (b / R) + b % R := (Nat.div_add_mod b R).symm
  have hrem : b % R < R := Nat.mod_lt b hR
  have hleq : b / R + 1 ≤ d := by omega
  have hmul : R * d = R * (b / R) + R * (d - b / R) := by
    rw [← Nat.mul_add]
    have : b / R + (d - b / R) = d := by omega
    rw [this]
  have hmul2 : R * (d - b / R) = R * (d - b / R - 1) + R := by
    have hdd : d - b / R = (d - b / R - 1) + 1 := by omega
    rw [hdd]
    rw [Nat.mul_add]
    simp
  have hrewrite : R * d - 1 - b = R * (d - b / R - 1) + (R - 1 - b % R) := by
    conv_lhs => rw [hbdecomp, hmul, hmul2]
    omega
  rw [hrewrite]
  rw [Nat.mul_add_mod_self_left]
  exact Nat.mod_eq_of_lt (by omega)

lemma phiQ_mod_low_even {R Q n b : ℕ} (hdvd : R ∣ Q) (he : n % 2 = 0) :
    PhiQ Q n b % R = b % R := by
  unfold PhiQ
  rw [he]
  have hQmod : Q % R = 0 := Nat.mod_eq_zero_of_dvd hdvd
  simp [Nat.add_mod, Nat.mul_mod, hQmod]

lemma phiQ_mod_low_odd {R Q n b : ℕ} (hR : 0 < R) (hdvd : R ∣ Q) (hb : b < Q)
    (ho : n % 2 ≠ 0) :
    PhiQ Q n b % R = R - 1 - b % R := by
  unfold PhiQ
  rw [if_neg ho]
  have hmod1 : n % 2 = 1 := odd_mod_of_not_even ho
  have hhalf : (n + 1) / 2 = n / 2 + 1 := odd_half_of_mod_two_eq_one hmod1
  have hrew : ((n + 1) / 2) * Q - 1 - b = (n / 2) * Q + (Q - 1 - b) := by
    rw [hhalf]
    have hc : 1 ≤ n / 2 + 1 := by omega
    simpa using odd_branch_rewrite (c := n / 2 + 1) (Q := Q) (b := b) hc hb
  rw [hrew]
  have hQmod : Q % R = 0 := Nat.mod_eq_zero_of_dvd hdvd
  rw [Nat.add_mod, Nat.mul_mod, hQmod]
  simp
  exact mod_complement_of_dvd hR hdvd hb

lemma foldChoice_transport_mod {R x b y : ℕ} (hR : 0 < R)
    (hx : x % R = b % R ∨ x % R = R - 1 - b % R)
    (hy : y = b % R ∨ y = R - 1 - b % R) :
    y = x % R ∨ y = R - 1 - x % R := by
  have hbR : b % R < R := Nat.mod_lt b hR
  rcases hx with hx | hx
  · rcases hy with hy | hy
    · left
      rw [hy, hx]
    · right
      rw [hy, hx]
  · have hcomp : R - 1 - (R - 1 - b % R) = b % R := by omega
    rcases hy with hy | hy
    · right
      rw [hy, hx, hcomp]
    · left
      rw [hy, hx]

lemma foldChoice_transport {P M x b y : ℕ} (hPM : 0 < P^M)
    (hx : x % P^M = b % P^M ∨ x % P^M = P^M - 1 - b % P^M)
    (hy : FoldChoice P M b y) :
    FoldChoice P M x y := by
  unfold FoldChoice at hy ⊢
  exact foldChoice_transport_mod hPM hx hy

lemma not_both_half_complement {Q r : ℕ} (hQge : 3 ≤ Q) (hr : r < Q)
    (hrhalf : r ≤ (Q - 3) / 2) (hchalf : Q - 1 - r ≤ (Q - 3) / 2) :
    False := by
  have h2r : r * 2 ≤ Q - 3 := (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mp hrhalf
  have h2c : (Q - 1 - r) * 2 ≤ Q - 3 :=
    (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mp hchalf
  have hrle : r ≤ Q - 1 := by omega
  have hsum : r + (Q - 1 - r) = Q - 1 := Nat.add_sub_of_le hrle
  have hsum2 : r * 2 + (Q - 1 - r) * 2 = (Q - 1) * 2 := by
    nlinarith only [hsum]
  have hQsub : Q - 3 + 3 = Q := Nat.sub_add_cancel hQge
  have hQsub1 : Q - 1 + 1 = Q := Nat.sub_add_cancel (by omega : 1 ≤ Q)
  nlinarith only [h2r, h2c, hsum2, hQsub, hQsub1]

lemma splitBQ_eq_of_foldChoice {Q A c : ℕ} (hQpos : 0 < Q) (hQge : 3 ≤ Q)
    (hcHalf : c ≤ (Q - 3) / 2)
    (hc : c = A % Q ∨ c = Q - 1 - A % Q) :
    SplitBQ Q A = c := by
  unfold SplitBQ
  rcases hc with hc | hc
  · rw [if_pos]
    · exact hc.symm
    · rwa [← hc]
  · rw [if_neg]
    · exact hc.symm
    · intro hrem
      have hrem_lt : A % Q < Q := Nat.mod_lt A hQpos
      exact not_both_half_complement hQge hrem_lt hrem (by simpa [hc] using hcHalf)

lemma top_fold_to_low {R Q A c : ℕ} (hR : 0 < R) (hQ : 0 < Q) (hdvd : R ∣ Q)
    (hc : c = A % Q ∨ c = Q - 1 - A % Q) :
    c % R = A % R ∨ c % R = R - 1 - A % R := by
  have hAQ : A % Q < Q := Nat.mod_lt A hQ
  have hmodAQ : (A % Q) % R = A % R := by
    exact Nat.ModEq.of_dvd hdvd (Nat.mod_modEq A Q)
  rcases hc with hc | hc
  · left
    rw [hc, hmodAQ]
  · right
    rw [hc]
    rw [mod_complement_of_dvd hR hdvd hAQ]
    rw [hmodAQ]

def Resid (Q n b : ℕ) : ℕ :=
  if n % 2 = 0 then 2 * b + 1 else Q - (2 * b + 1)

lemma two_phiQ_add_one_resid {Q n b : ℕ} (hQge : 3 ≤ Q)
    (hb : b ≤ (Q - 3) / 2) :
    2 * PhiQ Q n b + 1 = Q * n + Resid Q n b := by
  by_cases h : n % 2 = 0
  · simp [Resid, h, two_phiQ_add_one_even (Q := Q) (n := n) (b := b) h]
  · simp [Resid, h, two_phiQ_add_one_odd (Q := Q) (n := n) (b := b) hQge hb h]

set_option maxHeartbeats 2000000 in
-- The proof below is a finite parity split; each branch is elementary linear arithmetic.
lemma upper_forward_scalar
    (P Q n0 n1 n2 b0 b1 b2 : ℕ)
    (hQge : 3 ≤ Q)
    (hnsum : n0 + n1 + n2 + 2 ≤ 2 * P)
    (hn0 : n0 ≤ n1 + n2) (hn1 : n1 ≤ n0 + n2) (hn2 : n2 ≤ n0 + n1)
    (hbsum : b0 + b1 + b2 + 2 ≤ Q)
    (hb0 : b0 ≤ b1 + b2) (hb1 : b1 ≤ b0 + b2) (hb2 : b2 ≤ b0 + b1)
    (hb0half : b0 ≤ (Q - 3) / 2)
    (hb1half : b1 ≤ (Q - 3) / 2)
    (hb2half : b2 ≤ (Q - 3) / 2) :
    UpperOdd (P * Q)
      (fun i => match i with
        | 0 => PhiQ Q n0 b0
        | 1 => PhiQ Q n1 b1
        | 2 => PhiQ Q n2 b2) := by
  rw [UpperOdd]
  have e0 := two_phiQ_add_one_resid (Q := Q) (n := n0) (b := b0) hQge hb0half
  have e1 := two_phiQ_add_one_resid (Q := Q) (n := n1) (b := b1) hQge hb1half
  have e2 := two_phiQ_add_one_resid (Q := Q) (n := n2) (b := b2) hQge hb2half
  simp only [e0, e1, e2]
  have hb0Q : 2 * b0 + 1 ≤ Q := by omega
  have hb1Q : 2 * b1 + 1 ≤ Q := by omega
  have hb2Q : 2 * b2 + 1 ≤ Q := by omega
  have hsub0 : Q - (2 * b0 + 1) + (2 * b0 + 1) = Q := Nat.sub_add_cancel hb0Q
  have hsub1 : Q - (2 * b1 + 1) + (2 * b1 + 1) = Q := Nat.sub_add_cancel hb1Q
  have hsub2 : Q - (2 * b2 + 1) + (2 * b2 + 1) = Q := Nat.sub_add_cancel hb2Q
  have d0 := Nat.div_add_mod n0 2
  have d1 := Nat.div_add_mod n1 2
  have d2 := Nat.div_add_mod n2 2
  by_cases p0 : n0 % 2 = 0 <;> by_cases p1 : n1 % 2 = 0 <;> by_cases p2 : n2 % 2 = 0
  all_goals
    simp [Resid, p0, p1, p2]
    first
      | have ms : (n0 + n1 + n2 + 4) * Q ≤ (2 * P) * Q := Nat.mul_le_mul_right Q (by omega)
      | have ms : (n0 + n1 + n2 + 3) * Q ≤ (2 * P) * Q := Nat.mul_le_mul_right Q (by omega)
      | have ms : (n0 + n1 + n2 + 2) * Q ≤ (2 * P) * Q := Nat.mul_le_mul_right Q (by omega)
    first
      | have m0 : (n0 + 2) * Q ≤ (n1 + n2) * Q := Nat.mul_le_mul_right Q (by omega)
      | have m0 : (n0 + 1) * Q ≤ (n1 + n2) * Q := Nat.mul_le_mul_right Q (by omega)
      | have m0 : n0 * Q ≤ (n1 + n2) * Q := Nat.mul_le_mul_right Q (by omega)
    first
      | have m1 : (n1 + 2) * Q ≤ (n0 + n2) * Q := Nat.mul_le_mul_right Q (by omega)
      | have m1 : (n1 + 1) * Q ≤ (n0 + n2) * Q := Nat.mul_le_mul_right Q (by omega)
      | have m1 : n1 * Q ≤ (n0 + n2) * Q := Nat.mul_le_mul_right Q (by omega)
    first
      | have m2 : (n2 + 2) * Q ≤ (n0 + n1) * Q := Nat.mul_le_mul_right Q (by omega)
      | have m2 : (n2 + 1) * Q ≤ (n0 + n1) * Q := Nat.mul_le_mul_right Q (by omega)
      | have m2 : n2 * Q ≤ (n0 + n1) * Q := Nat.mul_le_mul_right Q (by omega)
    constructor
    · nlinarith only [ms, hbsum, hb0, hb1, hb2, hsub0, hsub1, hsub2]
    constructor
    · nlinarith only [m0, hbsum, hb0, hb1, hb2, hsub0, hsub1, hsub2]
    constructor
    · nlinarith only [m1, hbsum, hb0, hb1, hb2, hsub0, hsub1, hsub2]
    · nlinarith only [m2, hbsum, hb0, hb1, hb2, hsub0, hsub1, hsub2]

/--
The upper inequalities are preserved by the local forward construction.

Here `Q` should be thought of as `P^(N-1)`.  If `n` satisfies the level-one
upper inequalities at size `2 * P`, and `b` satisfies the lower-level upper
inequalities at size `Q`, then the triple obtained coordinatewise by `PhiQ`
satisfies the upper inequalities at size `P * Q`.
-/
theorem upper_forward
    (P Q : ℕ) (hQge : 3 ≤ Q) (hQodd : Q % 2 = 1)
    {n b : Triple} (hn : Upper (2 * P) n) (hb : Upper Q b) :
    Upper (P * Q) (fun i => PhiQ Q (n i) (b i)) := by
  rcases hn with ⟨hnsum, hn0, hn1, hn2⟩
  rcases hb with ⟨hbsum, hb0, hb1, hb2⟩
  apply upper_iff_upperOdd.mpr
  have hb0half : b 0 ≤ (Q - 3) / 2 :=
    half_bound_of_two_mul_add_two_le hQodd
      (by simpa [Upper] using
        (upper_two_mul_coord_add_two_le (L := Q)
          (a := b) ⟨hbsum, hb0, hb1, hb2⟩ 0))
  have hb1half : b 1 ≤ (Q - 3) / 2 :=
    half_bound_of_two_mul_add_two_le hQodd
      (by simpa [Upper] using
        (upper_two_mul_coord_add_two_le (L := Q)
          (a := b) ⟨hbsum, hb0, hb1, hb2⟩ 1))
  have hb2half : b 2 ≤ (Q - 3) / 2 :=
    half_bound_of_two_mul_add_two_le hQodd
      (by simpa [Upper] using
        (upper_two_mul_coord_add_two_le (L := Q)
          (a := b) ⟨hbsum, hb0, hb1, hb2⟩ 2))
  have h := upper_forward_scalar P Q (n 0) (n 1) (n 2) (b 0) (b 1) (b 2)
    hQge hnsum hn0 hn1 hn2 hbsum hb0 hb1 hb2 hb0half hb1half hb2half
  have hfun :
      (fun i : Fin 3 => match i with
        | 0 => PhiQ Q (n 0) (b 0)
        | 1 => PhiQ Q (n 1) (b 1)
        | 2 => PhiQ Q (n 2) (b 2)) =
      (fun i => PhiQ Q (n i) (b i)) := by
    funext i
    fin_cases i <;> rfl
  rwa [hfun] at h

set_option maxHeartbeats 2000000 in
-- The proof below is the inverse finite parity split for the four upper inequalities.
lemma upper_split_scalar
    (P Q n0 n1 n2 b0 b1 b2 : ℕ)
    (hQge : 3 ≤ Q)
    (ha : UpperOdd (P * Q)
      (fun i => match i with
        | 0 => PhiQ Q n0 b0
        | 1 => PhiQ Q n1 b1
        | 2 => PhiQ Q n2 b2))
    (hbsum : b0 + b1 + b2 + 2 ≤ Q)
    (hb0 : b0 ≤ b1 + b2) (hb1 : b1 ≤ b0 + b2) (hb2 : b2 ≤ b0 + b1)
    (hb0half : b0 ≤ (Q - 3) / 2)
    (hb1half : b1 ≤ (Q - 3) / 2)
    (hb2half : b2 ≤ (Q - 3) / 2) :
    Upper (2 * P)
      (fun i => match i with
        | 0 => n0
        | 1 => n1
        | 2 => n2) := by
  rw [Upper]
  rw [UpperOdd] at ha
  have e0 := two_phiQ_add_one_resid (Q := Q) (n := n0) (b := b0) hQge hb0half
  have e1 := two_phiQ_add_one_resid (Q := Q) (n := n1) (b := b1) hQge hb1half
  have e2 := two_phiQ_add_one_resid (Q := Q) (n := n2) (b := b2) hQge hb2half
  simp only [e0, e1, e2] at ha
  have hb0Q : 2 * b0 + 1 ≤ Q := by omega
  have hb1Q : 2 * b1 + 1 ≤ Q := by omega
  have hb2Q : 2 * b2 + 1 ≤ Q := by omega
  have hsub0 : Q - (2 * b0 + 1) + (2 * b0 + 1) = Q := Nat.sub_add_cancel hb0Q
  have hsub1 : Q - (2 * b1 + 1) + (2 * b1 + 1) = Q := Nat.sub_add_cancel hb1Q
  have hsub2 : Q - (2 * b2 + 1) + (2 * b2 + 1) = Q := Nat.sub_add_cancel hb2Q
  have d0 := Nat.div_add_mod n0 2
  have d1 := Nat.div_add_mod n1 2
  have d2 := Nat.div_add_mod n2 2
  by_cases p0 : n0 % 2 = 0 <;> by_cases p1 : n1 % 2 = 0 <;> by_cases p2 : n2 % 2 = 0
  all_goals
    simp [Resid, p0, p1, p2] at ha ⊢
    constructor
    · by_contra hfail
      first
        | have ms : (2 * P) * Q ≤ (n0 + n1 + n2) * Q := Nat.mul_le_mul_right Q (by omega)
        | have ms : (2 * P) * Q ≤ (n0 + n1 + n2 + 1) * Q := Nat.mul_le_mul_right Q (by omega)
      nlinarith only [ha.1, ms, hbsum, hb0, hb1, hb2, hsub0, hsub1, hsub2]
    constructor
    · by_contra hfail
      first
        | have m0 : (n1 + n2 + 2) * Q ≤ n0 * Q := Nat.mul_le_mul_right Q (by omega)
        | have m0 : (n1 + n2 + 1) * Q ≤ n0 * Q := Nat.mul_le_mul_right Q (by omega)
      nlinarith only [ha.2.1, m0, hbsum, hb0, hb1, hb2, hsub0, hsub1, hsub2]
    constructor
    · by_contra hfail
      first
        | have m1 : (n0 + n2 + 2) * Q ≤ n1 * Q := Nat.mul_le_mul_right Q (by omega)
        | have m1 : (n0 + n2 + 1) * Q ≤ n1 * Q := Nat.mul_le_mul_right Q (by omega)
      nlinarith only [ha.2.2.1, m1, hbsum, hb0, hb1, hb2, hsub0, hsub1, hsub2]
    · by_contra hfail
      first
        | have m2 : (n0 + n1 + 2) * Q ≤ n2 * Q := Nat.mul_le_mul_right Q (by omega)
        | have m2 : (n0 + n1 + 1) * Q ≤ n2 * Q := Nat.mul_le_mul_right Q (by omega)
      nlinarith only [ha.2.2.2, m2, hbsum, hb0, hb1, hb2, hsub0, hsub1, hsub2]

/--
The upper inequalities can be read back from the local split.

If `a` has upper size `P * Q`, `b` has upper size `Q`, and `a` is obtained from
`n` and `b` by `PhiQ`, then `n` must satisfy the level-one upper inequalities
at size `2 * P`.
-/
theorem upper_splitN
    (P Q : ℕ) (hQge : 3 ≤ Q) (hQodd : Q % 2 = 1)
    {a b n : Triple} (ha : Upper (P * Q) a) (hb : Upper Q b)
    (hphi : (fun i => PhiQ Q (n i) (b i)) = a) :
    Upper (2 * P) n := by
  rcases hb with ⟨hbsum, hb0, hb1, hb2⟩
  have haPhi : Upper (P * Q) (fun i => PhiQ Q (n i) (b i)) := by
    rw [hphi]
    exact ha
  have haOdd : UpperOdd (P * Q) (fun i => PhiQ Q (n i) (b i)) :=
    upper_iff_upperOdd.mp haPhi
  have hb0half : b 0 ≤ (Q - 3) / 2 :=
    half_bound_of_two_mul_add_two_le hQodd
      (by simpa [Upper] using
        (upper_two_mul_coord_add_two_le (L := Q)
          (a := b) ⟨hbsum, hb0, hb1, hb2⟩ 0))
  have hb1half : b 1 ≤ (Q - 3) / 2 :=
    half_bound_of_two_mul_add_two_le hQodd
      (by simpa [Upper] using
        (upper_two_mul_coord_add_two_le (L := Q)
          (a := b) ⟨hbsum, hb0, hb1, hb2⟩ 1))
  have hb2half : b 2 ≤ (Q - 3) / 2 :=
    half_bound_of_two_mul_add_two_le hQodd
      (by simpa [Upper] using
        (upper_two_mul_coord_add_two_le (L := Q)
          (a := b) ⟨hbsum, hb0, hb1, hb2⟩ 2))
  have hfunPhi :
      (fun i : Fin 3 => match i with
        | 0 => PhiQ Q (n 0) (b 0)
        | 1 => PhiQ Q (n 1) (b 1)
        | 2 => PhiQ Q (n 2) (b 2)) =
      (fun i => PhiQ Q (n i) (b i)) := by
    funext i
    fin_cases i <;> rfl
  have haOdd' :
      UpperOdd (P * Q)
        (fun i : Fin 3 => match i with
          | 0 => PhiQ Q (n 0) (b 0)
          | 1 => PhiQ Q (n 1) (b 1)
          | 2 => PhiQ Q (n 2) (b 2)) := by
    rwa [hfunPhi]
  have h := upper_split_scalar P Q (n 0) (n 1) (n 2) (b 0) (b 1) (b 2)
    hQge haOdd' hbsum hb0 hb1 hb2 hb0half hb1half hb2half
  have hfunN :
      (fun i : Fin 3 => match i with
        | 0 => n 0
        | 1 => n 1
        | 2 => n 2) = n := by
    funext i
    fin_cases i <;> rfl
  rwa [hfunN] at h

/--
Forward direction of the local factorization.

Given an admissible level-one triple `n ∈ C (2 * P) 1` and an admissible
lower-level triple `b ∈ C P (N - 1)`, their coordinatewise combination by
`Phi3` is an admissible triple in `C P N`.

The proof has two parts.  The top upper inequalities are supplied by
`upper_forward`.  For the lower-level residue conditions, reducing modulo
`P^M` either sees the residue of `b` or its folded complement, according to the
parity of the corresponding coordinate of `n`.
-/
theorem local_forward
    (P N : ℕ) (hP : 3 ≤ P) (hOdd : P % 2 = 1) (hN : 2 ≤ N)
    {n b : Triple} (hn : C (2 * P) 1 n) (hb : C P (N - 1) b) :
    C P N (Phi3 P N (n, b)) := by
  have hQpos : 0 < P^(N - 1) := Nat.pow_pos (by omega : 0 < P)
  have hN1 : 1 ≤ N - 1 := by omega
  have hP1 : 1 ≤ P := by omega
  have hQge : 3 ≤ P^(N - 1) := by
    have hpow : P^1 ≤ P^(N - 1) := pow_le_pow_right₀ hP1 hN1
    have hpow' : P ≤ P^(N - 1) := by simpa using hpow
    exact le_trans hP hpow'
  have hQodd : P^(N - 1) % 2 = 1 := odd_pow_mod_two (P := P) (N := N - 1) hOdd
  have hpowN : P^N = P * P^(N - 1) := by
    have hNeq : N = (N - 1) + 1 := by omega
    calc
      P^N = P^((N - 1) + 1) := by conv_lhs => rw [hNeq]
      _ = P^(N - 1) * P := by rw [pow_succ]
      _ = P * P^(N - 1) := by rw [mul_comm]
  have hnUpper : Upper (2 * P) n := by
    simpa using hn.1
  constructor
  · rw [hpowN]
    change Upper (P * P^(N - 1)) (fun i => PhiQ (P^(N - 1)) (n i) (b i))
    exact upper_forward P (P^(N - 1)) hQge hQodd hnUpper hb.1
  · intro M hM1 hMN
    by_cases htop : M = N - 1
    · subst M
      refine ⟨b, ?_, hb.1⟩
      intro i
      have hbHalf : b i ≤ (P^(N - 1) - 3) / 2 :=
        half_bound_of_two_mul_add_two_le hQodd
          (upper_two_mul_coord_add_two_le hb.1 i)
      have hbQ : b i < P^(N - 1) := by omega
      unfold FoldChoice
      by_cases he : n i % 2 = 0
      · left
        change b i = PhiQ (P^(N - 1)) (n i) (b i) % P^(N - 1)
        rw [phiQ_mod_low_even (R := P^(N - 1)) (Q := P^(N - 1))
          (n := n i) (b := b i) dvd_rfl he]
        exact (Nat.mod_eq_of_lt hbQ).symm
      · right
        change b i = P^(N - 1) - 1 -
          PhiQ (P^(N - 1)) (n i) (b i) % P^(N - 1)
        rw [phiQ_mod_low_odd (R := P^(N - 1)) (Q := P^(N - 1))
          (n := n i) (b := b i) hQpos dvd_rfl hbQ he]
        rw [Nat.mod_eq_of_lt hbQ]
        omega
    · have hMlt : M < N - 1 := by omega
      obtain ⟨c, hcFold, hcUpper⟩ := hb.2 M hM1 hMlt
      refine ⟨c, ?_, hcUpper⟩
      intro i
      have hPMpos : 0 < P^M := Nat.pow_pos (by omega : 0 < P)
      have hMle : M ≤ N - 1 := by omega
      have hdvd : P^M ∣ P^(N - 1) := Nat.pow_dvd_pow P hMle
      have hbHalf : b i ≤ (P^(N - 1) - 3) / 2 :=
        half_bound_of_two_mul_add_two_le hQodd
          (upper_two_mul_coord_add_two_le hb.1 i)
      have hbQ : b i < P^(N - 1) := by omega
      apply foldChoice_transport hPMpos
      · by_cases he : n i % 2 = 0
        · left
          simpa [Phi3, Phi, PhiQ] using
            phiQ_mod_low_even (R := P^M) (Q := P^(N - 1))
              (n := n i) (b := b i) hdvd he
        · right
          simpa [Phi3, Phi, PhiQ] using
            phiQ_mod_low_odd (R := P^M) (Q := P^(N - 1))
              (n := n i) (b := b i) hPMpos hdvd hbQ he
      · exact hcFold i

/--
Reverse direction of the local factorization.

Given an admissible triple `a ∈ C P N`, split each coordinate modulo
`P^(N-1)`.  The quotient/parity part gives a triple in `C (2 * P) 1`, while the
folded remainder part gives a triple in `C P (N - 1)`.

The important point is that the lower-level witness at `M = N - 1` identifies
the folded remainder uniquely.  Once this top folded remainder is known, all
smaller residue conditions follow by reducing modulo the smaller powers of
`P`.
-/
theorem local_split_mem
    (P N : ℕ) (hP : 3 ≤ P) (hOdd : P % 2 = 1) (hN : 2 ≤ N)
    {a : Triple} (ha : C P N a) :
    C (2 * P) 1 (fun i => SplitN P N (a i)) ∧
    C P (N - 1) (fun i => SplitB P N (a i)) := by
  have hQpos : 0 < P^(N - 1) := Nat.pow_pos (by omega : 0 < P)
  have hN1 : 1 ≤ N - 1 := by omega
  have hP1 : 1 ≤ P := by omega
  have hQge : 3 ≤ P^(N - 1) := by
    have hpow : P^1 ≤ P^(N - 1) := pow_le_pow_right₀ hP1 hN1
    have hpow' : P ≤ P^(N - 1) := by simpa using hpow
    exact le_trans hP hpow'
  have hQodd : P^(N - 1) % 2 = 1 := odd_pow_mod_two (P := P) (N := N - 1) hOdd
  have hpowN : P^N = P * P^(N - 1) := by
    have hNeq : N = (N - 1) + 1 := by omega
    calc
      P^N = P^((N - 1) + 1) := by conv_lhs => rw [hNeq]
      _ = P^(N - 1) * P := by rw [pow_succ]
      _ = P * P^(N - 1) := by rw [mul_comm]
  obtain ⟨c, hcFold, hcUpper⟩ := ha.2 (N - 1) hN1 (by omega)
  have hB : (fun i => SplitB P N (a i)) = c := by
    funext i
    have hcHalf : c i ≤ (P^(N - 1) - 3) / 2 :=
      half_bound_of_two_mul_add_two_le hQodd
        (upper_two_mul_coord_add_two_le hcUpper i)
    have h := splitBQ_eq_of_foldChoice (Q := P^(N - 1)) (A := a i) (c := c i)
      hQpos hQge hcHalf (hcFold i)
    simpa [SplitB, SplitBQ] using h
  have hBU : Upper (P^(N - 1)) (fun i => SplitB P N (a i)) := by
    rw [hB]
    exact hcUpper
  have haUpperPQ : Upper (P * P^(N - 1)) a := by
    simpa [hpowN] using ha.1
  have hphi : (fun i => PhiQ (P^(N - 1)) (SplitN P N (a i)) (SplitB P N (a i))) = a := by
    funext i
    have h := phiQ_split (Q := P^(N - 1)) (A := a i) hQpos
    simpa [SplitN, SplitB, SplitNQ, SplitBQ] using h
  constructor
  · constructor
    · simpa using upper_splitN P (P^(N - 1)) hQge hQodd haUpperPQ hBU hphi
    · intro M hM1 hMlt
      omega
  · constructor
    · exact hBU
    · intro M hM1 hMlt
      have hMN : M < N := by omega
      obtain ⟨d, hdFold, hdUpper⟩ := ha.2 M hM1 hMN
      refine ⟨d, ?_, hdUpper⟩
      intro i
      have hPMpos : 0 < P^M := Nat.pow_pos (by omega : 0 < P)
      have hMle : M ≤ N - 1 := by omega
      have hdvd : P^M ∣ P^(N - 1) := Nat.pow_dvd_pow P hMle
      apply foldChoice_transport (P := P) (M := M)
        (x := (fun i => SplitB P N (a i)) i) (b := a i) (y := d i) hPMpos
      · have hlow := top_fold_to_low (R := P^M) (Q := P^(N - 1))
          (A := a i) (c := c i) hPMpos hQpos hdvd (hcFold i)
        have hBi := congrFun hB i
        change SplitB P N (a i) % P^M = a i % P^M ∨
          SplitB P N (a i) % P^M = P^M - 1 - a i % P^M
        rw [hBi]
        exact hlow
      · exact hdFold i

theorem local_split_phi
    (P N : ℕ) (hP : 3 ≤ P) (hOdd : P % 2 = 1) (hN : 2 ≤ N)
    {a : Triple} (ha : C P N a) :
    Phi3 P N ((fun i => SplitN P N (a i)), (fun i => SplitB P N (a i))) = a := by
  funext i
  have hQpos : 0 < P^(N - 1) := Nat.pow_pos (by omega : 0 < P)
  have h := phiQ_split (Q := P^(N - 1)) (A := a i) hQpos
  simpa [Phi3, Phi, SplitN, SplitB, PhiQ, SplitNQ, SplitBQ] using h

theorem local_phi_split
    (P N : ℕ) (hP : 3 ≤ P) (hOdd : P % 2 = 1) (hN : 2 ≤ N)
    {n b : Triple} (hn : C (2 * P) 1 n) (hb : C P (N - 1) b) :
    (fun i => SplitN P N (Phi P N (n i) (b i))) = n ∧
    (fun i => SplitB P N (Phi P N (n i) (b i))) = b := by
  have hQpos : 0 < P^(N - 1) := Nat.pow_pos (by omega : 0 < P)
  have hN1 : 1 ≤ N - 1 := by omega
  have hP1 : 1 ≤ P := by omega
  have hQge : 3 ≤ P^(N - 1) := by
    have hpow : P^1 ≤ P^(N - 1) := pow_le_pow_right₀ hP1 hN1
    have hpow' : P ≤ P^(N - 1) := by simpa using hpow
    exact le_trans hP hpow'
  have hQodd : P^(N - 1) % 2 = 1 := odd_pow_mod_two (P := P) (N := N - 1) hOdd
  have hbHalf : ∀ i, b i ≤ (P^(N - 1) - 3) / 2 := by
    intro i
    exact half_bound_of_two_mul_add_two_le hQodd
      (upper_two_mul_coord_add_two_le hb.1 i)
  constructor
  · funext i
    by_cases he : n i % 2 = 0
    · have h := split_phiQ_even (Q := P^(N - 1)) (n := n i) (b := b i)
        hQpos (hbHalf i) he
      simpa [SplitN, Phi, SplitNQ, PhiQ] using h.1
    · have h := split_phiQ_odd (Q := P^(N - 1)) (n := n i) (b := b i)
        hQpos hQge (hbHalf i) he
      simpa [SplitN, Phi, SplitNQ, PhiQ] using h.1
  · funext i
    by_cases he : n i % 2 = 0
    · have h := split_phiQ_even (Q := P^(N - 1)) (n := n i) (b := b i)
        hQpos (hbHalf i) he
      simpa [SplitB, Phi, SplitBQ, PhiQ] using h.2
    · have h := split_phiQ_odd (Q := P^(N - 1)) (n := n i) (b := b i)
        hQpos hQge (hbHalf i) he
      simpa [SplitB, Phi, SplitBQ, PhiQ] using h.2

/--
Local factorization of admissible triples.

This is assembled from the explicit forward map and the explicit split map.
-/
noncomputable def localFactorization
    (P N : ℕ) (hP : 3 ≤ P) (hOdd : P % 2 = 1) (hN : 2 ≤ N) :
    {x : Triple × Triple // C (2 * P) 1 x.1 ∧ C P (N - 1) x.2} ≃
    {a : Triple // C P N a} := by
  classical
  refine
    { toFun := ?toFun
      invFun := ?invFun
      left_inv := ?left_inv
      right_inv := ?right_inv }
  · intro x
    exact ⟨Phi3 P N x.1, local_forward P N hP hOdd hN x.2.1 x.2.2⟩
  · intro a
    exact
      ⟨((fun i => SplitN P N (a.1 i)), (fun i => SplitB P N (a.1 i))),
        local_split_mem P N hP hOdd hN a.2⟩
  · intro x
    apply Subtype.ext
    have h := local_phi_split P N hP hOdd hN x.2.1 x.2.2
    exact Prod.ext h.1 h.2
  · intro a
    apply Subtype.ext
    exact local_split_phi P N hP hOdd hN a.2

end VerschiebungLean
