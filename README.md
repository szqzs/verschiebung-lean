# VerschiebungLean

This repository contains a Lean 4 formalization of two elementary pieces of
combinatorics and trigonometry around admissible edge labelings of trivalent
graphs.

The project uses Lean `v4.31.0` and mathlib `v4.31.0`, pinned by
`lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`.

## How to check the proofs

Install Lean through `elan`, then run:

```bash
lake exe cache get
lake build
```

The command `lake build` checks all theorem statements and proofs in the
repository.

## Mathematical objects

The file `VerschiebungLean/Defs.lean` defines the basic combinatorial objects.

* A local triple is a function `Fin 3 -> Nat`.
* `Upper L a` is the system of four inequalities

  $$
  a_0+a_1+a_2+2 \le L,\qquad
  a_0 \le a_1+a_2,\qquad
  a_1 \le a_0+a_2,\qquad
  a_2 \le a_0+a_1.
  $$

* `C P N a` is the level `N` local admissibility condition at parameter `P`.
  It consists of `Upper (P^N) a` together with the folded lower-level residue
  conditions modulo `P^M` for `1 <= M < N`.
* `Phi P N n b` is the one-coordinate folding map. When `n` is even, it is
  `(n / 2) * P^(N - 1) + b`. When `n` is odd, it is
  `((n + 1) / 2) * P^(N - 1) - 1 - b`.

  The definition `Phi3` applies this map coordinatewise to triples.
* `TriGraph` is a minimal incidence model for trivalent multigraphs. This
  avoids using simple graphs, since parallel edges are allowed.
* `EdSet G P N` is the type of admissible edge labelings of a trivalent graph
  `G`, where the three labels incident to every vertex satisfy `C P N`.

## Local factorization

The file `VerschiebungLean/Local.lean` proves the local one-step factorization.

For an odd integer `P >= 3` and an integer `N >= 2`, the main result is
`localFactorization`:

```lean
noncomputable def localFactorization
    (P N : ℕ) (hP : 3 ≤ P) (hOdd : P % 2 = 1) (hN : 2 ≤ N) :
    {x : Triple × Triple // C (2 * P) 1 x.1 ∧ C P (N - 1) x.2} ≃
    {a : Triple // C P N a}
```

In mathematical notation, this is the bijection

$$
C_N(P) \simeq C_1(2P)\times C_{N-1}(P).
$$

The forward map is `Phi3`. The inverse map splits each coordinate `A` by
writing

$$
A=qP^{N-1}+r.
$$

If `r` lies in the lower half, it records `n=2q` and `b=r`; if `r` lies in the
upper half, it records `n=2q+1` and `b=P^{N-1}-1-r`.

The theorem `local_forward` proves that the forward map preserves
admissibility. The theorem `local_split_mem` proves that the split map produces
one triple in `C (2 * P) 1` and one triple in `C P (N - 1)`. The inverse laws
are proved by `local_split_phi` and `local_phi_split`.

Thus uniqueness of the local decomposition is part of the formalized
bijection, not an additional assumption.

## Global factorization

The file `VerschiebungLean/Global.lean` lifts the local factorization to
edge labelings of a trivalent graph.

For a trivalent graph `G`, odd `P >= 3`, and `N >= 2`, the main result is
`globalStep`:

```lean
noncomputable def globalStep
    (P N : ℕ) (hP : 3 ≤ P) (hOdd : P % 2 = 1) (hN : 2 ≤ N) :
    EdSet G P N ≃ (EdSet G (2 * P) 1 × EdSet G P (N - 1))
```

In mathematical notation, this is the bijection

$$
\mathrm{Ed}_{P,N,G}
\simeq
\mathrm{Ed}_{2P,1,G}\times \mathrm{Ed}_{P,N-1,G}.
$$

The construction is edgewise: split every edge label to get the two labelings
on the right, or recombine the two right-hand labelings by `Phi`. The local
theorems from `Local.lean` verify the vertex conditions. The inverse laws are
checked edge by edge.

The iterated product formula is not separately packaged as a theorem in this
repository. The verified result is the one-step equivalence above.

## Finite trigonometric identity

The file `VerschiebungLean/Trig.lean` proves a square-root-free finite
Verlinde identity.

For `p > 0` and labels `a,b,c < p`, the quantity `fusionN p a b c` is the
level-one fusion coefficient at even parameter `2p`. It is equal to `1`
exactly when the inequalities

$$
a+b+c+2\le 2p,\qquad
a\le b+c,\qquad
b\le a+c,\qquad
c\le a+b
$$

hold. Otherwise it is equal to `0`.
Equivalently, it is the indicator function of `C1Even p a b c`.

Let

$$
\theta_j=\frac{j\pi}{2p}.
$$

The trigonometric kernel `verlindeKernel p a b c` is

$$
\frac{2}{p}\sum_{j=1}^{p-1}
\frac{
\sin((2a+1)\theta_j)
\sin((2b+1)\theta_j)
\sin((2c+1)\theta_j)
}{
\sin(\theta_j)
}
+
\frac{(-1)^{a+b+c}}{p}.
$$

The final theorem is `finiteVerlindeKernelTheorem_proved`, which proves
`finiteVerlindeKernelTheorem`, namely:

```lean
∀ p a b c : ℕ,
  0 < p → a < p → b < p → c < p →
    fusionN p a b c = verlindeKernel p a b c
```

Equivalently, for every positive integer `p` and every `a,b,c` with
`0 <= a,b,c < p`,

$$
N_{abc}^{(2p)}
=
\frac{2}{p}\sum_{j=1}^{p-1}
\frac{
\sin((2a+1)\theta_j)
\sin((2b+1)\theta_j)
\sin((2c+1)\theta_j)
}{
\sin(\theta_j)
}
+
\frac{(-1)^{a+b+c}}{p},
\qquad
\theta_j=\frac{j\pi}{2p},
$$

where `N_{abc}^{(2p)}` is `1` if the level-one admissibility inequalities at
parameter `2p` hold, and `0` otherwise.

The proof is elementary. It uses finite cosine sums, an endpoint-corrected
sine orthogonality relation, a Clebsch-Gordan telescoping identity, and
interval arithmetic.

The term `(-1)^(a+b+c)/p` is the endpoint correction corresponding to the
missing endpoint in the sum over `j = 1, ..., p-1`.
