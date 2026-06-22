import Mathlib

set_option linter.style.header false

namespace VerschiebungLean

/-- A triple of natural numbers, indexed by `0,1,2`. -/
abbrev Triple := Fin 3 → ℕ

/--
The four upper-level inequalities for an admissible triple at parameter `L`.

This uses `a 0 + a 1 + a 2 + 2 ≤ L` instead of
`a 0 + a 1 + a 2 ≤ L - 2`, because subtraction on `ℕ` is truncated.
-/
def Upper (L : ℕ) (a : Triple) : Prop :=
  a 0 + a 1 + a 2 + 2 ≤ L ∧
  a 0 ≤ a 1 + a 2 ∧
  a 1 ≤ a 0 + a 2 ∧
  a 2 ≤ a 0 + a 1

/-- The two possible folded residues of `x` modulo `P^M`. -/
def FoldChoice (P M x y : ℕ) : Prop :=
  y = x % P^M ∨ y = P^M - 1 - x % P^M

/--
The combinatorial set `{}^\dagger C_N(P)`, as a predicate on triples.

We impose the conditions for `M < N`; the case `M = N` is redundant in the
paper definition and is avoided here to make the formal statement cleaner.
-/
def C (P N : ℕ) (a : Triple) : Prop :=
  Upper (P^N) a ∧
  ∀ M, 1 ≤ M → M < N →
    ∃ b : Triple, (∀ i, FoldChoice P M (a i) (b i)) ∧ Upper (P^M) b

/-- The one-coordinate folding map. -/
def Phi (P N n b : ℕ) : ℕ :=
  if n % 2 = 0 then
    (n / 2) * P^(N - 1) + b
  else
    ((n + 1) / 2) * P^(N - 1) - 1 - b

/-- The coordinatewise folding map on triples. -/
def Phi3 (P N : ℕ) (x : Triple × Triple) : Triple :=
  fun i => Phi P N (x.1 i) (x.2 i)

/--
A minimal incidence model for the trivalent graphs used in the paper.

We deliberately do not use `SimpleGraph`, since the theta graph has parallel
edges.
-/
structure TriGraph where
  Vertex : Type
  Edge : Type
  inc : Vertex → Fin 3 → Edge
  edgeVertex : Edge → Vertex
  edgeIndex : Edge → Fin 3
  edge_inc : ∀ e : Edge, inc (edgeVertex e) (edgeIndex e) = e

/-- An edge-labeling is admissible if the three labels at every vertex lie in `C P N`. -/
def Ed (G : TriGraph) (P N : ℕ) (ℓ : G.Edge → ℕ) : Prop :=
  ∀ v : G.Vertex, C P N (fun i => ℓ (G.inc v i))

/-- The subtype of admissible edge-labelings. -/
abbrev EdSet (G : TriGraph) (P N : ℕ) :=
  {ℓ : G.Edge → ℕ // Ed G P N ℓ}

end VerschiebungLean
