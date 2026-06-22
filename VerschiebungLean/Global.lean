import VerschiebungLean.Local

set_option linter.style.header false

namespace VerschiebungLean

/-!
# Global edge-numbering factorization

This file globalizes the local factorization from triples to edge numberings on
a trivalent graph.

For a trivalent graph `G`, an element of `EdSet G P N` assigns a natural number
to every edge.  At each vertex, the three incident edge labels must form a
local admissible triple in `C P N`.

The local result can therefore be applied at every vertex.  The construction
itself is edgewise: each edge label is split once into `SplitN` and `SplitB`,
or reconstructed once by `Phi`.  Since both endpoints of an edge read the same
edge label, the vertexwise local factorizations automatically agree on shared
edges.  The only formal role of `edgeVertex`, `edgeIndex`, and `edge_inc` is to
recover a chosen endpoint and local index for each edge so that the local
inverse identities can be evaluated on that edge.

The main result is `globalStep`, a one-step equivalence between level `N`
edge numberings and a pair consisting of a level-one edge numbering and a
level `N - 1` edge numbering.
-/

variable (G : TriGraph)

/--
The one-step global factorization.

An edge numbering at level `N` is sent to two edge numberings by applying
`SplitN` and `SplitB` to every edge label.  Conversely, a pair of edge
numberings is recombined edgewise by `Phi`.

The vertex conditions are exactly the local statements `local_split_mem` and
`local_forward`.  The inverse laws are also checked edgewise, using
`local_split_phi` and `local_phi_split`.
-/
noncomputable def globalStep
    (P N : ℕ) (hP : 3 ≤ P) (hOdd : P % 2 = 1) (hN : 2 ≤ N) :
    EdSet G P N ≃ (EdSet G (2 * P) 1 × EdSet G P (N - 1)) := by
  classical
  refine
    { toFun := ?toFun
      invFun := ?invFun
      left_inv := ?left_inv
      right_inv := ?right_inv }
  · intro A
    exact
      ( ⟨fun e => SplitN P N (A.1 e), by
          intro v
          exact (local_split_mem P N hP hOdd hN (a := fun i => A.1 (G.inc v i)) (A.2 v)).1⟩,
        ⟨fun e => SplitB P N (A.1 e), by
          intro v
          exact (local_split_mem P N hP hOdd hN (a := fun i => A.1 (G.inc v i)) (A.2 v)).2⟩ )
  · intro x
    exact
      ⟨fun e => Phi P N (x.1.1 e) (x.2.1 e), by
        intro v
        exact local_forward P N hP hOdd hN
          (n := fun i => x.1.1 (G.inc v i))
          (b := fun i => x.2.1 (G.inc v i))
          (x.1.2 v) (x.2.2 v)⟩
  · intro A
    apply Subtype.ext
    funext e
    have hloc := local_split_phi P N hP hOdd hN
      (a := fun i => A.1 (G.inc (G.edgeVertex e) i))
      (A.2 (G.edgeVertex e))
    have h := congrFun hloc (G.edgeIndex e)
    simpa [Phi3, G.edge_inc e] using h
  · intro x
    cases x with
    | mk n b =>
      apply Prod.ext
      · apply Subtype.ext
        funext e
        have hloc := local_phi_split P N hP hOdd hN
          (n := fun i => n.1 (G.inc (G.edgeVertex e) i))
          (b := fun i => b.1 (G.inc (G.edgeVertex e) i))
          (n.2 (G.edgeVertex e)) (b.2 (G.edgeVertex e))
        have h := congrFun hloc.1 (G.edgeIndex e)
        simpa [G.edge_inc e] using h
      · apply Subtype.ext
        funext e
        have hloc := local_phi_split P N hP hOdd hN
          (n := fun i => n.1 (G.inc (G.edgeVertex e) i))
          (b := fun i => b.1 (G.inc (G.edgeVertex e) i))
          (n.2 (G.edgeVertex e)) (b.2 (G.edgeVertex e))
        have h := congrFun hloc.2 (G.edgeIndex e)
        simpa [G.edge_inc e] using h

-- An iterated factorization should be stated separately with an explicit lower
-- bound on `N`; the one-step factorization above is the part needed for the
-- local-to-global gluing argument.

end VerschiebungLean
