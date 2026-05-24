import VersoManual
import CountUnionFamilyPowersetsProof.Basic

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Classical

set_option pp.rawOnError true

#doc (Manual) "Part I: #VERTEX-COVER ≤ #⋃℘" =>

_Lean source: `CountUnionFamilyPowersetsProof/Basic.lean`_

This part proves the left half of the hardness chain.  Given an oracle for
computing |⋃ᵢ 𝒫(Sᵢ)|, we can compute the number of vertex covers of any
graph in polynomial time.  Since #VERTEX-COVER is #P-hard (Greenhill 2000),
#⋃℘ is #P-hard too.

# Definitions

A *vertex cover* of a hypergraph (V, E) is a subset T ⊆ V that intersects
every edge.

```lean
#check @IsVertexCover
```

For a set of vertices V and a collection of edges E, define
`UCP(V, E) = ⋃_{e ∈ E} 𝒫(V \ e)` — the union of the powersets of the edge
complements:

```lean
#check @unionComplementPowersets
```

A subset T belongs to `UCP(V, E)` exactly when T ⊆ V \ e for some edge e,
i.e., when T avoids at least one edge entirely.

# The Key Bijection

The reduction rests on the observation that vertex covers and `UCP(V, E)` are
*complementary subsets* of 𝒫(V).  For T ⊆ V:

T is a vertex cover  ⟺  T ∉ UCP(V, E).

Expanding definitions: T ∈ UCP(V, E) iff there exists an edge e such that
T ⊆ V \ e, i.e., every element of T avoids e, i.e., T ∩ e = ∅, i.e., T is
_not_ a vertex cover.

```lean
#check @isVertexCover_iff_not_mem_unionComplementPowersets
```

# Partition and Counting

From the bijection it follows that vertex covers and `UCP(V, E)` partition 𝒫(V):

```lean
#check @vertexCovers_disjoint
#check @vertexCovers_union_eq
```

Every subset of V is either a vertex cover (hits every edge) or it avoids some
edge entirely (belongs to UCP).  These two cases are mutually exclusive and
exhaustive.

Since a disjoint partition has parts whose cardinalities sum to the whole, we
get the *counting equation*:

```lean
#check @counting_equation
```

Spelled out: `#vertex-covers(G) + |UCP(V, E)| = 2^|V|`.

*Why this gives the reduction.* Suppose we have an oracle O that computes
|⋃ᵢ 𝒫(Sᵢ)| for any family \{S₁, …, Sₖ\}.  Given a graph G = (V, E), set
Sⱼ = V \ eⱼ for each edge eⱼ.  Then UCP(V, E) = ⋃ⱼ 𝒫(Sⱼ), so O computes
|UCP(V, E)|, and we recover

`#vertex-covers(G) = 2^|V| − O(\{V \ e | e ∈ E\})`.

This is a single oracle call with a polynomially-sized input, so
#VERTEX-COVER reduces in polynomial time to #⋃℘.  Since #VERTEX-COVER is
#P-hard, #⋃℘ is #P-hard.
