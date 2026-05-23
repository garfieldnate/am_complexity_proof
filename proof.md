# #P-Completeness of Computing the Size of a Union of a Family of Powersets

## Problem Definition

**#⋃℘**: Given a family of sets S₁, S₂, ..., Sₖ ⊆ [n], compute |⋃ᵢ ℘(Sᵢ)|.

In words: count the number of distinct sets that appear in the powerset of at least one Sᵢ. Equivalently, count the sets T ⊆ [n] such that T ⊆ Sᵢ for at least one i.

This problem arises in Analogical Modeling (AM), a memory-based classifier. The paper "Efficient Modeling of Analogy" (Johnsen & Johansson, 2005) explicitly notes: *"We are not aware of any algorithmically cheap (i.e. polynomial) way of determining the union of a family of powersets."* The proof below confirms that no such algorithm exists unless #P collapses.

---

## Result

**Theorem.** #⋃℘ is #P-complete.

The proof has two parts: membership in #P, and #P-hardness.

---

## Part 1: #⋃℘ is in #P

A problem is in #P if it counts the solutions to a relation that is verifiable in polynomial time.

**Verification:** Given an instance ⟨S₁,...,Sₖ⟩ and a candidate set T, we can check T ∈ ⋃ᵢ ℘(Sᵢ) by testing whether T ⊆ Sᵢ for some i. This requires O(n · k) time — polynomial in the input size.

Therefore #⋃℘ ∈ #P. □

---

## Part 2: #⋃℘ is #P-hard

We reduce from **#VERTEX-COVER**, which is known to be #P-hard (Greenhill, 2000, via the bijection between vertex covers and independent sets).

### Background: #VERTEX-COVER

A **vertex cover** of a graph G = (V, E) is a set T ⊆ V such that every edge has at least one endpoint in T:

> T is a vertex cover iff ∀e ∈ E: T ∩ e ≠ ∅

**#VERTEX-COVER** asks: how many vertex covers does G have?

This is #P-hard because vertex covers and independent sets are in bijection (T is a vertex cover iff V \ T is an independent set), and counting independent sets is #P-hard (Greenhill, 2000).

### The Reduction

**Construction.** Given a graph G = (V, E) with V = {1,...,n} and edges e₁,...,eₘ, define:

> Sⱼ = V \ eⱼ   for each edge eⱼ ∈ E

That is, Sⱼ contains all vertices *except* the two endpoints of edge eⱼ. This produces a family F = {S₁,...,Sₘ} of (n − 2)-element subsets of V, constructible in O(n · m) time.

### Key Lemma

**Lemma.** T ⊆ V is a vertex cover of G if and only if T ∉ ⋃ⱼ ℘(Sⱼ).

**Proof.**

T ∉ ⋃ⱼ ℘(Sⱼ)

⟺ for all j: T ∉ ℘(Sⱼ)        (definition of union)

⟺ for all j: T ⊄ Sⱼ            (definition of powerset)

⟺ for all j: T ⊄ V \ eⱼ        (substituting Sⱼ = V \ eⱼ)

⟺ for all j: T ∩ eⱼ ≠ ∅        (T hits something outside V \ eⱼ, i.e., inside eⱼ)

⟺ T is a vertex cover of G.    □

### Completing the Reduction

By the lemma, the vertex covers of G are exactly the subsets of V that are *not* in ⋃ⱼ ℘(Sⱼ). Therefore:

> **#vertex covers of G = 2ⁿ − |⋃ⱼ ℘(Sⱼ)|**

Given an oracle for #⋃℘, we compute the right-hand side in one oracle call and subtract from 2ⁿ (which is computable in polynomial time). The construction of the Sⱼ is polynomial in the input size. This is a valid polynomial-time Turing reduction from #VERTEX-COVER to #⋃℘.

Since #VERTEX-COVER is #P-hard, #⋃℘ is #P-hard. □

---

## Conclusion

#⋃℘ is in #P (Part 1) and #P-hard (Part 2), therefore **#⋃℘ is #P-complete**.

This means the problem is among the hardest counting problems — at least as hard as counting satisfying assignments of a Boolean formula (#SAT) or counting perfect matchings in a bipartite graph (#PERFECT-MATCHING, Valiant 1979). By Toda's theorem (1991), a polynomial-time oracle for #⋃℘ would suffice to solve every problem in the entire polynomial hierarchy.

---

## References

- Johnsen, L.G. & Johansson, C. (2005). *Efficient Modeling of Analogy*. DOI: 10.1007/978-3-540-30586-6_77
- Valiant, L.G. (1979). The complexity of computing the permanent. *Theoretical Computer Science*, 8(2): 189–201.
- Greenhill, C.S. (2000). The complexity of counting colourings and independent sets in sparse graphs and hypergraphs. *Computational Complexity*, 9(1): 52–72.
- Toda, S. (1991). PP is as hard as the polynomial-time hierarchy. *SIAM Journal on Computing*, 20(5): 865–877.
