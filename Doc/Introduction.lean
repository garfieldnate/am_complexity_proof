import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "The Complexity Class #P" =>

The class *#P* (pronounced "sharp P") was introduced by Valiant (1979) to
capture counting problems.  Where NP asks _does a solution exist?_, #P asks
_how many solutions exist?_

Formally, a function _f_ is in *#P* if there exists a polynomial-time
nondeterministic Turing machine _M_ such that _f(x)_ is the number of accepting
computation paths of _M_ on input _x_.

A problem is *#P-hard* if every problem in #P is polynomial-time
Turing-reducible to it.  A problem that is both #P-hard and in #P is
*#P-complete*.

Famous #P-complete problems include counting the perfect matchings in a
bipartite graph (equivalent to the matrix permanent), counting the satisfying
assignments of a CNF formula, and counting the vertex covers of a graph.
The last of these — #VERTEX-COVER — is the starting point for our chain of
reductions.

# The Intermediate Problem #⋃℘

As an intermediate step we use the problem *#⋃℘*:

Given a finite family of sets \{S₁, …, Sₖ\} ⊆ 𝒫(U), compute
`|⋃ᵢ 𝒫(Sᵢ)|`.

A subset _T_ belongs to ⋃ᵢ 𝒫(Sᵢ) exactly when T ⊆ Sᵢ for some _i_.
So *#⋃℘* asks: how many subsets of _U_ are contained in at least one Sᵢ?

This problem sits naturally between #VERTEX-COVER and AM: vertex covers map
onto it combinatorially (Part I), and it embeds into AM algorithmically
(Part II).
