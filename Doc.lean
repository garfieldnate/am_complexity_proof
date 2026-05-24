import VersoManual
import Doc.Introduction
import Doc.Background
import Doc.VertexCover
import Doc.Hardness

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "AM #P-Completeness: A Lean 4 Proof" =>

%%%
authors := ["Nathan Glenn"]
%%%

This document is a machine-checked proof, formalized in Lean 4 with Mathlib,
that computing the exact **Analogical Modeling (AM) score** is #P-complete.

The proof proceeds via a chain of polynomial-time Turing reductions:

```
#VERTEX-COVER  ≤  #⋃℘  ≤  exact-AM-scoring
```

Each `≤` means "is polynomial-time Turing-reducible to," making each step at
least as hard as the one before it.  Since `#VERTEX-COVER` is known to be
#P-hard (Greenhill 2000), exact AM scoring is also #P-hard.  Combined with the
observation that AM is in #P, it is **#P-complete**.

Both reductions share the same structural trick: embed the counting problem into
a complementary equation of the form

```
answer  +  oracle-query  =  2ⁿ
```

so that the answer is recoverable by subtraction.  Part I establishes this for
vertex covers; Part II establishes it for AM scores.

{include 1 Doc.Introduction}

{include 1 Doc.Background}

{include 1 Doc.VertexCover}

{include 1 Doc.Hardness}
