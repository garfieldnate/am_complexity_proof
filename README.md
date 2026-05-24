# AM Hardness — Lean 4 Formalization

A machine-checked proof that computing the exact **Analogical Modeling (AM)** score
is #P-complete.

Built with [Lean 4](https://leanprover.github.io/) and [Mathlib](https://leanprover-community.github.io/mathlib4_docs/).

---

## What this proves

The project establishes a chain of reductions:

```
#VERTEX-COVER  ≤  #⋃℘  ≤  exact-AM-scoring
```

Each `≤` means "is polynomial-time reducible to", so the rightmost problem is
at least as hard as the leftmost.  Since `#VERTEX-COVER` is known to be #P-hard
(Greenhill 2000), this chain makes exact AM scoring #P-hard.  Combined with the
observation that AM membership is verifiable in polynomial time, exact AM scoring
is **#P-complete**.

The two reductions are proved in separate files and connect through the
intermediate problem **#⋃℘** (counting the size of a union of powerset families).

---

## The two proofs

### 1. `Basic.lean` — #VERTEX-COVER ≤ #⋃℘

Given a graph G = (V, E), define a family of sets by complementing each edge:

```
Sₑ = V \ e     for each edge e ∈ E
```

**Key fact** (`isVertexCover_iff_not_mem_unionComplementPowersets`):

> T ⊆ V is a vertex cover of G  ⟺  T ∉ ⋃_{e ∈ E} ℘(Sₑ)

A subset T avoids every set in ⋃ ℘(Sₑ) exactly when T hits every edge — i.e.,
when T is a vertex cover.

This gives the **counting equation** (`counting_equation`):

```
#vertex-covers(G) + |⋃_{e ∈ E} ℘(V \ e)| = 2^|V|
```

Because together, vertex covers and non-vertex-covers partition all of ℘(V).

**What this means**: if you can count |⋃ ℘(Sₑ)|, you can compute #VERTEX-COVER
by subtraction.  So #⋃℘ (on this specific input shape) is at least as hard as
#VERTEX-COVER, making #⋃℘ itself #P-hard.

---

### 2. `AM/Hardness.lean` — #⋃℘ ≤ exact-AM-scoring

Given a #⋃℘ instance — a family {S₁, …, Sₖ} ⊆ Finset (Fin n) — we construct
a small AM database that encodes the counting problem.

#### The database construction

Features are indexed by `Fin (n+1)`: slots 0 through n-1 are "real" features,
and slot n is a "fresh" marker feature added just for this construction.

| Exemplar | Features              | Outcome |
|----------|-----------------------|---------|
| `d₀`     | {0, 1, …, n-1}       | 0       |
| `dᵢ S₁`  | embedFin(S₁) ∪ {n}   | 1       |
| `dᵢ S₂`  | embedFin(S₂) ∪ {n}   | 1       |
| …        | …                     | …       |
| `dᵢ Sₖ`  | embedFin(Sₖ) ∪ {n}   | 1       |

`embedFin` maps each element of Fin n to the same slot in Fin (n+1) via
`Fin.castSucc`, leaving slot n untouched.  The test query is `τ = {0, …, n}` (all
features).

#### What AM computes on this database

If you have implemented AM, here is what each step of the algorithm produces:

**Match set M** (`matchSet_encodeDatabase`):
```
M = {x_A} ∪ { embedFin(Sᵢ) ∪ {n} | i = 1..k }
```
where `x_A = {0, …, n-1}`.  There are exactly k+1 elements in M.

**θ-fibers** (the partition of D by match pattern):
```
θ(x_A)              = {d₀}     — just the class-0 exemplar
θ(embedFin Sᵢ ∪ {n}) = {dᵢ Sᵢ}  — each class-1 exemplar in its own fiber
```

**Support σ** (exemplars "activated" by a sub-pattern p ⊆ x_A):
- d₀ is always in σ(p), because p ⊆ x_A = d₀.features.
- dᵢ Sᵢ is in σ(p) if and only if p ⊆ embedFin(Sᵢ).
  The fresh feature n is irrelevant because p ⊆ x_A never contains it.

**Homogeneity** (`isHomogeneous_iff`):

> p ⊆ x_A is homogeneous  ⟺  ∀ Sᵢ ∈ family, p ⊄ embedFin(Sᵢ)

A sub-pattern p of x_A is homogeneous exactly when it does NOT sit inside any of
the Sᵢ.  If p ⊆ Sᵢ, then both d₀ (class 0) and dᵢ Sᵢ (class 1) support p,
creating disagreement; adding the fresh feature n to make q = p ∪ {n} removes d₀
from the support (since d₀ lacks feature n), causing the disagreement count to
drop — which violates the constancy requirement for homogeneity.  Conversely, if
p avoids all Sᵢ, only d₀ ever supports p, so the support is unanimously class-0
and δ stays 0 across all supersets.

**c_{x_A} and the counting equation** (`c_xA_counting`):

The AM coefficient `c_{x_A}` counts the homogeneous sub-patterns of x_A:
```
c_{x_A} = |{p ⊆ x_A : p is homogeneous}|
         = |{p ⊆ {0..n-1} : ∀ Sᵢ, p ⊄ embedFin Sᵢ}|
         = 2^n  −  |⋃ᵢ ℘(embedFin Sᵢ)|
```

The last step uses the fact that "bad" subsets (those sitting inside some Sᵢ)
and "good" subsets (those avoiding all Sᵢ) partition all of ℘(x_A), which has
size 2^n.

**The total score** (`totalScore_eq_c_xA`):

By the representation theorem (Theorem 1 in the paper, proved in `Propositions.lean`):
```
totalScore(τ, D, 0) = Σ_{x ∈ M} c_x · outcomeCount(θ(x), 0)
```
Only x_A contributes: `outcomeCount(θ(x_A), 0) = 1`, and all other fibers have
`outcomeCount = 0` (they contain only class-1 exemplars).  So:
```
totalScore(τ, D, 0) = c_{x_A} · 1 = c_{x_A}
```

**The main theorem** (`exact_AM_scoring_is_hard`):
```
totalScore(τ, D, 0) + |⋃ᵢ ℘(embedFin Sᵢ)| = 2^n
```
Given an oracle for `totalScore`, recover `|⋃ᵢ ℘(Sᵢ)|` by subtraction.  This
is a polynomial-time Turing reduction: the database has k+1 exemplars and n+1
features, both linear in the input size.

---

## Are the two proofs connected in the Lean code?

**Yes, conceptually — but no, they don't call each other's lemmas.**

- `Basic.lean` proves that #VERTEX-COVER ≤ #⋃℘ by establishing the counting
  equation `#vertex-covers + |⋃ ℘(V \ e)| = 2^|V|`.
- `AM/Hardness.lean` proves that #⋃℘ ≤ exact-AM by establishing the analogous
  equation `totalScore(τ, D, 0) + |⋃ᵢ ℘(Sᵢ)| = 2^n`.

Both files reduce to the same structural insight: a counting problem can be
embedded into AM so that the AM score recovers the answer by subtraction from 2^n.
But neither file directly cites lemmas from the other — the chain of hardness is
assembled in the module docstrings and in this README rather than in a single
combined Lean theorem.

---

## File structure

```
Basic.lean                    #VERTEX-COVER ≤ #⋃℘ (the "left" reduction)
  IsVertexCover               — definition of vertex cover
  unionComplementPowersets    — ⋃_{e ∈ E} ℘(V \ e)
  isVertexCover_iff_not_mem_unionComplementPowersets  — the key bijection
  counting_equation           — #VC + |⋃℘| = 2^|V|

AM/
  Basic.lean                  — Exemplar, Database, lattice L = ℘(τ)
  Functions.lean              — matchSet (M), θ, σ, κ, δ; Propositions 1+2
  Homogeneity.lean            — IsHomogeneous, IsDetermHomogeneous, analogicalSet A
  Score.lean                  — outcomeCount, c_x coefficients, totalScore
  Propositions.lean           — Theorem 1: totalScoreA = totalScore (representation theorem)
  Hardness.lean               — #⋃℘ ≤ exact-AM (the "right" reduction)
    encodeDatabase            — the constructed database
    isHomogeneous_iff         — key characterization of homogeneity in the constructed DB
    c_xA_counting             — c_{x_A} + |⋃℘| = 2^n
    exact_AM_scoring_is_hard  — the main theorem
```

---

## Building

```bash
lake build
```

Requires Lean 4 and Mathlib.  The toolchain version is pinned in `lean-toolchain`.

## Interactive HTML documentation (Verso)

The proof is also presented as a literate document with hoverable types and proof
states, built with [Verso](https://github.com/leanprover/verso).

```bash
./build-docs.sh
# then open _out/html-multi/index.html
```

**Note on the build script:** `lake exe generate-docs` fails directly on macOS
because linking ~8 400 Lean object files produces a command line (~1.4 MB) that
exceeds the OS `ARG_MAX` limit (1 MB).  `build-docs.sh` works around this by
bundling all objects into a single `.a` archive via `llvm-ar` (in 500-file
batches to stay inside LLVM's own internal response-file limit) before calling
clang.  This is a platform limitation, not a bug in the proof.

---

## References

- Johnsen, M. & Johansson, U. (2005). *Efficient Modeling of Analogy*.
  §3 defines M, θ, σ, δ, homogeneity, A.
  §4 proves Propositions 1+2 and Theorem 1 (representation theorem).
  §4.3 identifies c_x computation as the #P-hard bottleneck.

- Greenhill, C. (2000). *The complexity of counting colourings and independent sets
  in sparse graphs and hypergraphs.*  Establishes #VERTEX-COVER is #P-hard.

- Valiant, L. G. (1979). *The complexity of computing the permanent.*
  Introduced the class #P.
