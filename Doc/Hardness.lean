import VersoManual
import CountUnionFamilyPowersetsProof.AM.Hardness

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Classical

set_option pp.rawOnError true

#doc (Manual) "Part II: #⋃℘ ≤ Exact AM Scoring" =>

_Lean source: `CountUnionFamilyPowersetsProof/AM/Hardness.lean`_

This part proves the right half of the hardness chain: given an oracle for the
exact AM score, we can compute |⋃ᵢ 𝒫(Sᵢ)| in polynomial time.  Together with
Part I, this makes exact AM scoring #P-hard.

The strategy mirrors Part I: we build a small database D and test query τ such
that the AM score equals 2ⁿ − |⋃ᵢ 𝒫(Sᵢ)|.  Subtraction recovers the answer.

# The Database Construction

Given a #⋃℘ instance — a family ℱ = \{S₁, …, Sₖ\} ⊆ 𝒫(Fin n) — we construct
an AM database over *n+1 features* (indexed by `Fin (n+1)`) with two outcome
classes (`Fin 2`, i.e., outcomes 0 and 1).

Feature slots 0 through n−1 represent the n "real" features; slot n is a
"fresh" marker.  The embedding `embedFin` injects a subset of `Fin n` into
`Fin (n+1)` by lifting each element with `Fin.castSucc`:

```lean
#check @embedFin
```

`embedFin S = S.image Fin.castSucc`.  Since `Fin.castSucc` is injective and
never produces `Fin.last n`, the embedding keeps all real features below slot n.

The *fresh feature* is slot n itself:

```lean
#check @freshFeature
```

It is absent from the class-0 exemplar and from every real-feature pattern.
Its only role is to tag class-1 exemplars, distinguishing them from class-0.

The test query uses *all* features simultaneously:

```lean
#check @testExemplar
```

`testExemplar n = Finset.univ : Finset (Fin (n+1))`.  With τ = univ, the
match pattern of any exemplar d is τ ∩ d.features = d.features exactly.

We place exactly k + 1 exemplars in the database.  The *class-0 exemplar* `d₀`
carries all n real features and has outcome 0:

```lean
#check @d₀
```

Its feature set is `embedFin Finset.univ = \{0, …, n−1\}`.

For each Sᵢ ∈ ℱ, a *class-1 exemplar* `dᵢ Sᵢ` carries the embedded features
of Sᵢ together with the fresh feature n, and has outcome 1:

```lean
#check @dᵢ
```

Feature set: `embedFin Sᵢ ∪ \{freshFeature n\}`.

The full database is:

```lean
#check @encodeDatabase
```

`encodeDatabase n ℱ = \{d₀ n\} ∪ ℱ.image (dᵢ n)`.

The match pattern of `d₀` against τ = univ is `d₀.features`, which we call
`x_A` in the Lean code:

```lean
#check @x_A
```

`x_A n = \{0, …, n−1\}`.  The coefficient `c` at `x_A` drives the entire
class-0 AM score.

# The Fresh Feature Separates the Classes

The key invariant is that the fresh feature n *never appears* in `x_A` or in
any real-feature pattern, but *always appears* in every class-1 exemplar's
feature set.

```lean
#check @d₀_not_fresh
#check @dᵢ_has_fresh
#check @fresh_not_in_xA
```

As a consequence, any pattern q ⊆ Fin (n+1) that does not contain n is
necessarily a subset of `x_A`:

```lean
#check @sub_xA_of_no_fresh
```

This lets us split the analysis of every superset q ⊇ p into two exhaustive
cases: either n ∈ q, or q ⊆ `x_A`.

# Match Patterns and θ-Fibers

Since τ = univ, the match set is simply the set of feature vectors:

```lean
#check @matchSet_encodeDatabase
```

M = \{`x_A`\} ∪ \{`embedFin S ∪ \{n\}` | S ∈ ℱ\}.  The patterns are pairwise
distinct: `x_A` never contains n, while every class-1 pattern does.

The θ-fiber at `x_A` contains exactly `d₀`:

```lean
#check @θ_xA
```

An exemplar e in θ(`x_A`) satisfies e.features = `x_A`.  Among all exemplars,
only `d₀` has features \{0, …, n−1\}.

The class-0 outcome count in each fiber is:

```lean
#check @outcomeCount_θ_xA
#check @outcomeCount_θ_non_xA
```

`outcomeCount(θ(x_A), 0) = 1` (the fiber \{`d₀`\} has exactly one class-0
exemplar), and for every class-1 fiber `outcomeCount = 0`.

# Support Characterization

For a pattern p ⊆ `x_A` (which never contains n), the support of p splits
cleanly by outcome class.

`d₀` is always in σ(p), since p ⊆ `x_A` = `d₀.features`:

```lean
#check @d₀_in_σ_of_sub_xA
```

`dᵢ S` is in σ(p) if and only if p ⊆ `embedFin S`.  Because p never contains
n, the containment p ⊆ `embedFin S ∪ \{n\}` is equivalent to p ⊆ `embedFin S`:

```lean
#check @dᵢ_in_σ_iff
```

For p ⊆ `x_A`, σ(p) contains `d₀` always, and also `dᵢ S` whenever p "fits
inside" S.  If p fits inside some Sᵢ, both a class-0 and a class-1 exemplar
support p, creating disagreement.  If p fits inside _no_ Sᵢ, only `d₀`
supports p, giving unanimous class-0 agreement.

# Disagreement Analysis

When σ(p) contains exemplars of different outcome classes, δ(p) > 0:

```lean
#check @δ_pos_of_disagreeing
```

When n ∈ q, `d₀` cannot support q (it lacks feature n), so σ(q) is entirely
class-1, making δ(q) = 0:

```lean
#check @d₀_not_in_σ_if_fresh
#check @δ_zero_of_fresh_in_q
```

This is the key mechanism: *adding the fresh feature n to a pattern forces δ
to drop to 0*, because `d₀` (the only source of class-0 votes) gets excluded.

# Homogeneity Characterization

This is the mathematical core of the reduction.

```lean
#check @isHomogeneous_iff
```

For p ⊆ `x_A`:

p is homogeneous in (τ, D)  ⟺  ∀ S ∈ ℱ, p ⊄ `embedFin S`.

In words: a sub-pattern of `x_A` is homogeneous *exactly when it avoids every
Sᵢ in the family*.

*Proof sketch (⇒).* Suppose p ⊆ `embedFin Sᵢ` for some Sᵢ.  Then both `d₀`
(class-0) and `dᵢ Sᵢ` (class-1) support p, so δ(p) > 0.  Consider
q = p ∪ \{n\}: the fresh feature n excludes `d₀` from σ(q), leaving only
class-1 support, so δ(q) = 0.  Since p ⊆ q and σ(q) is nonempty, homogeneity
requires δ(q) = δ(p), giving 0 = δ(q) = δ(p) > 0, a contradiction.

*Proof sketch (⇐).* Suppose p avoids all Sᵢ.  Then σ(p) = \{`d₀`\} only, so
δ(p) = 0.  For any superset q ⊇ p in 𝒫(τ): if n ∈ q then δ(q) = 0 by the
fresh-feature lemma; if n ∉ q then q ⊆ `x_A` and the same avoidance argument
shows δ(q) = 0.  So δ is constantly 0 above p, confirming homogeneity.

# Counting the Class-0 Coefficient

The characterization of homogeneous patterns immediately gives:

```lean
#check @c_xA_eq_card_avoiding
```

`c (testExemplar n) D (x_A n)` equals the count of subsets p ⊆ `x_A` that
avoid all Sᵢ.

The "bad" subsets of `x_A` — those that belong to ⋃ᵢ 𝒫(`embedFin Sᵢ`) — are
collected as `unionEmbeddedPowersets`:

```lean
#check @unionEmbeddedPowersets
```

Good subsets (homogeneous) and bad subsets (non-homogeneous) partition 𝒫(`x_A`),
which has 2ⁿ elements (since |`x_A`| = n).  Therefore:

```lean
#check @c_xA_counting
```

`c (testExemplar n) D (x_A n) + |unionEmbeddedPowersets ℱ| = 2 ^ n`.

# The Total Score

By the representation theorem (`representation_theorem`), the total class-0
score is the weighted sum over each x in M of cₓ times outcomeCount(θ(x), 0).
Only `x_A` contributes, because all other θ-fibers have zero class-0 exemplars.
Therefore:

```lean
#check @totalScore_eq_c_xA
```

`totalScore (testExemplar n) D 0 = c (testExemplar n) D (x_A n)`.

# The Main Theorem

Combining the score formula with the counting equation:

```lean
#check @exact_AM_scoring_is_hard
```

For the encoded database:

`totalScore (testExemplar n) (encodeDatabase n ℱ) 0 + |unionEmbeddedPowersets ℱ| = 2 ^ n`.

*Why this completes the reduction.* Given an oracle O for `totalScore`, we
recover `|⋃ᵢ 𝒫(Sᵢ)|` = 2ⁿ − O(`testExemplar n`, `encodeDatabase n ℱ`, 0).

The database `encodeDatabase n ℱ` has k + 1 exemplars and n + 1 features,
both linear in the input size.  This is a polynomial-time Turing reduction
from #⋃℘ to exact-AM-scoring.

Combined with Part I:

`#VERTEX-COVER  ≤  #⋃℘  ≤  exact-AM-scoring`.

Since #VERTEX-COVER is *#P-hard*, exact AM scoring is *#P-hard*.  Since AM
membership is verifiable in polynomial time, exact AM scoring is *#P-complete*.
