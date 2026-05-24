import VersoManual
import CountUnionFamilyPowersetsProof.AM.Score

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Classical

set_option pp.rawOnError true

#doc (Manual) "The AM Algorithm" =>

Analogical Modeling (AM) is a memory-based classifier introduced by Skousen
(1989).  The algorithm classifies a test query by comparing it against a
database of exemplars — previously seen (features, outcome) pairs — and
computing a weighted vote over outcome classes.

This chapter describes every object the algorithm computes, along with its Lean
definition.  If you have already implemented AM, this is the formal
specification of what your implementation does.

# Exemplars and Databases

An *exemplar* is a record of observed features and an outcome.

```lean
#check @Exemplar
```

A *database* is a finite set of exemplars:

```lean
#check @Database
```

The *test query* τ is also a feature set; it is the item we want to classify.

# The Match Set M

The first step of AM is to intersect the test query with every exemplar's
feature set, then deduplicate.  The result is the *match set* M:

```lean
#check @matchSet
```

Concretely, `matchSet τ D = { τ ∩ d.features | d ∈ D }`.  Every element of M
is a subset of τ.  In our hardness proof, τ = Finset.univ (all features), so
τ ∩ d.features = d.features and M is just the set of feature vectors in D.

# The Partition θ

M partitions D: each exemplar maps to exactly one element of M.  The
*θ-fiber* over x ∈ M is the set of exemplars that produce match pattern x:

```lean
#check @θ
```

`θ τ D x = { d ∈ D | τ ∩ d.features = x }`.  The θ-fibers are pairwise
disjoint and cover D.

# Support σ

The *support* of a pattern p is the set of exemplars whose feature set
_contains_ p — those that are "activated" when the algorithm queries pattern p:

```lean
#check @σ
```

`σ D p = { d ∈ D | p ⊆ d.features }`.  Support is anti-monotone: a larger
pattern p has fewer (or equal) supporting exemplars.

# Disagreement δ

The *disagreement* of a pattern p counts the ordered pairs of supporting
exemplars that disagree on their outcome:

```lean
#check @δ
```

`δ D p = |\{ (r, s) ∈ σ(p) × σ(p) | r.outcome ≠ s.outcome \}|`.

If all exemplars in σ(p) have the same outcome, δ(p) = 0.  Disagreement being
nonzero is the signal that a pattern is "contested."

# Homogeneity

A pattern p ⊆ τ is *homogeneous* (with respect to τ and D) if its support is
non-empty and the disagreement count does not change as we extend p within τ:
for every q with p ⊆ q ⊆ τ and σ(q) nonempty, we have δ(q) = δ(p).

```lean
#check @IsHomogeneous
```

Intuitively, p is homogeneous when "zooming in" (adding features to the
pattern) does not resolve any ambiguity.

# The Analogical Set A and the Coefficient cₓ

The *analogical set* A is the collection of all homogeneous patterns in 𝒫(τ):

```lean
#check @analogicalSet
```

For each x ∈ M, the *coefficient* `c τ D x` counts how many sub-patterns of x
are homogeneous:

```lean
#check @c
```

`c τ D x = |{ p ∈ 𝒫(x) | IsHomogeneous τ D p }|`.  Computing `c` is the hard
step — this is the #P-complete bottleneck (§4.3 of Johnsen & Johansson 2005).

# The Total Score

The total analogical score for outcome _o_ is defined in two equivalent ways.

The *direct sum* (over all homogeneous patterns):

```lean
#check @totalScoreA
```

`totalScoreA τ D o = Σ_{p ∈ A} outcomeCount(σ(p), o)`.

The *weighted sum* (the Representation Theorem):

```lean
#check @totalScore
```

`totalScore τ D o = Σ_{x ∈ M} c x · outcomeCount(θ(x), o)`.

The representation theorem (`representation_theorem`) proves these are equal.
The weighted form is computationally useful because |M| ≤ |D|, avoiding a sum
over the exponentially-large 𝒫(τ).  The hard part is computing `c`.
