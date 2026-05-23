import CountUnionFamilyPowersetsProof.AM.Homogeneity

set_option linter.style.openClassical false
open Classical

/-!
## Analogical Modeling — Scoring

Formalizes the scoring mechanism from Johnsen & Johansson (2005), §3–4.

Key objects:
- `outcomeCount D o`  — number of exemplars in D with outcome o
- `c τ D x`          — c_x: |{p ∈ ℘(x) | p is homogeneous in τ}|
                       (counts how many lattice subsets of x are homogeneous)
- `scoreθ τ D x`     — the score contribution of the θ-fiber over x:
                       (c_x, outcomeCount (θ τ D x) o) for each outcome o
- `totalScore τ D o` — Σ_{x ∈ M} c_x · |{d ∈ θ(x) | d.outcome = o}|
                       (Theorem 1 from the paper)
-/

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-! ### Outcome Counting -/

/-- Number of exemplars in a set with a given outcome. -/
def outcomeCount (S : Finset (Exemplar α β)) (o : β) : ℕ :=
  (S.filter (fun d => d.outcome = o)).card

@[simp]
lemma outcomeCount_empty (o : β) : outcomeCount (∅ : Finset (Exemplar α β)) o = 0 := by
  simp [outcomeCount]

lemma outcomeCount_le_card (S : Finset (Exemplar α β)) (o : β) :
    outcomeCount S o ≤ S.card :=
  Finset.card_filter_le _ _

/-! ### c_x: The Homogeneous Powerset Count -/

/-- c_x = |{p ∈ ℘(x) | IsHomogeneous τ D p}|: the number of subsets of x
    that are homogeneous in (τ, D).

    This is the weight used in the representation theorem (Theorem 1). -/
noncomputable def c (τ : Finset α) (D : Database α β) (x : Finset α) : ℕ :=
  (x.powerset.filter (IsHomogeneous τ D)).card

/-- c_x ≤ 2^|x|: bounded by the total number of subsets. -/
lemma c_le_pow (τ : Finset α) (D : Database α β) (x : Finset α) :
    c τ D x ≤ 2 ^ x.card := by
  calc c τ D x = (x.powerset.filter (IsHomogeneous τ D)).card := rfl
    _ ≤ x.powerset.card := Finset.card_filter_le _ _
    _ = 2 ^ x.card := Finset.card_powerset _

/-- c_∅ counts homogeneous subsets of ∅: at most 1 (only ∅ itself). -/
lemma c_empty_le_one (τ : Finset α) (D : Database α β) : c τ D ∅ ≤ 1 := by
  simp only [c, Finset.powerset_empty]
  calc (Finset.filter (IsHomogeneous τ D) {∅}).card
      ≤ ({∅} : Finset (Finset α)).card := Finset.card_filter_le _ _
    _ = 1 := Finset.card_singleton _

/-! ### Total Score (Theorem 1) -/

/-- The **total analogical score** for outcome o:
    tot(o) = Σ_{x ∈ M} c_x · |{d ∈ θ(x) | d.outcome = o}|

    This is Theorem 1 from Johnsen & Johansson (2005):
    the sum over lattice elements in the analogical set can be
    reorganized as a sum over the (much smaller) match set M. -/
noncomputable def totalScore (τ : Finset α) (D : Database α β) (o : β) : ℕ :=
  (matchSet τ D).sum (fun x => c τ D x * outcomeCount (θ τ D x) o)

/-! ### Alternative via the Analogical Set -/

/-- The analogical set version of the total score:
    Σ_{p ∈ A} |{d ∈ σ(p) | d.outcome = o}|

    This is the definition-side form; Theorem 1 says it equals `totalScore`. -/
noncomputable def totalScoreA (τ : Finset α) (D : Database α β) (o : β) : ℕ :=
  (analogicalSet τ D).sum (fun p => outcomeCount (σ D p) o)

/-! ### Basic Properties -/

/-- totalScore is non-negative (trivially, as it's a natural number). -/
lemma totalScore_nonneg (τ : Finset α) (D : Database α β) (o : β) :
    0 ≤ totalScore τ D o := Nat.zero_le _

/-- If the match set is empty (no database exemplars), the total score is 0. -/
@[simp]
lemma totalScore_empty_matchSet (τ : Finset α) (o : β) :
    totalScore τ (∅ : Database α β) o = 0 := by
  simp [totalScore, matchSet]
