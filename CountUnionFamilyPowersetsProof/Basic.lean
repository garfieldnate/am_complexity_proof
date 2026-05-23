import Mathlib

set_option linter.style.openClassical false
open Classical

variable {α : Type*} [DecidableEq α]

/-!
## Combinatorial Core of the #P-Hardness Reduction for #⋃℘

We formalize the bijection underlying the reduction from #VERTEX-COVER to
computing |⋃ᵢ ℘(Sᵢ)|:

  T ⊆ V is a vertex cover of (V, edges)
  ↔  T ∉ ⋃_{e ∈ edges} ℘(V \ e)

And therefore:

  #vertex_covers(G) = 2^|V| − |⋃_{e ∈ edges} ℘(V \ e)|

Reference: Johnsen & Johansson, "Efficient Modeling of Analogy" (2005), §4.3.
-/

/-! ### Definitions -/

/-- A **vertex cover** of a hypergraph intersects every edge. -/
def IsVertexCover (edges : Finset (Finset α)) (T : Finset α) : Prop :=
  ∀ e ∈ edges, (T ∩ e).Nonempty


/-- `⋃_{e ∈ edges} ℘(V \ e)` — the union of powersets of edge complements. -/
def unionComplementPowersets (V : Finset α) (edges : Finset (Finset α)) : Finset (Finset α) :=
  edges.biUnion (fun e => (V \ e).powerset)

/-! ### Supporting Lemma -/

/-- Every element of `unionComplementPowersets V edges` is a subset of `V`. -/
lemma unionComplementPowersets_subset (V : Finset α) (edges : Finset (Finset α)) :
    unionComplementPowersets V edges ⊆ V.powerset := by
  intro T hT
  simp only [unionComplementPowersets, Finset.mem_biUnion, Finset.mem_powerset] at hT ⊢
  obtain ⟨e, _, hTe⟩ := hT
  exact hTe.trans Finset.sdiff_subset

/-! ### Key Theorem -/

/-- **Key Lemma**: for `T ⊆ V`, `T` is a vertex cover iff `T ∉ ⋃_{e ∈ edges} ℘(V \ e)`.

Proof chain:
```
T ∈ ⋃_{e} ℘(V \ e)
  ↔  ∃ e ∈ edges, T ⊆ V \ e
  ↔  ∃ e ∈ edges, ∀ x ∈ T, x ∉ e   (using T ⊆ V)
  ↔  ∃ e ∈ edges, (T ∩ e) = ∅
  ↔  ¬ IsVertexCover edges T
```
-/
theorem isVertexCover_iff_not_mem_unionComplementPowersets
    (V : Finset α) (edges : Finset (Finset α)) {T : Finset α} (hTV : T ⊆ V) :
    IsVertexCover edges T ↔ T ∉ unionComplementPowersets V edges := by
  simp only [IsVertexCover, unionComplementPowersets, Finset.mem_biUnion, Finset.mem_powerset]
  constructor
  · -- Forward: if T hits every edge, then T ⊄ V \ e for any edge e
    intro hCover ⟨e, he, hTe⟩
    obtain ⟨x, hxInt⟩ := hCover e he
    rw [Finset.mem_inter] at hxInt
    exact (Finset.mem_sdiff.mp (hTe hxInt.1)).2 hxInt.2
  · -- Backward: if T ⊄ V \ e for all e, build an intersecting element for each edge
    intro hNotIn e he
    by_contra hEmpty
    apply hNotIn
    exact ⟨e, he, fun x hxT =>
      Finset.mem_sdiff.mpr ⟨hTV hxT, fun hxe =>
        hEmpty ⟨x, Finset.mem_inter.mpr ⟨hxT, hxe⟩⟩⟩⟩

/-! ### Partition and Counting -/

/-- Vertex covers and the union of complement powersets are disjoint. -/
lemma vertexCovers_disjoint (V : Finset α) (edges : Finset (Finset α)) :
    Disjoint (V.powerset.filter (IsVertexCover edges)) (unionComplementPowersets V edges) := by
  rw [Finset.disjoint_left]
  intro T hTf hTu
  have hTV : T ⊆ V := Finset.mem_powerset.mp (Finset.mem_filter.mp hTf).1
  have hVC  : IsVertexCover edges T := (Finset.mem_filter.mp hTf).2
  exact (isVertexCover_iff_not_mem_unionComplementPowersets V edges hTV).mp hVC hTu

/-- Vertex covers and the union of complement powersets together cover all of `V.powerset`. -/
lemma vertexCovers_union_eq (V : Finset α) (edges : Finset (Finset α)) :
    V.powerset.filter (IsVertexCover edges) ∪ unionComplementPowersets V edges = V.powerset := by
  ext T
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro (⟨hTV, _⟩ | hTu)
    · exact hTV
    · exact Finset.mem_powerset.mp (unionComplementPowersets_subset V edges hTu)
  · intro hTV
    by_cases h : IsVertexCover edges T
    · exact Or.inl ⟨hTV, h⟩
    · apply Or.inr
      by_contra hNotIn
      exact h ((isVertexCover_iff_not_mem_unionComplementPowersets V edges hTV).mpr hNotIn)

/-- **Counting Equation**:
    `#vertex_covers(G) + |⋃_{e ∈ E} ℘(V \ e)| = 2^|V|`

This is the identity that makes the #P-hardness reduction work:
if we can compute `|⋃_{e ∈ E} ℘(V \ e)|`, we recover `#VERTEX-COVER` by subtraction. -/
theorem counting_equation (V : Finset α) (edges : Finset (Finset α)) :
    (V.powerset.filter (IsVertexCover edges)).card +
    (unionComplementPowersets V edges).card = 2 ^ V.card := by
  rw [← Finset.card_union_of_disjoint (vertexCovers_disjoint V edges),
      vertexCovers_union_eq, Finset.card_powerset]
