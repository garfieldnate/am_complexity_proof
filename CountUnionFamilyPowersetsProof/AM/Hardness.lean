import CountUnionFamilyPowersetsProof.AM.Propositions
import CountUnionFamilyPowersetsProof.Basic

set_option linter.style.openClassical false
open Classical

/-!
## Analogical Modeling — #P-Hardness via Reduction from #⋃℘

Given a #⋃℘ instance {S₁,...,Sₖ} ⊆ Finset (Fin n), construct:
  - τ   = Finset.univ : Finset (Fin (n+1))
  - d₀  : features = embedFin (Finset.univ : Finset (Fin n)), outcome = 0
  - dᵢ S: features = embedFin S ∪ {freshFeature n},            outcome = 1

Main result: totalScore τ D 0 = 2^n − |⋃ᵢ ℘(embedFin Sᵢ)|.
Therefore |⋃ᵢ ℘(Sᵢ)| is recoverable from totalScore in polynomial time:
  #⋃℘ ≤_T exact-AM-scoring, so exact AM is #P-hard.
-/

/-! ### Database Construction -/

def embedFin {n : ℕ} (S : Finset (Fin n)) : Finset (Fin (n + 1)) :=
  S.image Fin.castSucc

def freshFeature (n : ℕ) : Fin (n + 1) := Fin.last n

def testExemplar (n : ℕ) : Finset (Fin (n + 1)) := Finset.univ

def d₀ (n : ℕ) : Exemplar (Fin (n + 1)) (Fin 2) where
  features := embedFin (Finset.univ : Finset (Fin n))
  outcome  := 0

def dᵢ (n : ℕ) (S : Finset (Fin n)) : Exemplar (Fin (n + 1)) (Fin 2) where
  features := embedFin S ∪ {freshFeature n}
  outcome  := 1

noncomputable def encodeDatabase (n : ℕ) (family : Finset (Finset (Fin n))) :
    Database (Fin (n + 1)) (Fin 2) :=
  {d₀ n} ∪ family.image (dᵢ n)

/-- x_A = τ ∩ d₀.features: the "class-0 pattern" in M. -/
def x_A (n : ℕ) : Finset (Fin (n + 1)) := embedFin (Finset.univ : Finset (Fin n))

/-! ### Section A: Basic Membership -/

lemma d₀_mem (n : ℕ) (family : Finset (Finset (Fin n))) :
    d₀ n ∈ encodeDatabase n family := by
  simp [encodeDatabase]

lemma dᵢ_mem {n : ℕ} (family : Finset (Finset (Fin n))) {S : Finset (Fin n)}
    (hS : S ∈ family) : dᵢ n S ∈ encodeDatabase n family := by
  simp only [encodeDatabase, Finset.mem_union, Finset.mem_image]
  exact Or.inr ⟨S, hS, rfl⟩

lemma encodeDatabase_mem_iff {n : ℕ} (family : Finset (Finset (Fin n)))
    (e : Exemplar (Fin (n + 1)) (Fin 2)) :
    e ∈ encodeDatabase n family ↔ e = d₀ n ∨ ∃ S ∈ family, e = dᵢ n S := by
  simp [encodeDatabase, Finset.mem_image, eq_comm]

lemma d₀_outcome_ne_dᵢ (n : ℕ) (S : Finset (Fin n)) :
    (d₀ n).outcome ≠ (dᵢ n S).outcome := by
  simp [d₀, dᵢ]

/-! ### Section B: Fresh Feature and x_A -/

lemma d₀_not_fresh (n : ℕ) : freshFeature n ∉ (d₀ n).features := by
  simp only [d₀, embedFin, Finset.mem_image]
  rintro ⟨y, _, hy⟩; exact absurd hy (Fin.castSucc_ne_last y)

lemma dᵢ_has_fresh (n : ℕ) (S : Finset (Fin n)) : freshFeature n ∈ (dᵢ n S).features :=
  Finset.mem_union_right _ (Finset.mem_singleton_self _)

lemma fresh_not_in_xA (n : ℕ) : freshFeature n ∉ x_A n := by
  simp only [x_A, embedFin, Finset.mem_image]
  rintro ⟨y, _, hy⟩; exact absurd hy (Fin.castSucc_ne_last y)

/-- Every element of Fin(n+1) that is not the fresh feature lies in x_A. -/
lemma mem_xA_of_ne_fresh {n : ℕ} {x : Fin (n + 1)} (hx : x ≠ freshFeature n) :
    x ∈ x_A n := by
  simp only [x_A, embedFin, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨x.castPred hx, x.castSucc_castPred hx⟩

/-- q ⊆ Finset.univ and freshFeature n ∉ q implies q ⊆ x_A. -/
lemma sub_xA_of_no_fresh {n : ℕ} {q : Finset (Fin (n + 1))} (hn : freshFeature n ∉ q) :
    q ⊆ x_A n :=
  fun x hx => mem_xA_of_ne_fresh (fun h => hn (h ▸ hx))

lemma x_A_card (n : ℕ) : (x_A n).card = n := by
  unfold x_A embedFin
  rw [Finset.card_image_of_injective _ (Fin.castSucc_injective n), Finset.card_fin]

lemma x_A_powerset_card (n : ℕ) : (x_A n).powerset.card = 2 ^ n := by
  rw [Finset.card_powerset, x_A_card]

/-! ### Section C: Match Patterns -/

lemma testExemplar_inter_d₀ (n : ℕ) :
    testExemplar n ∩ (d₀ n).features = x_A n := by
  simp [testExemplar, d₀, x_A]

lemma testExemplar_inter_dᵢ (n : ℕ) (S : Finset (Fin n)) :
    testExemplar n ∩ (dᵢ n S).features = embedFin S ∪ {freshFeature n} := by
  simp [testExemplar, dᵢ]

lemma xA_ne_embedFin_union_fresh (n : ℕ) (S : Finset (Fin n)) :
    x_A n ≠ embedFin S ∪ {freshFeature n} := fun h =>
  fresh_not_in_xA n (h ▸ Finset.mem_union_right _ (Finset.mem_singleton_self _))

/-! ### Section D: θ-Fiber at x_A -/

lemma θ_xA (n : ℕ) (family : Finset (Finset (Fin n))) :
    θ (testExemplar n) (encodeDatabase n family) (x_A n) = {d₀ n} := by
  ext e
  simp only [mem_θ, Finset.mem_singleton]
  constructor
  · intro ⟨hmem, hpat⟩
    rw [encodeDatabase_mem_iff] at hmem
    rcases hmem with rfl | ⟨S, _, rfl⟩
    · rfl
    · rw [testExemplar_inter_dᵢ] at hpat
      exact absurd hpat.symm (xA_ne_embedFin_union_fresh n S)
  · rintro rfl
    exact ⟨d₀_mem n family, testExemplar_inter_d₀ n⟩

lemma outcomeCount_θ_xA (n : ℕ) (family : Finset (Finset (Fin n))) :
    outcomeCount (θ (testExemplar n) (encodeDatabase n family) (x_A n)) 0 = 1 := by
  rw [θ_xA, outcomeCount, Finset.filter_singleton, if_pos (show (d₀ n).outcome = (0 : Fin 2) from rfl),
    Finset.card_singleton]

lemma outcomeCount_θ_non_xA (n : ℕ) (family : Finset (Finset (Fin n))) {S : Finset (Fin n)}
    (hS : S ∈ family) :
    outcomeCount (θ (testExemplar n) (encodeDatabase n family)
      (embedFin S ∪ {freshFeature n})) 0 = 0 := by
  simp only [outcomeCount]
  apply Finset.card_eq_zero.mpr
  ext e; constructor
  · intro he
    simp only [Finset.mem_filter, mem_θ] at he
    obtain ⟨⟨hmem, hpat⟩, hout⟩ := he
    rw [encodeDatabase_mem_iff] at hmem
    rcases hmem with rfl | ⟨T, _, rfl⟩
    · rw [testExemplar_inter_d₀] at hpat
      exact absurd hpat (xA_ne_embedFin_union_fresh n S)
    · simp [dᵢ] at hout
  · intro h; simp at h

/-! ### Section E: Support Characterization -/

lemma d₀_in_σ_of_sub_xA {n : ℕ} (family : Finset (Finset (Fin n)))
    {p : Finset (Fin (n + 1))} (hp : p ⊆ x_A n) :
    d₀ n ∈ σ (encodeDatabase n family) p := by
  rw [mem_σ]
  exact ⟨d₀_mem n family, hp.trans (by simp [x_A, d₀])⟩

/-- For p ⊆ x_A, dᵢ S ∈ σ(p) iff p ⊆ embedFin S.
    Key: since freshFeature n ∉ x_A, p can't reach n, so
    p ⊆ embedFin S ∪ {n} iff p ⊆ embedFin S. -/
lemma dᵢ_in_σ_iff {n : ℕ} (family : Finset (Finset (Fin n)))
    {p : Finset (Fin (n + 1))} (hp : p ⊆ x_A n)
    {S : Finset (Fin n)} (hS : S ∈ family) :
    dᵢ n S ∈ σ (encodeDatabase n family) p ↔ p ⊆ embedFin S := by
  rw [mem_σ]
  constructor
  · intro ⟨_, hpd⟩
    -- hpd : p ⊆ embedFin S ∪ {freshFeature n}
    intro x hx
    rcases Finset.mem_union.mp (hpd hx) with h | h
    · exact h
    · -- x = freshFeature n, but x ∈ p ⊆ x_A and freshFeature n ∉ x_A
      exact absurd (hp hx) (Finset.mem_singleton.mp h ▸ fresh_not_in_xA n)
  · intro hpS
    exact ⟨dᵢ_mem family hS, hpS.trans (Finset.subset_union_left)⟩

/-! ### Section F: δ Lemmas -/

/-- If two exemplars in σ(m) have different outcomes, δ(m) > 0. -/
lemma δ_pos_of_disagreeing {α β : Type*} [DecidableEq α] [DecidableEq β]
    {D : Database α β} {m : Finset α} {r s : Exemplar α β}
    (hr : r ∈ σ D m) (hs : s ∈ σ D m) (hne : r.outcome ≠ s.outcome) : 0 < δ D m := by
  rw [Nat.pos_iff_ne_zero]
  intro heq
  exact hne (δ_eq_zero_iff.mp heq r hr s hs)

/-- When freshFeature n ∈ q, d₀ is not in σ(q) (since freshFeature n ∉ d₀.features). -/
lemma d₀_not_in_σ_if_fresh {n : ℕ} (family : Finset (Finset (Fin n)))
    {q : Finset (Fin (n + 1))} (hq : freshFeature n ∈ q) :
    d₀ n ∉ σ (encodeDatabase n family) q := by
  rw [mem_σ]; push Not
  intro _; exact fun hsub => absurd (hsub hq) (d₀_not_fresh n)

/-- When freshFeature n ∈ q, all exemplars in σ(q) have outcome 1, so δ(q) = 0. -/
lemma δ_zero_of_fresh_in_q {n : ℕ} (family : Finset (Finset (Fin n)))
    {q : Finset (Fin (n + 1))} (hq : freshFeature n ∈ q) :
    δ (encodeDatabase n family) q = 0 := by
  rw [δ_eq_zero_iff]
  intro r hr s hs
  -- r, s ∈ encodeDatabase and q ⊆ r.features (resp. s.features)
  -- d₀ is excluded (since freshFeature n ∈ q ⊆ r.features but n ∉ d₀.features)
  have hr_mem := (mem_σ.mp hr).1
  have hs_mem := (mem_σ.mp hs).1
  have hr_not_d₀ : r ≠ d₀ n := by
    intro h; exact absurd (h ▸ (mem_σ.mp hr).2 hq) (d₀_not_fresh n)
  have hs_not_d₀ : s ≠ d₀ n := by
    intro h; exact absurd (h ▸ (mem_σ.mp hs).2 hq) (d₀_not_fresh n)
  rw [encodeDatabase_mem_iff] at hr_mem hs_mem
  rcases hr_mem with rfl | ⟨Sr, _, rfl⟩
  · exact absurd rfl hr_not_d₀
  rcases hs_mem with rfl | ⟨Ss, _, rfl⟩
  · exact absurd rfl hs_not_d₀
  -- Both r = dᵢ Sr and s = dᵢ Ss have outcome 1
  simp [dᵢ]

/-! ### Section G: Homogeneity Characterization -/

/-- **Key Theorem**: p ⊆ x_A is homogeneous iff no Sᵢ contains p (as embedded sets).
    Equivalently: p avoids ⋃ᵢ ℘(embedFin Sᵢ). -/
theorem isHomogeneous_iff {n : ℕ} (family : Finset (Finset (Fin n)))
    {p : Finset (Fin (n + 1))} (hp : p ⊆ x_A n) :
    IsHomogeneous (testExemplar n) (encodeDatabase n family) p ↔
    ∀ S ∈ family, ¬(p ⊆ embedFin S) := by
  simp only [IsHomogeneous, mem_lattice, testExemplar]
  constructor
  · -- Forward: if homogeneous, no dᵢ S is in σ(p)
    intro ⟨_, hconst⟩ S hS hpS
    -- d₀ and dᵢ S are both in σ(p), with different outcomes → δ(p) > 0
    have hd₀ : d₀ n ∈ σ (encodeDatabase n family) p := d₀_in_σ_of_sub_xA family hp
    have hdᵢ : dᵢ n S ∈ σ (encodeDatabase n family) p :=
      (dᵢ_in_σ_iff family hp hS).mpr hpS
    have hδp_pos : 0 < δ (encodeDatabase n family) p :=
      δ_pos_of_disagreeing hd₀ hdᵢ (d₀_outcome_ne_dᵢ n S)
    -- Let q = p ∪ {freshFeature n}: p ⊆ q, dᵢ S ∈ σ(q) (since p ⊆ embedFin S and n ∈ q)
    set q := p ∪ {freshFeature n} with hq_def
    have hq_sub_τ : q ⊆ Finset.univ := Finset.subset_univ _
    have hpq : p ⊆ q := Finset.subset_union_left
    have hfresh_q : freshFeature n ∈ q := Finset.mem_union_right _ (Finset.mem_singleton_self _)
    have hq_ne : (σ (encodeDatabase n family) q).Nonempty :=
      ⟨dᵢ n S, mem_σ.mpr ⟨dᵢ_mem family hS, by
        rw [hq_def]
        exact Finset.union_subset (hpS.trans Finset.subset_union_left) Finset.subset_union_right⟩⟩
    -- δ(q) = 0 (all of σ(q) has outcome 1)
    have hδq_zero : δ (encodeDatabase n family) q = 0 :=
      δ_zero_of_fresh_in_q family hfresh_q
    -- By homogeneity: δ(q) = δ(p)
    have hδq_eq : δ (encodeDatabase n family) q = δ (encodeDatabase n family) p :=
      hconst q hq_sub_τ hpq hq_ne
    -- But δ(q) = 0 and δ(p) > 0, contradiction
    linarith [hδp_pos, hδq_zero, hδq_eq]
  · -- Backward: if no dᵢ in σ(p), then p is homogeneous
    intro hno
    -- σ(p) = {d₀}: only d₀ is in the support
    have hσ_only_d₀ : ∀ e ∈ σ (encodeDatabase n family) p, e = d₀ n := by
      intro e he
      have hemem := (mem_σ.mp he).1
      rw [encodeDatabase_mem_iff] at hemem
      rcases hemem with rfl | ⟨S, hS, rfl⟩
      · rfl
      · exact absurd ((dᵢ_in_σ_iff family hp hS).mp he) (hno S hS)
    -- δ(p) = 0 (all exemplars in σ(p) agree on outcome)
    have hδp_zero : δ (encodeDatabase n family) p = 0 := by
      rw [δ_eq_zero_iff]; intro r hr s hs
      rw [hσ_only_d₀ r hr, hσ_only_d₀ s hs]
    refine ⟨⟨d₀ n, d₀_in_σ_of_sub_xA family hp⟩, fun q hqτ hpq hqne => ?_⟩
    -- Show δ(q) = δ(p) = 0 for any superset q ∈ ℘(τ) with non-empty support
    rw [hδp_zero]
    by_cases hn : freshFeature n ∈ q
    · -- Case n ∈ q: d₀ ∉ σ(q), all of σ(q) has outcome 1, δ(q) = 0
      exact δ_zero_of_fresh_in_q family hn
    · -- Case n ∉ q: q ⊆ x_A, so σ(q) ⊆ {d₀}
      have hq_sub_xA : q ⊆ x_A n := sub_xA_of_no_fresh hn
      rw [δ_eq_zero_iff]; intro r hr s hs
      have hσ_q_only_d₀ : ∀ e ∈ σ (encodeDatabase n family) q, e = d₀ n := by
        intro e he
        have hemem := (mem_σ.mp he).1
        rw [encodeDatabase_mem_iff] at hemem
        rcases hemem with rfl | ⟨S, hS, rfl⟩
        · rfl
        · -- dᵢ S ∈ σ(q) → q ⊆ embedFin S → p ⊆ q ⊆ embedFin S → contradicts hno
          exact absurd (hpq.trans ((dᵢ_in_σ_iff family hq_sub_xA hS).mp he)) (hno S hS)
      rw [hσ_q_only_d₀ r hr, hσ_q_only_d₀ s hs]

/-! ### Section H: Counting c_{x_A} -/

/-- The homogeneous powerset count at x_A equals the count of subsets of x_A
    that avoid all embedFin Sᵢ. -/
theorem c_xA_eq_card_avoiding {n : ℕ} (family : Finset (Finset (Fin n))) :
    c (testExemplar n) (encodeDatabase n family) (x_A n) =
    (x_A n |>.powerset.filter (fun p => ∀ S ∈ family, ¬(p ⊆ embedFin S))).card := by
  simp only [c]
  congr 1; ext p
  simp only [Finset.mem_filter, Finset.mem_powerset]
  constructor
  · intro ⟨hpx, hHom⟩
    exact ⟨hpx, (isHomogeneous_iff family hpx).mp hHom⟩
  · intro ⟨hpx, hno⟩
    exact ⟨hpx, (isHomogeneous_iff family hpx).mpr hno⟩

/-- The complement: subsets of x_A that DO hit some Sᵢ form the "union of powersets". -/
def unionEmbeddedPowersets {n : ℕ} (family : Finset (Finset (Fin n))) :
    Finset (Finset (Fin (n + 1))) :=
  family.biUnion (fun S => (embedFin S).powerset)

/-- **c_{x_A} counting equation**: c_{x_A} + |⋃ᵢ ℘(embedFin Sᵢ)| = 2^n. -/
theorem c_xA_counting {n : ℕ} (family : Finset (Finset (Fin n))) :
    c (testExemplar n) (encodeDatabase n family) (x_A n) +
    (unionEmbeddedPowersets family).card = 2 ^ n := by
  rw [c_xA_eq_card_avoiding, ← x_A_powerset_card]
  -- The "avoiding" filter and the biUnion partition x_A.powerset
  set A := (x_A n).powerset.filter (fun p => ∀ S ∈ family, ¬(p ⊆ embedFin S))
  set B := unionEmbeddedPowersets family ∩ (x_A n).powerset
  have hpart : A ∪ B = (x_A n).powerset := by
    ext p
    simp only [A, B, Finset.mem_union, Finset.mem_filter, Finset.mem_powerset, Finset.mem_inter,
               unionEmbeddedPowersets, Finset.mem_biUnion]
    constructor
    · rintro (⟨h, _⟩ | ⟨_, h⟩) <;> exact h
    · intro hp
      by_cases h : ∀ S ∈ family, ¬(p ⊆ embedFin S)
      · exact Or.inl ⟨hp, h⟩
      · push Not at h
        obtain ⟨S, hS, hpS⟩ := h
        exact Or.inr ⟨⟨S, hS, hpS⟩, hp⟩
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro p hp hq
    simp only [A, Finset.mem_filter] at hp
    simp only [B, Finset.mem_inter, unionEmbeddedPowersets, Finset.mem_biUnion,
               Finset.mem_powerset] at hq
    obtain ⟨⟨S, hS, hpS⟩, _⟩ := hq
    exact hp.2 S hS hpS
  have hcard := Finset.card_union_of_disjoint hdisj
  have huniv_card : B.card = (unionEmbeddedPowersets family).card := by
    have hB_eq : B = unionEmbeddedPowersets family := by
      simp only [B]
      apply Finset.inter_eq_left.mpr
      intro p hp
      simp only [Finset.mem_powerset]
      simp only [unionEmbeddedPowersets, Finset.mem_biUnion, Finset.mem_powerset] at hp
      obtain ⟨S, _, hpS⟩ := hp
      exact hpS.trans (fun x hx => by
        simp only [embedFin, Finset.mem_image] at hx
        obtain ⟨y, _, rfl⟩ := hx
        exact mem_xA_of_ne_fresh (Fin.castSucc_ne_last y))
    rw [hB_eq]
  rw [hpart] at hcard
  linarith [huniv_card]

/-! ### Section I: Score Computation -/

/-- In the constructed database, the match set M = {x_A} ∪ {embedFin S ∪ {n} | S ∈ family}. -/
lemma matchSet_encodeDatabase (n : ℕ) (family : Finset (Finset (Fin n))) :
    matchSet (testExemplar n) (encodeDatabase n family) =
    {x_A n} ∪ family.image (fun S => embedFin S ∪ {freshFeature n}) := by
  ext x
  simp only [mem_matchSet, Finset.mem_union, Finset.mem_singleton, Finset.mem_image]
  constructor
  · rintro ⟨e, hemem, rfl⟩
    rw [encodeDatabase_mem_iff] at hemem
    rcases hemem with rfl | ⟨S, hS, rfl⟩
    · exact Or.inl (testExemplar_inter_d₀ n)
    · exact Or.inr ⟨S, hS, (testExemplar_inter_dᵢ n S).symm⟩
  · rintro (rfl | ⟨S, hS, rfl⟩)
    · exact ⟨d₀ n, d₀_mem n family, testExemplar_inter_d₀ n⟩
    · exact ⟨dᵢ n S, dᵢ_mem family hS, testExemplar_inter_dᵢ n S⟩

/-- The total score for outcome 0 equals c_{x_A} (the x_i fibers all have outcomeCount 0). -/
theorem totalScore_eq_c_xA {n : ℕ} (family : Finset (Finset (Fin n))) :
    totalScore (testExemplar n) (encodeDatabase n family) 0 =
    c (testExemplar n) (encodeDatabase n family) (x_A n) := by
  simp only [totalScore, matchSet_encodeDatabase]
  rw [Finset.sum_union]
  · -- {x_A} contributes c_{x_A} * outcomeCount(θ(x_A), 0) = c_{x_A} * 1 = c_{x_A}
    simp only [Finset.sum_singleton, outcomeCount_θ_xA]
    -- family.image (...) contributes 0 for each S (all θ(x_i) have outcomeCount 0)
    suffices h : (family.image (fun S => embedFin S ∪ {freshFeature n})).sum
        (fun x => c (testExemplar n) (encodeDatabase n family) x *
          outcomeCount (θ (testExemplar n) (encodeDatabase n family) x) 0) = 0 by
      rw [h]; ring
    apply Finset.sum_eq_zero
    intro x hx
    simp only [Finset.mem_image] at hx
    obtain ⟨S, hS, rfl⟩ := hx
    rw [outcomeCount_θ_non_xA n family hS, Nat.mul_zero]
  · -- Disjointness: x_A ∉ family.image (...)
    simp only [Finset.disjoint_left, Finset.mem_singleton, Finset.mem_image]
    rintro x rfl ⟨S, _, hS⟩
    exact xA_ne_embedFin_union_fresh n S hS.symm

/-! ### Section J: Main Hardness Theorem -/

/-- **#P-Hardness of Exact AM Scoring**:

    The constructed database encodes the #⋃℘ counting problem:
      totalScore τ D 0 + |⋃ᵢ ℘(embedFin Sᵢ)| = 2^n

    Given the oracle `totalScore τ D 0`, one recovers |⋃ᵢ ℘(Sᵢ)| = 2^n - totalScore.
    This is polynomial-time computable, establishing #⋃℘ ≤_T exact-AM-scoring.

    Combined with Basic.lean (which proves #VERTEX-COVER ≤ #⋃℘ and #⋃℘ is #P-complete),
    we conclude exact AM scoring is #P-hard. -/
theorem exact_AM_scoring_is_hard (n : ℕ) (family : Finset (Finset (Fin n))) :
    totalScore (testExemplar n) (encodeDatabase n family) 0 +
    (unionEmbeddedPowersets family).card = 2 ^ n := by
  rw [totalScore_eq_c_xA]
  exact c_xA_counting family
