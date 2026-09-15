import Erdos811Definitions
import CyclicDifference
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.GroupTheory.Perm.DomMulAct

/-!
# Finite first-moment and orbit bookkeeping for the q≥12 construction

The numerical estimate in `ProbabilisticBound` is only useful after two finite
combinatorial facts have been supplied: a bad sample comes in whole translation
orbits, and a sample has either no bad orbit or at least `N` of them. This file
records the pairing-space and orbit interfaces as small, reusable lemmas; the
concrete cyclic instantiation and its expected-value bound are completed in
`ProbabilisticBound`.
-/

namespace Erdos811

structure PairingMap (D C : Type*) [Fintype D] [Fintype C]
    [DecidableEq D] [DecidableEq C] where
  color : D → C
  fiber_card : ∀ c : C,
    ((Finset.univ : Finset D).filter (fun d => color d = c)).card = 2

/- A canonical pairing of a set of `m * 2` edge-difference classes.  The
second coordinate of `Fin.finProdFinEquiv` is the member of the pair.  Keeping
this construction explicit is useful later: a random pairing is just a
permutation followed by this fixed map. -/
def canonicalPairingColor (m : ℕ) (d : Fin (m * 2)) : Fin m :=
  (finProdFinEquiv.symm d).1

def canonicalPairingMap (m : ℕ) :
    PairingMap (Fin (m * 2)) (Fin m) where
  color := canonicalPairingColor m
  fiber_card := by
    intro c
    let s : Finset (Fin (m * 2)) :=
      (Finset.univ : Finset (Fin (m * 2))).filter
        (fun d => canonicalPairingColor m d = c)
    let t : Finset (Fin 2) := Finset.univ
    have hcard : s.card = t.card := by
      apply Finset.card_bij
        (fun d _ => (finProdFinEquiv.symm d).2)
      · intro d hd
        simp [t]
      · intro d₁ hd₁ d₂ hd₂ heq
        have hc₁ : (finProdFinEquiv.symm d₁).1 = c := by
          simpa [s, canonicalPairingColor] using (Finset.mem_filter.1 hd₁).2
        have hc₂ : (finProdFinEquiv.symm d₂).1 = c := by
          simpa [s, canonicalPairingColor] using (Finset.mem_filter.1 hd₂).2
        have hp : finProdFinEquiv.symm d₁ =
            finProdFinEquiv.symm d₂ := by
          exact Prod.ext (hc₁.trans hc₂.symm) heq
        calc
          d₁ = finProdFinEquiv (finProdFinEquiv.symm d₁) :=
            (finProdFinEquiv.apply_symm_apply d₁).symm
          _ = finProdFinEquiv (finProdFinEquiv.symm d₂) := congrArg _ hp
          _ = d₂ := finProdFinEquiv.apply_symm_apply d₂
      · intro j hj
        refine ⟨finProdFinEquiv (c, j), ?_, ?_⟩
        · have hmk : finProdFinEquiv (c, j) = Fin.mkDivMod c j := by
            apply Fin.ext
            simp [finProdFinEquiv, Fin.mkDivMod]
            omega
          rw [hmk]
          simpa [s, canonicalPairingColor] using Fin.divNat_mkDivMod c j
        · have hmk : finProdFinEquiv (c, j) = Fin.mkDivMod c j := by
            apply Fin.ext
            simp [finProdFinEquiv, Fin.mkDivMod]
            omega
          rw [hmk]
          simpa using Fin.modNat_mkDivMod c j
    simpa [s, t] using hcard

/- A random pairing is obtained by first permuting the `m * 2` difference
classes and then applying the canonical adjacent-pair map.  The permutation
does not change any fibre cardinality. -/
def permutationPairingMap (m : ℕ) (σ : Equiv.Perm (Fin (m * 2))) :
    PairingMap (Fin (m * 2)) (Fin m) where
  color d := canonicalPairingColor m (σ d)
  fiber_card := by
    intro c
    let s : Finset (Fin (m * 2)) :=
      (Finset.univ : Finset (Fin (m * 2))).filter
        (fun d => canonicalPairingColor m (σ d) = c)
    let t : Finset (Fin (m * 2)) :=
      (Finset.univ : Finset (Fin (m * 2))).filter
        (fun d => canonicalPairingColor m d = c)
    have hcard : s.card = t.card := by
      apply Finset.card_bij'
        (fun d _ => σ d) (fun d _ => σ.symm d)
      · intro d hd
        simp [s, t] at hd ⊢
        exact hd
      · intro d hd
        simp [s, t] at hd ⊢
        exact hd
      · intro d hd
        simp
      · intro d hd
        simp
    have ht : t.card = 2 := by
      simpa [t, canonicalPairingMap, canonicalPairingColor] using
        (canonicalPairingMap m).fiber_card c
    simpa [s] using hcard.trans ht

/- The same random pairing construction with an arbitrary finite type of
   difference classes.  The equivalence `e` transports those classes to the
   canonical `Fin (m*2)` model; this is the interface used by the cyclic
   difference coloring. -/
def permutationPairingMapOfEquiv
    {D : Type*} [Fintype D] [DecidableEq D]
    (m : ℕ) (e : D ≃ Fin (m * 2))
    (σ : Equiv.Perm (Fin (m * 2))) : PairingMap D (Fin m) where
  color d := canonicalPairingColor m (σ (e d))
  fiber_card := by
    intro c
    let s : Finset D :=
      (Finset.univ : Finset D).filter
        (fun d => canonicalPairingColor m (σ (e d)) = c)
    let t : Finset (Fin (m * 2)) :=
      (Finset.univ : Finset (Fin (m * 2))).filter
        (fun d => canonicalPairingColor m (σ d) = c)
    have hcard : s.card = t.card := by
      apply Finset.card_bij' (fun d _ => e d) (fun d _ => e.symm d)
      · intro d hd
        simp [s, t] at hd ⊢
        exact hd
      · intro d hd
        simp [s, t] at hd ⊢
        exact hd
      · intro d hd
        simp
      · intro d hd
        simp
    have ht : t.card = 2 := by
      change ((Finset.univ : Finset (Fin (m * 2))).filter
        (fun d => canonicalPairingColor m (σ d) = c)).card = 2
      exact (permutationPairingMap m σ).fiber_card c
    simpa [s] using hcard.trans ht

@[simp] lemma card_permutation_sample (m : ℕ) :
    Fintype.card (Equiv.Perm (Fin (m * 2))) = Nat.factorial (m * 2) := by
  simp [Fintype.card_perm]

/- The canonical adjacent-pair model exposes the pair index and the
orientation bit of a difference class.  These small definitions keep the
finite counting argument below independent of the particular base coloring. -/
def pairingPairIndex (m : ℕ) (d : Fin (m * 2)) : Fin m :=
  (finProdFinEquiv.symm d).1

def pairingPairOrientation (m : ℕ) (d : Fin (m * 2)) : Fin 2 :=
  (finProdFinEquiv.symm d).2

def PairSeparated (m : ℕ) (e : Fin m ↪ Fin (m * 2))
    (σ : Equiv.Perm (Fin (m * 2))) : Prop :=
  Function.Injective (fun i : Fin m =>
      pairingPairIndex m (σ (e i)))

lemma permutationPairingMap_color_eq_pairingPairIndex
    (m : ℕ) (σ : Equiv.Perm (Fin (m * 2))) (d : Fin (m * 2)) :
    (permutationPairingMap m σ).color d = pairingPairIndex m (σ d) := by
  rfl

lemma permutationPairingMap_color_injective_iff_pairSeparated
    (m : ℕ) (e : Fin m ↪ Fin (m * 2))
    (σ : Equiv.Perm (Fin (m * 2))) :
    Function.Injective (fun i : Fin m =>
      (permutationPairingMap m σ).color (e i)) ↔
      PairSeparated m e σ := by
  rfl

def pairingMemIndicator {α : Type*} [DecidableEq α]
    (A : Finset α) : α → Fin 2 :=
  fun x => if x ∈ A then 0 else 1

def pairingPermPreservesFinset {α : Type*} [DecidableEq α]
    (A B : Finset α) (σ : Equiv.Perm α) : Prop :=
  ∀ x, x ∈ A ↔ σ x ∈ B

lemma pairingPermPreservesFinset_iff_image
    {α : Type*} [DecidableEq α]
    (A B : Finset α) (σ : Equiv.Perm α) :
    pairingPermPreservesFinset A B σ ↔ A.image σ = B := by
  constructor
  · intro h
    ext y
    constructor
    · intro hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      exact (h x).mp hx
    · intro hy
      have hpre : σ.symm y ∈ A := by
        apply (h (σ.symm y)).mpr
        simpa using hy
      exact Finset.mem_image.mpr ⟨σ.symm y, hpre, by simp⟩
  · intro himage x
    constructor
    · intro hx
      have hx' : σ x ∈ A.image σ :=
        Finset.mem_image.mpr ⟨x, hx, rfl⟩
      simpa [himage] using hx'
    · intro hx
      have hx' : σ x ∈ A.image σ := by
        rw [himage]
        exact hx
      obtain ⟨y, hy, hyeq⟩ := Finset.mem_image.mp hx'
      have hyx : y = x := σ.injective hyeq
      simpa [hyx] using hy

noncomputable instance pairingPermPreservesFinsetFintype
    {α : Type*} [Fintype α] [DecidableEq α]
    (A B : Finset α) :
    Fintype {σ : Equiv.Perm α // pairingPermPreservesFinset A B σ} := by
  classical
  exact Fintype.subtype
    (Finset.univ.filter (fun σ => pairingPermPreservesFinset A B σ)) (by simp)

lemma pairing_indicatorFin_preserves_iff {α : Type*} [DecidableEq α]
    (A : Finset α) (σ : Equiv.Perm α) :
    (pairingMemIndicator A) ∘ σ = pairingMemIndicator A ↔
      pairingPermPreservesFinset A A σ := by
  constructor
  · intro h x
    have hx := congrFun h x
    change (if σ x ∈ A then 0 else 1) = (if x ∈ A then 0 else 1) at hx
    by_cases hxa : x ∈ A
    · by_cases hσa : σ x ∈ A
      · simp [hxa, hσa]
      · exfalso
        have h01 : (0 : Fin 2) = 1 := by simpa [hxa, hσa] using hx
        exact zero_ne_one h01
    · by_cases hσa : σ x ∈ A
      · exfalso
        have h10 : (1 : Fin 2) = 0 := by simpa [hxa, hσa] using hx
        exact one_ne_zero h10
      · simp [hxa, hσa]
  · intro h
    funext x
    change (if σ x ∈ A then 0 else 1) = (if x ∈ A then 0 else 1)
    by_cases hxa : x ∈ A
    · by_cases hσa : σ x ∈ A
      · simp [hxa, hσa]
      · exact False.elim (hσa ((h x).mp hxa))
    · by_cases hσa : σ x ∈ A
      · exact False.elim (hxa ((h x).mpr hσa))
      · simp [hxa, hσa]

lemma card_pairingPermPreservesFinset
    {α : Type*} [Fintype α] [DecidableEq α]
    (A : Finset α) :
    Fintype.card {σ : Equiv.Perm α // pairingPermPreservesFinset A A σ} =
      A.card.factorial * Aᶜ.card.factorial := by
  classical
  let f := pairingMemIndicator A
  have heq : {σ : Equiv.Perm α // pairingPermPreservesFinset A A σ} ≃
      {σ : Equiv.Perm α // f ∘ σ = f} := by
    apply Equiv.subtypeEquiv (Equiv.refl _)
    intro σ
    exact (pairing_indicatorFin_preserves_iff A σ).symm
  rw [Fintype.card_congr heq]
  rw [DomMulAct.stabilizer_card f]
  have h0 : Fintype.card {a : α // f a = (0 : Fin 2)} = A.card := by
    have e0 : {a : α // f a = (0 : Fin 2)} ≃ {a : α // a ∈ A} := by
      apply Equiv.subtypeEquiv (Equiv.refl _)
      intro a
      simp [f, pairingMemIndicator]
    rw [Fintype.card_congr e0]
    simp [Fintype.card_subtype]
  have h1 : Fintype.card {a : α // f a = (1 : Fin 2)} = Aᶜ.card := by
    have e1 : {a : α // f a = (1 : Fin 2)} ≃ {a : α // a ∉ A} := by
      apply Equiv.subtypeEquiv (Equiv.refl _)
      intro a
      simp [f, pairingMemIndicator]
    rw [Fintype.card_congr e1]
    rw [Fintype.card_subtype_compl, Fintype.card_subtype]
    simp [Finset.card_compl]
  rw [Fin.prod_univ_two, h0, h1]

noncomputable def pairingPermMapsEquiv
    {α : Type*} [Fintype α] [DecidableEq α]
    (A B : Finset α) (ρ : Equiv.Perm α)
    (hρ : pairingPermPreservesFinset A B ρ) :
    {σ : Equiv.Perm α // pairingPermPreservesFinset A A σ} ≃
      {σ : Equiv.Perm α // pairingPermPreservesFinset A B σ} := by
  let toFun : {σ : Equiv.Perm α // pairingPermPreservesFinset A A σ} →
      {σ : Equiv.Perm α // pairingPermPreservesFinset A B σ} := fun γ =>
    ⟨γ.val.trans ρ, by
      intro x
      simp only [Equiv.trans_apply]
      exact (γ.property x).trans (hρ (γ.val x))⟩
  let invFun : {σ : Equiv.Perm α // pairingPermPreservesFinset A B σ} →
      {σ : Equiv.Perm α // pairingPermPreservesFinset A A σ} := fun σ =>
    ⟨σ.val.trans ρ.symm, by
      intro x
      simp only [Equiv.trans_apply]
      have hρ' := hρ (ρ.symm (σ.val x))
      simp only [Equiv.apply_symm_apply] at hρ'
      exact (σ.property x).trans hρ'.symm⟩
  refine ⟨toFun, invFun, ?_, ?_⟩
  · intro γ
    apply Subtype.ext
    ext x
    simp [toFun, invFun]
  · intro σ
    apply Subtype.ext
    ext x
    simp [toFun, invFun]

lemma card_pairingPermMapsFinset
    {α : Type*} [Fintype α] [DecidableEq α]
    (A B : Finset α) (ρ : Equiv.Perm α)
    (hρ : pairingPermPreservesFinset A B ρ) :
    Fintype.card {σ : Equiv.Perm α // pairingPermPreservesFinset A B σ} =
      A.card.factorial * Aᶜ.card.factorial := by
  calc
    Fintype.card {σ : Equiv.Perm α // pairingPermPreservesFinset A B σ} =
        Fintype.card {σ : Equiv.Perm α // pairingPermPreservesFinset A A σ} :=
      (Fintype.card_congr (pairingPermMapsEquiv A B ρ hρ)).symm
    _ = A.card.factorial * Aᶜ.card.factorial :=
      card_pairingPermPreservesFinset A

noncomputable instance pairingSeparatedFintype
    (m : ℕ) (e : Fin m ↪ Fin (m * 2)) :
    Fintype {σ : Equiv.Perm (Fin (m * 2)) // PairSeparated m e σ} :=
by
  classical
  exact Fintype.subtype
    ((Finset.univ : Finset (Equiv.Perm (Fin (m * 2)))).filter
      (fun σ => PairSeparated m e σ)) (by simp)

lemma card_fin_embedding_self (m : ℕ) :
    Fintype.card (Fin m ↪ Fin m) = Nat.factorial m := by
  rw [Fintype.card_embedding_eq, Fintype.card_fin, Nat.descFactorial_self]

lemma card_fin_fun_two (m : ℕ) :
    Fintype.card (Fin m → Fin 2) = 2 ^ m := by
  simp [Fintype.card_fun]

lemma card_pairing_restriction_code (m : ℕ) :
    Fintype.card ((Fin m ↪ Fin m) × (Fin m → Fin 2)) =
      Nat.factorial m * 2 ^ m := by
  rw [Fintype.card_prod, card_fin_embedding_self, card_fin_fun_two]

def pairingChoiceFinset (m : ℕ) (ε : Fin m → Fin 2) :
    Finset (Fin (m * 2)) :=
  (Finset.univ : Finset (Fin m)).image
    (fun i => finProdFinEquiv (i, ε i))

lemma pairingChoiceFinset_card (m : ℕ) (ε : Fin m → Fin 2) :
    (pairingChoiceFinset m ε).card = m := by
  unfold pairingChoiceFinset
  have hinj : Function.Injective (fun i : Fin m =>
      finProdFinEquiv (i, ε i)) := by
    intro i j hij
    have hp := congrArg (fun d : Fin (m * 2) =>
      (finProdFinEquiv.symm d).1) hij
    simpa using hp
  rw [Finset.card_image_of_injective _ hinj]
  simp

lemma pairingChoiceFinset_injective (m : ℕ) :
    Function.Injective (pairingChoiceFinset m) := by
  intro ε δ h
  funext i
  have hi : finProdFinEquiv (i, ε i) ∈ pairingChoiceFinset m ε := by
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  rw [h] at hi
  obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hi
  have hp : (i, ε i) = (j, δ j) := finProdFinEquiv.injective hji.symm
  have hij : i = j := congrArg Prod.fst hp
  have ho : ε i = δ j := congrArg Prod.snd hp
  simpa [hij] using ho

lemma card_pairing_choice_family (m : ℕ) :
    (Finset.univ.image (pairingChoiceFinset m)).card = 2 ^ m := by
  rw [Finset.card_image_of_injective _ (pairingChoiceFinset_injective m)]
  simp [Fintype.card_fun]

def pairingRestrictionCode (m : ℕ) (e : Fin m ↪ Fin (m * 2))
    (σ : Equiv.Perm (Fin (m * 2)))
    (hsep : PairSeparated m e σ) :
    (Fin m ↪ Fin m) × (Fin m → Fin 2) :=
  ⟨⟨fun i => pairingPairIndex m (σ (e i)), hsep⟩,
    fun i => pairingPairOrientation m (σ (e i))⟩

noncomputable def pairingPairIndexEquiv
    (m : ℕ) (e : Fin m ↪ Fin (m * 2))
    (σ : Equiv.Perm (Fin (m * 2)))
    (hsep : PairSeparated m e σ) : Fin m ≃ Fin m :=
  Equiv.ofBijective (fun i : Fin m => pairingPairIndex m (σ (e i)))
    ⟨hsep, Finite.injective_iff_surjective.mp hsep⟩

noncomputable def pairingSelectedChoice
    (m : ℕ) (e : Fin m ↪ Fin (m * 2))
    (σ : Equiv.Perm (Fin (m * 2)))
    (hsep : PairSeparated m e σ) : Fin m → Fin 2 :=
  fun j => pairingPairOrientation m
    (σ (e ((pairingPairIndexEquiv m e σ hsep).symm j)))

lemma pairingPairIndexOrientation_reconstruct
    (m : ℕ) (d : Fin (m * 2)) :
    finProdFinEquiv (pairingPairIndex m d, pairingPairOrientation m d) = d := by
  exact finProdFinEquiv.apply_symm_apply d

lemma pairingSelectedImage_eq_choice
    (m : ℕ) (e : Fin m ↪ Fin (m * 2))
    (σ : Equiv.Perm (Fin (m * 2)))
    (hsep : PairSeparated m e σ) :
    (Finset.univ.image (fun i : Fin m => σ (e i))) =
      pairingChoiceFinset m (pairingSelectedChoice m e σ hsep) := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    let p := pairingPairIndexEquiv m e σ hsep
    let j := p i
    have hji : p.symm j = i := by simp [j]
    have hrecon : finProdFinEquiv (j,
        pairingSelectedChoice m e σ hsep j) = σ (e i) := by
      change finProdFinEquiv (p i,
        pairingPairOrientation m
          (σ (e (p.symm (p i))))) = σ (e i)
      rw [p.symm_apply_apply]
      change finProdFinEquiv
        (pairingPairIndex m (σ (e i)),
          pairingPairOrientation m (σ (e i))) = σ (e i)
      exact pairingPairIndexOrientation_reconstruct m (σ (e i))
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hrecon⟩
  · intro hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    let p := pairingPairIndexEquiv m e σ hsep
    let i := p.symm j
    have hip : p i = j := by simp [i]
    have hrecon : σ (e i) = finProdFinEquiv (j,
        pairingSelectedChoice m e σ hsep j) := by
      change σ (e i) = finProdFinEquiv (j,
        pairingPairOrientation m (σ (e i)))
      rw [← hip]
      change σ (e i) = finProdFinEquiv
        (pairingPairIndex m (σ (e i)),
          pairingPairOrientation m (σ (e i)))
      exact (pairingPairIndexOrientation_reconstruct m (σ (e i))).symm
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hrecon⟩

def pairingGoodCodeType (m : ℕ) (e : Fin m ↪ Fin (m * 2)) :=
  Σ ε : Fin m → Fin 2,
    {σ : Equiv.Perm (Fin (m * 2)) //
      pairingPermPreservesFinset
        (Finset.univ.image e) (pairingChoiceFinset m ε) σ}

noncomputable instance pairingGoodCodeTypeFintype
    (m : ℕ) (e : Fin m ↪ Fin (m * 2)) : Fintype (pairingGoodCodeType m e) := by
  classical
  dsimp [pairingGoodCodeType]
  infer_instance

/- A permutation extending an equivalence between two equally-sized finite sets. -/
noncomputable def finsetPermOfCardEq
    {α : Type*} [Fintype α] [DecidableEq α]
    (A B : Finset α) (hcard : A.card = B.card) : Equiv.Perm α :=
  Equiv.extendSubtype (A.equivOfCardEq hcard)

lemma finsetPermOfCardEq_mem
    {α : Type*} [Fintype α] [DecidableEq α]
    (A B : Finset α) (hcard : A.card = B.card)
    {x : α} (hx : x ∈ A) : finsetPermOfCardEq A B hcard x ∈ B := by
  exact Equiv.extendSubtype_mem (A.equivOfCardEq hcard) x hx

lemma finsetPermOfCardEq_preserves
    {α : Type*} [Fintype α] [DecidableEq α]
    (A B : Finset α) (hcard : A.card = B.card) :
    pairingPermPreservesFinset A B (finsetPermOfCardEq A B hcard) := by
  rw [pairingPermPreservesFinset_iff_image]
  apply Finset.eq_of_subset_of_card_le
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact finsetPermOfCardEq_mem A B hcard hx
  · rw [Finset.card_image_of_injective _ (finsetPermOfCardEq A B hcard).injective]
    exact hcard.symm.le

lemma pairingGoodCodeType_card
    (m : ℕ) (e : Fin m ↪ Fin (m * 2)) :
    Fintype.card (pairingGoodCodeType m e) =
      2 ^ m * Nat.factorial m * Nat.factorial m := by
  classical
  let A : Finset (Fin (m * 2)) := Finset.univ.image e
  have hA : A.card = m := by
    dsimp [A]
    rw [Finset.card_image_of_injective _ e.injective]
    simp
  have hAc : Aᶜ.card = m := by
    rw [Finset.card_compl]
    simp [hA]
    omega
  let ρ : (Fin m → Fin 2) → Equiv.Perm (Fin (m * 2)) := fun ε =>
    finsetPermOfCardEq A (pairingChoiceFinset m ε)
      (hA.trans (pairingChoiceFinset_card m ε).symm)
  have hρ (ε : Fin m → Fin 2) :
      pairingPermPreservesFinset A (pairingChoiceFinset m ε) (ρ ε) := by
    exact finsetPermOfCardEq_preserves A (pairingChoiceFinset m ε)
      (hA.trans (pairingChoiceFinset_card m ε).symm)
  have hfiber (ε : Fin m → Fin 2) :
      Fintype.card {σ : Equiv.Perm (Fin (m * 2)) //
        pairingPermPreservesFinset A (pairingChoiceFinset m ε) σ} =
        Nat.factorial m * Nat.factorial m := by
    rw [card_pairingPermMapsFinset A (pairingChoiceFinset m ε) (ρ ε) (hρ ε)]
    rw [hA, hAc]
  change Fintype.card (Σ ε : Fin m → Fin 2,
      {σ : Equiv.Perm (Fin (m * 2)) //
        pairingPermPreservesFinset A (pairingChoiceFinset m ε) σ}) = _
  rw [Fintype.card_sigma]
  simp_rw [hfiber]
  simp [Fintype.card_fun, Nat.mul_assoc]

noncomputable def pairingGoodToCode
    (m : ℕ) (e : Fin m ↪ Fin (m * 2)) :
    {σ : Equiv.Perm (Fin (m * 2)) // PairSeparated m e σ} →
      pairingGoodCodeType m e := fun s =>
  ⟨pairingSelectedChoice m e s.1 s.2,
    ⟨s.1, (pairingPermPreservesFinset_iff_image
      (Finset.univ.image e) (pairingChoiceFinset m
        (pairingSelectedChoice m e s.1 s.2)) s.1).2 (by
      simpa [Finset.image_image, Function.comp_def] using
        pairingSelectedImage_eq_choice m e s.1 s.2)⟩⟩

lemma pairingGoodToCode_injective
    (m : ℕ) (e : Fin m ↪ Fin (m * 2)) :
    Function.Injective (pairingGoodToCode m e) := by
  intro s t h
  have hσ : s.1 = t.1 := by
    exact congrArg (fun z : pairingGoodCodeType m e => z.2.1) h
  exact Subtype.ext hσ

lemma card_pairSeparated_le_via_good_code
    (m : ℕ) (e : Fin m ↪ Fin (m * 2)) :
    Fintype.card {σ : Equiv.Perm (Fin (m * 2)) // PairSeparated m e σ} ≤
      2 ^ m * Nat.factorial m * Nat.factorial m := by
  calc
    Fintype.card {σ : Equiv.Perm (Fin (m * 2)) // PairSeparated m e σ} ≤
        Fintype.card (pairingGoodCodeType m e) :=
      Fintype.card_le_of_injective (pairingGoodToCode m e)
        (pairingGoodToCode_injective m e)
    _ = 2 ^ m * Nat.factorial m * Nat.factorial m :=
      pairingGoodCodeType_card m e

lemma card_permutation_subtype_le_of_pairSeparated
    (m : ℕ) (e : Fin m ↪ Fin (m * 2))
    (rainbow : Equiv.Perm (Fin (m * 2)) → Prop)
    [Fintype {σ : Equiv.Perm (Fin (m * 2)) // rainbow σ}]
    (hrainbow : ∀ σ, rainbow σ → PairSeparated m e σ) :
    Fintype.card {σ : Equiv.Perm (Fin (m * 2)) // rainbow σ} ≤
      2 ^ m * Nat.factorial m * Nat.factorial m := by
  classical
  let toPairSeparated :
      {σ : Equiv.Perm (Fin (m * 2)) // rainbow σ} →
      {σ : Equiv.Perm (Fin (m * 2)) // PairSeparated m e σ} := fun s =>
    ⟨s.1, hrainbow s.1 s.2⟩
  have hinj : Function.Injective toPairSeparated := by
    intro s t h
    apply Subtype.ext
    exact congrArg (fun z => z.1) h
  calc
    Fintype.card {σ : Equiv.Perm (Fin (m * 2)) // rainbow σ} ≤
        Fintype.card {σ : Equiv.Perm (Fin (m * 2)) // PairSeparated m e σ} :=
      Fintype.card_le_of_injective toPairSeparated hinj
    _ ≤ 2 ^ m * Nat.factorial m * Nat.factorial m :=
      card_pairSeparated_le_via_good_code m e

lemma pairingRestrictionCode_eq_iff_on_selected
    (m : ℕ) (e : Fin m ↪ Fin (m * 2))
    (σ τ : Equiv.Perm (Fin (m * 2)))
    (hσ : PairSeparated m e σ) (hτ : PairSeparated m e τ) :
    pairingRestrictionCode m e σ hσ = pairingRestrictionCode m e τ hτ ↔
      ∀ i : Fin m, σ (e i) = τ (e i) := by
  constructor
  · intro h i
    have hp : pairingPairIndex m (σ (e i)) =
        pairingPairIndex m (τ (e i)) := by
      exact congrArg (fun z : Fin m ↪ Fin m => z i)
        (congrArg Prod.fst h)
    have ho : pairingPairOrientation m (σ (e i)) =
        pairingPairOrientation m (τ (e i)) := by
      exact congrArg (fun z : Fin m → Fin 2 => z i)
        (congrArg Prod.snd h)
    apply finProdFinEquiv.symm.injective
    exact Prod.ext hp ho
  · intro h
    apply Prod.ext
    · apply Function.Embedding.ext
      intro i
      exact congrArg (fun z => pairingPairIndex m z) (h i)
    · funext i
      exact congrArg (fun z => pairingPairOrientation m z) (h i)

lemma pairingPairIndex_image_eq_univ
    (m : ℕ) (e : Fin m ↪ Fin (m * 2))
    (σ : Equiv.Perm (Fin (m * 2)))
    (hsep : PairSeparated m e σ) :
    (Finset.univ.image (fun i : Fin m =>
      pairingPairIndex m (σ (e i)))) = Finset.univ := by
  apply Finset.eq_univ_of_card
  rw [Finset.card_image_of_injective _ hsep]
  simp

/- The remaining extension-count argument will construct this code for every
pair-separated permutation: the first two components record the selected
m elements (pair indices and orientations), while the final permutation
records the complement.  Once that code is injective, the desired factorial
bound is a direct finite-cardinality calculation. -/
lemma card_pairSeparated_le_of_injective_code
    (m : ℕ) (e : Fin m ↪ Fin (m * 2))
    (code : {σ : Equiv.Perm (Fin (m * 2)) // PairSeparated m e σ} →
      ((Fin m ↪ Fin m) × (Fin m → Fin 2)) × Equiv.Perm (Fin m))
    (hcode : Function.Injective code) :
    Fintype.card {σ : Equiv.Perm (Fin (m * 2)) // PairSeparated m e σ} ≤
      Nat.factorial m * 2 ^ m * Nat.factorial m := by
  classical
  calc
    Fintype.card {σ : Equiv.Perm (Fin (m * 2)) // PairSeparated m e σ} ≤
        Fintype.card (((Fin m ↪ Fin m) × (Fin m → Fin 2)) ×
          Equiv.Perm (Fin m)) :=
      Fintype.card_le_of_injective code hcode
    _ = Nat.factorial m * 2 ^ m * Nat.factorial m := by
      rw [Fintype.card_prod, card_pairing_restriction_code]
      simp [Fintype.card_perm]

def pairedColoring {V D C : Type*} [Fintype D] [Fintype C]
    [DecidableEq D] [DecidableEq C]
    (κ : CompleteEdgeColoring V D) (p : PairingMap D C) :
    CompleteEdgeColoring V C where
  color v w := p.color (κ.color v w)
  color_symm v w := by simp [κ.color_symm]

lemma pairedColoring_colorDegree_of_two_regular
    {V D C : Type*} [Fintype V] [Fintype D] [Fintype C]
    [DecidableEq V] [DecidableEq D] [DecidableEq C]
    (κ : CompleteEdgeColoring V D) (p : PairingMap D C)
    (hbase : ∀ v : V, ∀ d : D, κ.colorDegree v d = 2)
    (hquot : Fintype.card V / Fintype.card C = 4)
    (v : V) (c : C) :
    (pairedColoring κ p).colorDegree v c =
      Fintype.card V / Fintype.card C := by
  let s : Finset V := Finset.univ.erase v
  let t : Finset D := (Finset.univ : Finset D).filter (fun d => p.color d = c)
  have hsplit :
      (s.filter (fun w => p.color (κ.color v w) = c)).card =
        ∑ d ∈ t, (s.filter (fun w => κ.color v w = d)).card := by
    calc
      (s.filter (fun w => p.color (κ.color v w) = c)).card =
          (s.filter (fun w => κ.color v w ∈ t)).card := by
            congr 1
            ext w
            simp [t]
      _ = ∑ d ∈ t, (s.filter (fun w => κ.color v w = d)).card := by
            symm
            exact Finset.sum_card_fiberwise_eq_card_filter s t
              (fun w => κ.color v w)
  change (s.filter (fun w => p.color (κ.color v w) = c)).card = _
  rw [hsplit]
  calc
    (∑ d ∈ t, (s.filter (fun w => κ.color v w = d)).card) =
        ∑ d ∈ t, 2 := by
          apply Finset.sum_congr rfl
          intro d hd
          simpa [CompleteEdgeColoring.colorDegree, s] using hbase v d
    _ = t.card * 2 := by simp
    _ = 4 := by
      have ht : t.card = 2 := by simpa [t] using p.fiber_card c
      rw [ht]
    _ = Fintype.card V / Fintype.card C := hquot.symm

theorem pairedColoring_isBalanced_of_two_regular
    {V D C : Type*} [Fintype V] [Fintype D] [Fintype C]
    [DecidableEq V] [DecidableEq D] [DecidableEq C]
    (κ : CompleteEdgeColoring V D) (p : PairingMap D C)
    (hbase : ∀ v : V, ∀ d : D, κ.colorDegree v d = 2)
    (hquot : Fintype.card V / Fintype.card C = 4) :
    (pairedColoring κ p).IsBalanced := by
  intro v c
  exact pairedColoring_colorDegree_of_two_regular κ p hbase hquot v c

lemma pairedColoring_permutation_isBalanced
    {V : Type*} [Fintype V] [DecidableEq V]
    (m : ℕ) (κ : CompleteEdgeColoring V (Fin (m * 2)))
    (hbase : ∀ v : V, ∀ d : Fin (m * 2), κ.colorDegree v d = 2)
    (hquot : Fintype.card V / m = 4)
    (σ : Equiv.Perm (Fin (m * 2))) :
    (pairedColoring κ (permutationPairingMap m σ)).IsBalanced := by
  apply pairedColoring_isBalanced_of_two_regular κ
    (permutationPairingMap m σ) hbase
  simpa using hquot

/- A finite sample is represented by a permutation of the `2m` difference
classes.  This definition packages the pairing construction as a genuine
sample-to-colouring map, so later first-moment arguments can quantify over the
finite permutation type without rebuilding the balance proof each time. -/
def permutationPairingColoring
    {V : Type*} (m : ℕ) (κ : CompleteEdgeColoring V (Fin (m * 2)))
    (σ : Equiv.Perm (Fin (m * 2))) :
    CompleteEdgeColoring V (Fin m) :=
  pairedColoring κ (permutationPairingMap m σ)

lemma permutationPairingColoring_isBalanced
    {V : Type*} [Fintype V] [DecidableEq V]
    (m : ℕ) (κ : CompleteEdgeColoring V (Fin (m * 2)))
    (hbase : ∀ v : V, ∀ d : Fin (m * 2), κ.colorDegree v d = 2)
    (hquot : Fintype.card V / m = 4) :
    ∀ σ : Equiv.Perm (Fin (m * 2)),
      (permutationPairingColoring m κ σ).IsBalanced := by
  intro σ
  exact pairedColoring_permutation_isBalanced m κ hbase hquot σ

lemma exists_zero_of_sum_lt_mul_card {Ω : Type*} [Fintype Ω]
    (N : ℕ) (hN : 0 < N) (badCount : Ω → ℕ)
    (horbit : ∀ ω : Ω, badCount ω = 0 ∨ N ≤ badCount ω)
    (hcount : (∑ ω : Ω, badCount ω) < N * Fintype.card Ω) :
    ∃ ω : Ω, badCount ω = 0 := by
  by_contra hzero
  push_neg at hzero
  have hNle : ∀ ω : Ω, N ≤ badCount ω := by
    intro ω
    rcases horbit ω with hz | hNω
    · exact False.elim (hzero ω hz)
    · exact hNω
  have hsum : (∑ _ω : Ω, N) ≤ ∑ ω : Ω, badCount ω := by
    exact Finset.sum_le_sum (fun ω _ => hNle ω)
  have hcard : N * Fintype.card Ω ≤ ∑ ω : Ω, badCount ω := by
    simpa [Finset.sum_const, Nat.mul_comm] using hsum
  exact (Nat.not_lt_of_ge hcard) hcount

/- A translation orbit is represented by a map from the finite translation
parameter space into a sample type.  The concrete cyclic construction will
prove injectivity of this map from `gcd q N = 1`; the cardinality step itself
is completely generic. -/
lemma card_free_translation_orbit
    {N : ℕ} {Ω : Type*} [DecidableEq Ω]
    (orbit : Fin N → Ω) (hfree : Function.Injective orbit) :
    (Finset.univ.image orbit).card = N := by
  rw [Finset.card_image_of_injective _ hfree]
  simp

/- If every point in an injective finite orbit satisfies a predicate, then the
predicate has at least as many points as the orbit.  This is the cardinality
lemma needed to turn translation invariance into the zero-or-`N` dichotomy. -/
lemma card_filter_ge_of_injective_orbit
    {N : ℕ} {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (bad : Ω → Prop) [DecidablePred bad]
    (orbit : Fin N → Ω)
    (hbad : ∀ t : Fin N, bad (orbit t))
    (hfree : Function.Injective orbit) :
    N ≤ ((Finset.univ : Finset Ω).filter bad).card := by
  classical
  let image : Finset Ω := Finset.univ.image orbit
  have hsub : image ⊆ (Finset.univ : Finset Ω).filter bad := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hbad t
  have hcard : image.card ≤
      ((Finset.univ : Finset Ω).filter bad).card :=
    Finset.card_le_card hsub
  have himage : image.card = N := by
    exact card_free_translation_orbit orbit hfree
  rw [himage] at hcard
  exact hcard

lemma exists_zero_of_sum_lt_orbit_card {Ω : Type*} [Fintype Ω]
    (N : ℕ) (hN : 0 < N) (badCount : Ω → ℕ)
    (horbit : ∀ ω : Ω, badCount ω = 0 ∨ N ≤ badCount ω)
    (hcount : (∑ ω : Ω, badCount ω) <
      N * Fintype.card Ω) :
    ∃ ω : Ω, badCount ω = 0 :=
  exists_zero_of_sum_lt_mul_card N hN badCount horbit hcount

end Erdos811
