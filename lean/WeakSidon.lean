import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Prod.Lex

/-!
# Small collision-counting lemmas for weak Sidon sets

This module is independent of the concrete Erdős 811 colourings.  The first
lemma bounds a finite domain by the image of a map plus its unordered pairs
of colliding inputs.  It is the finite pigeonhole step used in the additive
energy proof.
-/

namespace Erdos811

section FiniteMap

variable {α β : Type*} [LinearOrder α] [DecidableEq β]

def mapCollisionPairs (s : Finset α) (f : α → β) : Finset (α × α) :=
  s.offDiag.filter fun p => p.1 < p.2 ∧ f p.1 = f p.2

private def fiberAt (s : Finset α) (f : α → β) (x : α) : Finset α :=
  s.filter fun y => f y = f x

private lemma mem_fiberAt {s : Finset α} {f : α → β} {x : α} (hx : x ∈ s) :
    x ∈ fiberAt s f x := by
  simp [fiberAt, hx]

private def fiberMin (s : Finset α) (f : α → β) (x : α) (hx : x ∈ s) : α :=
  (fiberAt s f x).min' ⟨x, mem_fiberAt hx⟩

private lemma fiberMin_mem {s : Finset α} {f : α → β} {x : α} (hx : x ∈ s) :
    fiberMin s f x hx ∈ s := by
  have h := Finset.min'_mem (fiberAt s f x) ⟨x, mem_fiberAt hx⟩
  exact (Finset.mem_filter.mp h).1

private lemma fiberMin_map {s : Finset α} {f : α → β} {x : α} (hx : x ∈ s) :
    f (fiberMin s f x hx) = f x := by
  have h := Finset.min'_mem (fiberAt s f x) ⟨x, mem_fiberAt hx⟩
  exact (Finset.mem_filter.mp h).2

private lemma fiberMin_le {s : Finset α} {f : α → β} {x : α} (hx : x ∈ s) :
    fiberMin s f x hx ≤ x := by
  exact Finset.min'_le _ _ (mem_fiberAt hx)

private lemma fiberMin_eq_of_map_eq {s : Finset α} {f : α → β}
    {x y : α} (hx : x ∈ s) (hy : y ∈ s) (hxy : f x = f y) :
    fiberMin s f x hx = fiberMin s f y hy := by
  apply le_antisymm
  · apply Finset.min'_le
    have hm := Finset.min'_mem (fiberAt s f y) ⟨y, mem_fiberAt hy⟩
    have hm' := Finset.mem_filter.mp hm
    exact Finset.mem_filter.mpr ⟨hm'.1, hm'.2.trans hxy.symm⟩
  · apply Finset.min'_le
    have hm := Finset.min'_mem (fiberAt s f x) ⟨x, mem_fiberAt hx⟩
    have hm' := Finset.mem_filter.mp hm
    exact Finset.mem_filter.mpr ⟨hm'.1, hm'.2.trans hxy⟩

private def mapOrCollision (s : Finset α) (f : α → β) (x : α) : β ⊕ (α × α) :=
  if hx : x ∈ s then
    let r := fiberMin s f x hx
    if h : r = x then Sum.inl (f x) else Sum.inr (r, x)
  else
    Sum.inl (f x)

lemma card_le_card_image_add_card_mapCollisionPairs
    (s : Finset α) (f : α → β) :
    s.card ≤ (s.image f).card + (mapCollisionPairs s f).card := by
  classical
  rw [← Finset.card_disjSum]
  apply Finset.card_le_card_of_injOn (mapOrCollision s f)
  · intro x hx
    have hxs : x ∈ s := hx
    rw [mapOrCollision, dif_pos hxs]
    dsimp only
    split_ifs with hmin
    · exact Finset.inl_mem_disjSum.mpr (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    · apply Finset.inr_mem_disjSum.mpr
      simp only [mapCollisionPairs, Finset.mem_filter, Finset.mem_offDiag]
      refine ⟨⟨fiberMin_mem hxs, hxs, hmin⟩, ?_, fiberMin_map hxs⟩
      exact lt_of_le_of_ne (fiberMin_le hxs) hmin
  · intro x hx y hy hmap
    have hxs : x ∈ s := hx
    have hys : y ∈ s := hy
    rw [mapOrCollision, dif_pos hxs, mapOrCollision, dif_pos hys] at hmap
    by_cases hxMin : fiberMin s f x hxs = x <;>
      by_cases hyMin : fiberMin s f y hys = y <;>
      simp only [hxMin, hyMin, ↓reduceIte] at hmap
    · have hxy : f x = f y := Sum.inl.inj hmap
      calc
        x = fiberMin s f x hxs := hxMin.symm
        _ = fiberMin s f y hys := fiberMin_eq_of_map_eq hxs hys hxy
        _ = y := hyMin
    · contradiction
    · contradiction
    · exact congrArg (fun z : α × α => z.2) (Sum.inr.inj hmap)

end FiniteMap

section WeakSidon

variable {G : Type*} [AddCommGroup G] [LinearOrder G]

/- The ordinary product order is only partial.  Collision pairs need an
arbitrary linear orientation, so use the transported lexicographic order
locally. -/
local instance lexLinearOrderProd : LinearOrder (G × G) :=
  LinearOrder.lift' (fun p : G × G => toLex p) toLex.injective

def IsWeakTwoSidon (A : Finset G) : Prop :=
  ∀ ⦃a b c d : G⦄, a ∈ A → b ∈ A → c ∈ A → d ∈ A →
    a ≠ b → c ≠ d → a + b = c + d →
      (a = c ∧ b = d) ∨ (a = d ∧ b = c)

def IsThreeAPFree (A : Finset G) : Prop :=
  ∀ ⦃a b c : G⦄, a ∈ A → b ∈ A → c ∈ A → b ≠ c → b + c ≠ 2 • a

private lemma weakSidon_collision_cross {A : Finset G} (hA : IsWeakTwoSidon A)
    {a b c d : G} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hd : d ∈ A)
    (hab : a ≠ b) (hcd : c ≠ d) (hpq : (a, b) ≠ (c, d))
    (hsub : a - b = c - d) : a = d ∨ c = b := by
  by_contra hcross
  push_neg at hcross
  have hsum : a + d = c + b := sub_eq_sub_iff_add_eq_add.mp hsub
  have hs := hA ha hd hc hb hcross.1 hcross.2 hsum
  rcases hs with hs | hs
  · exact hpq (Prod.ext hs.1 hs.2.symm)
  · exact hab hs.1

private lemma collision_cross_exclusive
    (hTwo : Function.Injective fun x : G => 2 • x)
    {a b c d : G} (hab : a ≠ b) (hsub : a - b = c - d) :
    ¬ (a = d ∧ c = b) := by
  rintro ⟨rfl, rfl⟩
  apply hab
  apply hTwo
  simp only [two_nsmul]
  exact sub_eq_sub_iff_add_eq_add.mp hsub

private lemma oriented_pair_eq {a b c d : G} (hab : a ≠ b) (hcd : c ≠ d)
    (hsame : (a = c ∧ b = d) ∨ (a = d ∧ b = c))
    (horient : decide (a < b) = decide (c < d)) : a = c ∧ b = d := by
  rcases hsame with hsame | hsame
  · exact hsame
  · rcases hsame with ⟨rfl, rfl⟩
    exfalso
    rcases lt_or_gt_of_ne hab with hablt | hbalt
    · simp [hablt, not_lt_of_ge hablt.le] at horient
    · simp [hbalt, not_lt_of_ge hbalt.le] at horient

private def weakSidonCollisionCode
    (z : (G × G) × (G × G)) : G × Bool :=
  let a := z.1.1
  let b := z.1.2
  let c := z.2.1
  let d := z.2.2
  if a = d then
    (a, decide (b < c))
  else
    (b, !decide (a < d))

private lemma mapCollisionPairs_offDiag_data {A : Finset G}
    {z : (G × G) × (G × G)}
    (hz : z ∈ mapCollisionPairs A.offDiag (fun p : G × G => p.1 - p.2)) :
    z.1.1 ∈ A ∧ z.1.2 ∈ A ∧ z.1.1 ≠ z.1.2 ∧
    z.2.1 ∈ A ∧ z.2.2 ∈ A ∧ z.2.1 ≠ z.2.2 ∧
    z.1 ≠ z.2 ∧ toLex z.1 < toLex z.2 ∧
    z.1.1 - z.1.2 = z.2.1 - z.2.2 := by
  have hfilter := Finset.mem_filter.mp hz
  have hoff := hfilter.1
  have hlt := hfilter.2.1
  have hsub := hfilter.2.2
  have hlt' : toLex z.1 < toLex z.2 := by exact hlt
  simpa [and_assoc] using And.intro hoff (And.intro hlt' hsub)

private lemma weakSidonCollisionCode_mem {A : Finset G} (hA : IsWeakTwoSidon A)
    {z : (G × G) × (G × G)}
    (hz : z ∈ mapCollisionPairs A.offDiag (fun p : G × G => p.1 - p.2)) :
    weakSidonCollisionCode z ∈ A.product Finset.univ := by
  obtain ⟨ha, hb, hab, hc, hd, hcd, hpq, hpqlt, hsub⟩ :=
    mapCollisionPairs_offDiag_data hz
  have hcross : z.1.1 = z.2.2 ∨ z.2.1 = z.1.2 :=
    weakSidon_collision_cross hA ha hb hc hd hab hcd hpq hsub
  rcases z with ⟨⟨a, b⟩, ⟨c, d⟩⟩
  simp only at ha hb hab hc hd hcd hpq hpqlt hsub hcross ⊢
  rcases hcross with had | hcb
  · rw [weakSidonCollisionCode, if_pos had]
    exact Finset.mem_product.mpr ⟨ha, Finset.mem_univ _⟩
  · by_cases had : a = d
    · rw [weakSidonCollisionCode, if_pos had]
      exact Finset.mem_product.mpr ⟨ha, Finset.mem_univ _⟩
    · rw [weakSidonCollisionCode, if_neg had]
      exact Finset.mem_product.mpr ⟨hb, Finset.mem_univ _⟩

private lemma endpoints_ne_of_midpoint
    (hTwo : Function.Injective fun x : G => 2 • x)
    {m x y : G} (hmx : m ≠ x) (hmid : 2 • m = x + y) : x ≠ y := by
  intro hxy
  apply hmx
  apply hTwo
  rw [← hxy] at hmid
  simpa only [two_nsmul] using hmid

private lemma weakSidonCollisionCode_injOn {A : Finset G}
    (hA : IsWeakTwoSidon A)
    (hTwo : Function.Injective fun x : G => 2 • x) :
    Set.InjOn weakSidonCollisionCode
      (↑(mapCollisionPairs A.offDiag (fun p : G × G => p.1 - p.2)) :
        Set ((G × G) × (G × G))) := by
  intro z hz w hw hcode
  obtain ⟨ha, hb, hab, hc, hd, hcd, hpq, hpqlt, hsub⟩ :=
    mapCollisionPairs_offDiag_data hz
  obtain ⟨he, hf, hef, hg, hh, hgh, hrs, hrslt, hsub'⟩ :=
    mapCollisionPairs_offDiag_data hw
  have hcross : z.1.1 = z.2.2 ∨ z.2.1 = z.1.2 :=
    weakSidon_collision_cross hA ha hb hc hd hab hcd hpq hsub
  have hcross' : w.1.1 = w.2.2 ∨ w.2.1 = w.1.2 :=
    weakSidon_collision_cross hA he hf hg hh hef hgh hrs hsub'
  rcases z with ⟨⟨a, b⟩, ⟨c, d⟩⟩
  rcases w with ⟨⟨e, f⟩, ⟨g, h⟩⟩
  by_cases had : a = d
  · have hnotcb : ¬(c = b) := by
      intro hcb
      exact collision_cross_exclusive hTwo hab hsub ⟨had, hcb⟩
    by_cases heh : e = h
    · subst d
      subst h
      have hzmid : 2 • a = b + c := by
        have hs := sub_eq_sub_iff_add_eq_add.mp hsub
        simpa only [two_nsmul, add_comm] using hs
      have hwmid : 2 • e = f + g := by
        have hs := sub_eq_sub_iff_add_eq_add.mp hsub'
        simpa only [two_nsmul, add_comm] using hs
      have hbc : b ≠ c := endpoints_ne_of_midpoint hTwo hab hzmid
      have hfg : f ≠ g := endpoints_ne_of_midpoint hTwo hef hwmid
      have hcode' : (a, decide (b < c)) = (e, decide (f < g)) := by
        simpa only [weakSidonCollisionCode, if_pos rfl, ite_true] using hcode
      have hm : a = e := by
        exact congrArg Prod.fst hcode'
      have hbit : decide (b < c) = decide (f < g) := by
        exact congrArg Prod.snd hcode'
      have hsum : b + c = f + g := by
        calc
          b + c = 2 • a := hzmid.symm
          _ = 2 • e := congrArg (fun x : G => 2 • x) hm
          _ = f + g := hwmid
      have hsides : (b = f ∧ c = g) ∨ (b = g ∧ c = f) := by
        simpa only using hA hb hc hf hg hbc hfg hsum
      have hend := oriented_pair_eq hbc hfg hsides hbit
      rcases hend with ⟨hbf, hcg⟩
      subst e
      subst f
      subst g
      rfl
    · have hgf : g = f := hcross'.resolve_left heh
      subst d
      subst g
      have hzmid : 2 • a = b + c := by
        have hs := sub_eq_sub_iff_add_eq_add.mp hsub
        simpa only [two_nsmul, add_comm] using hs
      have hwmid : 2 • f = e + h := by
        have hs := sub_eq_sub_iff_add_eq_add.mp hsub'
        simpa only [two_nsmul] using hs.symm
      have hbc : b ≠ c := endpoints_ne_of_midpoint hTwo hab hzmid
      have heh' : e ≠ h := endpoints_ne_of_midpoint hTwo hef.symm hwmid
      have hcode' : (a, decide (b < c)) = (f, !decide (e < h)) := by
        simpa only [weakSidonCollisionCode, if_pos rfl, if_neg heh, ite_true] using hcode
      have hm : a = f := by
        exact congrArg Prod.fst hcode'
      have hbit : decide (b < c) = !decide (e < h) := by
        exact congrArg Prod.snd hcode'
      have hsum : b + c = e + h := by
        calc
          b + c = 2 • a := hzmid.symm
          _ = 2 • f := congrArg (fun x : G => 2 • x) hm
          _ = e + h := hwmid
      have hsides : (b = e ∧ c = h) ∨ (b = h ∧ c = e) := by
        simpa only using hA hb hc he hh hbc heh' hsum
      rcases hsides with hend | hend
      · rcases hend with ⟨hbe, hch⟩
        subst e
        subst h
        simp at hbit
      · rcases hend with ⟨hbh, hce⟩
        subst e
        subst h
        subst f
        exact (lt_asymm hpqlt hrslt).elim
  · have hcb : c = b := hcross.resolve_left had
    by_cases heh : e = h
    · have hnotgf : ¬(g = f) := by
        intro hgf
        exact collision_cross_exclusive hTwo hef hsub' ⟨heh, hgf⟩
      subst c
      subst h
      have hzmid : 2 • b = a + d := by
        have hs := sub_eq_sub_iff_add_eq_add.mp hsub
        simpa only [two_nsmul] using hs.symm
      have hwmid : 2 • e = f + g := by
        have hs := sub_eq_sub_iff_add_eq_add.mp hsub'
        simpa only [two_nsmul, add_comm] using hs
      have had' : a ≠ d := endpoints_ne_of_midpoint hTwo hab.symm hzmid
      have hfg : f ≠ g := endpoints_ne_of_midpoint hTwo hef hwmid
      have hcode' : (b, !decide (a < d)) = (e, decide (f < g)) := by
        simpa only [weakSidonCollisionCode, if_neg had, if_pos rfl, ite_true] using hcode
      have hm : b = e := by
        exact congrArg Prod.fst hcode'
      have hbit : (!decide (a < d)) = decide (f < g) := by
        exact congrArg Prod.snd hcode'
      have hsum : a + d = f + g := by
        calc
          a + d = 2 • b := hzmid.symm
          _ = 2 • e := congrArg (fun x : G => 2 • x) hm
          _ = f + g := hwmid
      have hsides : (a = f ∧ d = g) ∨ (a = g ∧ d = f) := by
        simpa only using hA ha hd hf hg had' hfg hsum
      rcases hsides with hend | hend
      · rcases hend with ⟨haf, hdg⟩
        subst f
        subst g
        simp at hbit
      · rcases hend with ⟨hag, hdf⟩
        subst e
        subst f
        subst g
        exact (lt_asymm hpqlt hrslt).elim
    · have hgf : g = f := hcross'.resolve_left heh
      subst c
      subst g
      have hzmid : 2 • b = a + d := by
        have hs := sub_eq_sub_iff_add_eq_add.mp hsub
        simpa only [two_nsmul] using hs.symm
      have hwmid : 2 • f = e + h := by
        have hs := sub_eq_sub_iff_add_eq_add.mp hsub'
        simpa only [two_nsmul] using hs.symm
      have had' : a ≠ d := endpoints_ne_of_midpoint hTwo hab.symm hzmid
      have heh' : e ≠ h := endpoints_ne_of_midpoint hTwo hef.symm hwmid
      have hcode' : (b, !decide (a < d)) = (f, !decide (e < h)) := by
        simpa only [weakSidonCollisionCode, if_neg had, if_neg heh] using hcode
      have hm : b = f := by
        exact congrArg Prod.fst hcode'
      have hbitNot : (!decide (a < d)) = (!decide (e < h)) := by
        exact congrArg Prod.snd hcode'
      have hbit : decide (a < d) = decide (e < h) := by
        have hdouble := congrArg (fun x : Bool => !x) hbitNot
        simpa using hdouble
      have hsum : a + d = e + h := by
        calc
          a + d = 2 • b := hzmid.symm
          _ = 2 • f := congrArg (fun x : G => 2 • x) hm
          _ = e + h := hwmid
      have hsides : (a = e ∧ d = h) ∨ (a = h ∧ d = e) := by
        simpa only using hA ha hd he hh had' heh' hsum
      have hend := oriented_pair_eq had' heh' hsides hbit
      rcases hend with ⟨hae, hdh⟩
      subst e
      subst f
      subst h
      rfl

theorem card_mapCollisionPairs_offDiag_le_two_mul_card {A : Finset G}
    (hA : IsWeakTwoSidon A)
    (hTwo : Function.Injective fun x : G => 2 • x) :
    (mapCollisionPairs A.offDiag (fun p : G × G => p.1 - p.2)).card ≤
      2 * A.card := by
  calc
    (mapCollisionPairs A.offDiag (fun p : G × G => p.1 - p.2)).card ≤
        (A.product (Finset.univ : Finset Bool)).card := by
      apply Finset.card_le_card_of_injOn weakSidonCollisionCode
      · intro z hz
        exact weakSidonCollisionCode_mem hA hz
      · exact weakSidonCollisionCode_injOn hA hTwo
    _ = A.card * 2 := by simp [Finset.card_product]
    _ = 2 * A.card := Nat.mul_comm _ _

theorem weakTwoSidon_card_mul_sub_three_le [Fintype G]
    (A : Finset G) (hA : IsWeakTwoSidon A)
    (hTwo : Function.Injective fun x : G => 2 • x) :
    A.card * (A.card - 3) ≤ Fintype.card G - 1 := by
  let D : Finset (G × G) := A.offDiag
  let δ : G × G → G := fun p => p.1 - p.2
  have hcount := card_le_card_image_add_card_mapCollisionPairs D δ
  have himage : (D.image δ).card ≤ Fintype.card G - 1 := by
    have hsub : D.image δ ⊆ (Finset.univ : Finset G).erase 0 := by
      intro x hx
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
      have hp' : p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 ≠ p.2 := by
        simpa [D] using hp
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      exact sub_ne_zero.mpr hp'.2.2
    calc
      (D.image δ).card ≤ ((Finset.univ : Finset G).erase 0).card :=
        Finset.card_le_card hsub
      _ = Fintype.card G - 1 := by simp
  have hcollisions : (mapCollisionPairs D δ).card ≤ 2 * A.card := by
    simpa [D, δ] using card_mapCollisionPairs_offDiag_le_two_mul_card hA hTwo
  have hbase : A.card * A.card - A.card ≤
      (Fintype.card G - 1) + 2 * A.card := by
    rw [show D.card = A.card * A.card - A.card by simp [D]] at hcount
    exact hcount.trans (Nat.add_le_add himage hcollisions)
  calc
    A.card * (A.card - 3) =
        (A.card * A.card - A.card) - 2 * A.card := by
      rw [Nat.mul_sub_left_distrib]
      omega
    _ ≤ Fintype.card G - 1 := Nat.sub_le_iff_le_add.mpr hbase

theorem threeAPFree_weakTwoSidon_card_mul_sub_one_le [Fintype G]
    (A : Finset G) (hA : IsWeakTwoSidon A) (hAP : IsThreeAPFree A)
    (hTwo : Function.Injective fun x : G => 2 • x) :
    A.card * (A.card - 1) ≤ Fintype.card G - 1 := by
  let D : Finset (G × G) := A.offDiag
  let δ : G × G → G := fun p => p.1 - p.2
  have hcollisionEmpty : mapCollisionPairs D δ = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro z hz
    obtain ⟨ha, hb, hab, hc, hd, hcd, hpq, _hpqlt, hsub⟩ :=
      mapCollisionPairs_offDiag_data (A := A) (by simpa [D, δ] using hz)
    have hcross : z.1.1 = z.2.2 ∨ z.2.1 = z.1.2 :=
      weakSidon_collision_cross hA ha hb hc hd hab hcd hpq hsub
    rcases z with ⟨⟨a, b⟩, ⟨c, d⟩⟩
    rcases hcross with had | hcb
    · have hmid : 2 • a = b + c := by
        have hs := sub_eq_sub_iff_add_eq_add.mp hsub
        rw [← had] at hs
        simpa only [two_nsmul, add_comm] using hs
      have hbc : b ≠ c := endpoints_ne_of_midpoint hTwo hab hmid
      exact hAP ha hb hc hbc hmid.symm
    · have hmid : 2 • b = a + d := by
        have hs := sub_eq_sub_iff_add_eq_add.mp hsub
        rw [hcb] at hs
        simpa only [two_nsmul] using hs.symm
      have had : a ≠ d := endpoints_ne_of_midpoint hTwo hab.symm hmid
      exact hAP hb ha hd had hmid.symm
  have hcount := card_le_card_image_add_card_mapCollisionPairs D δ
  have himage : (D.image δ).card ≤ Fintype.card G - 1 := by
    have hsub : D.image δ ⊆ (Finset.univ : Finset G).erase 0 := by
      intro x hx
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
      have hp' : p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 ≠ p.2 := by
        simpa [D] using hp
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      exact sub_ne_zero.mpr hp'.2.2
    calc
      (D.image δ).card ≤ ((Finset.univ : Finset G).erase 0).card :=
        Finset.card_le_card hsub
      _ = Fintype.card G - 1 := by simp
  have hbase : A.card * A.card - A.card ≤ Fintype.card G - 1 := by
    rw [show D.card = A.card * A.card - A.card by simp [D]] at hcount
    rw [hcollisionEmpty] at hcount
    simpa using hcount.trans (Nat.add_le_add_right himage 0)
  rw [Nat.mul_sub_left_distrib]
  simpa using hbase

end WeakSidon

end Erdos811
