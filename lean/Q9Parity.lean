import CyclicBases

/-!
Arithmetic lemmas for the q=9 cyclic colouring.  These are the first layer of
the smaller two-branch LRAT bridge: they expose the parity formula used to
remove the `∞` branch on paper.
-/

namespace Erdos811

lemma q9Color_val_finite {i j : Fin 73}
    (hi : i.val < 72) (hj : j.val < 72) :
    (q9Coloring.color i j).val = ((i.val + j.val + 1) / 2) % 36 := by
  have hi' : i.val ≠ 72 := by omega
  have hj' : j.val ≠ 72 := by omega
  simp [q9Coloring, hi', hj']

lemma q9Color_val_infty_left {j : Fin 73} :
    (q9Coloring.color ⟨72, by omega⟩ j).val = j.val % 36 := by
  simp [q9Coloring]

lemma q9Color_val_infty_right {i : Fin 73} :
    (q9Coloring.color i ⟨72, by omega⟩).val = i.val % 36 := by
  by_cases hi : i.val = 72
  · simp [q9Coloring, hi]
  · simp [q9Coloring, hi]

lemma q9_fin36_value_sum :
    ∑ c : Fin 36, c.val = 630 := by decide

lemma q9_sum_image_fin36 {α : Type*} [Fintype α]
    (f : α → Fin 36) (hf : Function.Injective f)
    (hcard : Fintype.card α = 36) :
    ∑ a : α, (f a).val = 630 := by
  have himage : (Finset.univ.image f).card = 36 := by
    rw [Finset.card_image_of_injective _ hf]
    simpa [hcard]
  have hfull : Finset.univ.image f = (Finset.univ : Finset (Fin 36)) := by
    apply Finset.eq_univ_of_card
    simpa using himage
  calc
    (∑ a : α, (f a).val) = Finset.sum (Finset.univ : Finset α) (fun a => (f a).val) := by rfl
    _ = Finset.sum (Finset.univ.image f) (fun c => c.val) := by
      rw [Finset.sum_image]
      intro a ha b hb hab
      exact hf hab
    _ = ∑ c : Fin 36, c.val := by simp [hfull]
    _ = 630 := q9_fin36_value_sum

end Erdos811
