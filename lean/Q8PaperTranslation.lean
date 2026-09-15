import Q8PaperNormalized

/-! Translation of the q=8 numerical colouring, fixing the infinity vertex. -/

namespace Erdos811

def q8TranslateNat (s x : Nat) : Nat :=
  if x = 56 then 56 else (x + s) % 56

lemma q8TranslateNat_le (s x : Nat) : q8TranslateNat s x ≤ 56 := by
  unfold q8TranslateNat
  split <;> omega

lemma q8TranslateNat_finite (s x : Nat) (hx : x < 56) :
    q8TranslateNat s x < 56 := by
  have hn : x ≠ 56 := by omega
  simp only [q8TranslateNat, hn, ite_false]
  omega

lemma q8TranslateNat_injective (s x y : Nat) (hx : x ≤ 56) (hy : y ≤ 56)
    (he : q8TranslateNat s x = q8TranslateNat s y) : x = y := by
  unfold q8TranslateNat at he
  split_ifs at he <;> omega

lemma q8TranslateNat_inverse (s x : Nat) (hs : s < 56) (hx : x ≤ 56) :
    q8TranslateNat (56 - s) (q8TranslateNat s x) = x := by
  by_cases hi : x = 56
  · simp [q8TranslateNat, hi]
  · have ht : (x + s) % 56 ≠ 56 := by omega
    simp only [q8TranslateNat, hi, ht, ite_false]
    omega

/-- Every non-diagonal edge colour is translated by the same amount modulo 28. -/
lemma q8TranslateNat_color (s x y : Nat)
    (hne : x ≠ y) :
    q8PaperColorNat (q8TranslateNat s x) (q8TranslateNat s y) =
      (q8PaperColorNat x y + s) % 28 := by
  have hxt : (x + s) % 56 ≠ 56 := by omega
  have hyt : (y + s) % 56 ≠ 56 := by omega
  by_cases hxi : x = 56 <;> by_cases hyi : y = 56 <;>
    simp [q8TranslateNat, q8PaperColorNat, hxi, hyi, hxt, hyt] <;> omega

#print axioms q8TranslateNat_color
#print axioms q8TranslateNat_inverse

end Erdos811
