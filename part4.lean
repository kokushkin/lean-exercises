open classical

variables (α : Type*) (p q : α → Prop)
variable r : Prop

example : (∃ x : α, r) → r := 
assume ⟨w,hw⟩, hw

example (a : α) : r → (∃ x : α, r) := 
assume r,
exists.intro a r

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := 
iff.intro
(assume h: ∃ x, p x ∧ r,
  exists.elim h
  (assume w,
   assume hw: p w ∧ r,
   show (∃ x, p x) ∧ r,
    from ⟨exists.intro w hw.left, hw.right ⟩ ))
(assume h: (∃ x, p x) ∧ r,
  exists.elim h.left
  (assume wl,
   assume hwl: p wl,
   show ∃ x, p x ∧ r, 
    from exists.intro wl ⟨hwl,  h.right⟩ ))

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := 
iff.intro
(assume h: ∃ x, p x ∨ q x,
  exists.elim h
  (assume w,
  assume hw: p w ∨ q w,
  hw.elim 
    (assume hp: p w,
      or.inl (exists.intro w hp))
    (assume hq: q w,
      or.inr (exists.intro w hq))))
(assume h: (∃ x, p x) ∨ (∃ x, q x),
  h.elim
    -- short version
    (assume ⟨w, hw⟩, ⟨w, (or.inl hw)⟩)
    -- long version
    (assume hq: ∃ x, q x,
      exists.elim hq
      (assume w,
      assume hw: q w,
      show ∃ x, p x ∨ q x, from  exists.intro w (or.inr hw)))
)

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := 
iff.intro
(assume h: ∀ x, p x,
 show ¬ (∃ x, ¬ p x), from
 (assume h1: ∃ x, ¬ p x,
  show false, from exists.elim h1 
    (assume w,
     assume hw: ¬ p w,
     hw (h w) 
    )
 )
)
(assume h: ¬ (∃ x, ¬ p x),
 assume w,
 

 )

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := sorry
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := sorry
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := sorry

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := sorry
example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := sorry
example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := sorry