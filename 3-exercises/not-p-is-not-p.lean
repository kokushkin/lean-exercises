variables p q r : Prop

-- Prove ¬(p ↔ ¬p) without using classical logic.
-- p ↔ ¬p - > false  

example: ¬(p ↔ ¬p) :=-
assume pisnotp: p ↔ ¬p,
iff.mp p ¬p pisnotp




example: ¬(p ↔ ¬p) :=
assume pisnotp: p ↔ ¬p,
have h1: p → ¬p  , from iff.mp pisnotp,
have h2: ¬ (p ↔ ¬p), from h1 pisnotp,



example: (p ↔ q) → (q ↔ p) :=
  assume pq: p ↔ q,
   iff.intro
   (assume hq: q,
    iff.mpr pq hq)
   (assume hp: p,
    iff.mp pq hp)
   


-- We're proving that ¬(p ↔ ¬ p) is true for every p: Prop is true, right?

example : ¬ ∀ p, p ↔ ¬ p := sorry


def NegNotEq {p: Prop} (h: ∀ p, p ↔ ¬ p):  false := 
assume p: Prop, 
have pisnotp: p ↔ ¬ p, from h p,
have pisnotpeq: (p ↔ ¬ p) ↔ ¬(p ↔ ¬ p), from h pisnotp,
-- have notPisnotp: ¬(p → ¬ p), from iff.mp (h ()

#check NegNotEq