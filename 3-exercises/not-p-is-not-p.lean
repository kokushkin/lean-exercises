-- Prove ¬(p ↔ ¬p) without using classical logic


-- it's not true for all of them (this is not what they meant but still interesting proof)
 def NotTrueForAll : ¬ (∀ p: Prop, p ↔ ¬ p) :=
assume h: (∀ p: Prop, p ↔ ¬ p),
have anypfalse: Prop → false, from

(assume p: Prop, 
  have pisnotp: p ↔ ¬ p, from h p,
  have pisnotpeq: (p ↔ ¬ p) ↔ ¬(p ↔ ¬ p), from h (p ↔ ¬ p),
  have notPisnotp: (p ↔ ¬ p) → ¬(p ↔ ¬ p), from iff.mp pisnotpeq,
  have notPISNOTP: ¬(p ↔ ¬ p), from notPisnotp pisnotp,
 notPISNOTP pisnotp),

-- instead of true we could substitute any prooven proposition
 anypfalse true


-- it's false for all of them
def FalseForAll: (∀ p: Prop, ¬(p ↔ ¬p)) :=
assume p: Prop,
show ¬(p ↔ ¬p), from
(
    assume h : p ↔ ¬p,
    iff.elim
        (
            assume hl : p → ¬p,
            assume hr : ¬p → p,
            have hnp : ¬p,
            from
                assume hp : p,
                hl hp hp,
            hnp (hr hnp)
        ) h
)
