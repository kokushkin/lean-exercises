variable r: Prop


-- it's not true for all of them
def NegNotEq  (h: (∀ p: Prop, p ↔ ¬ p)):  false :=

have anypfalse: Prop → false, from

(assume p: Prop, 
have pisnotp: p ↔ ¬ p, from h p,
have pisnotpeq: (p ↔ ¬ p) ↔ ¬(p ↔ ¬ p), from h (p ↔ ¬ p),
have notPisnotp: (p ↔ ¬ p) → ¬(p ↔ ¬ p), from iff.mp pisnotpeq,
have notPISNOTP: ¬(p ↔ ¬ p), from notPisnotp pisnotp,
 notPISNOTP pisnotp),

 anypfalse r


-- Prove ¬(p ↔ ¬p) without using classical logic
-- it's false for all of them
def NegNotEq2 (h: (∀ p: Prop, ¬(p ↔ ¬p))): true :=
    assume q: Prop,
    assume h : q ↔ ¬q,
    iff.elim
        (
            assume hl : q → ¬q,
            assume hr : ¬q → q,
            have hnp : ¬q,
            from
                assume hp : q,
                hl hp hp,
            hnp (hr hnp)
        ) h


--     --
variable p: Prop

def asdasd (hl : p → ¬p, hr : ¬p → p): false :=
(hl hp) hp




example : ¬(p ↔ ¬p) :=
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




--  def NegNotEq  (h: (∀ p: Prop, p ↔ ¬ p)):  false :=
-- assume p: Prop, 
-- have pisnotp: p ↔ ¬ p, from h p,
-- have pisnotpeq: (p ↔ ¬ p) ↔ ¬(p ↔ ¬ p), from h (p ↔ ¬ p),
-- have notPisnotp: (p ↔ ¬ p) → ¬(p ↔ ¬ p), from iff.mp pisnotpeq,
-- have notPISNOTP: ¬(p ↔ ¬ p), from notPisnotp pisnotp,
--  notPISNOTP pisnotp

def add: Int → Int → Int :=
    assume a, assume b, a + b





#check  NegNotEq
