variables p q r : Prop

-- commutativity of ∧ and ∨
def conjuction_commutativity : p ∧ q ↔ q ∧ p := sorry


def disjunction_commutativity_one_way {p: Prop} {q: Prop} (h : p ∨ q) : q ∨ p :=
or.elim h
  (assume hp : p,
    show q ∨ p, from or.intro_right q hp)
  (assume hq : q,
    show q ∨ p, from or.intro_left p hq)

example : p ∨ q ↔ q ∨ p := 
iff.intro
  (disjunction_commutativity_one_way)
  (disjunction_commutativity_one_way)


def conjuction_associativity_left {p: Prop} {q: Prop} {r: Prop} (h: (p ∧ q) ∧ r) : p ∧ (q ∧ r) :=
have hpq: p ∧ q, from h.left,
have hp: p, from hpq.left,
have hq: q, from hpq.right,
have hr: r, from h.right,
have hqr: q ∧ r, from ⟨hq, hr⟩,
show p ∧ (q ∧ r), from ⟨hp, hqr⟩

def conjuction_associativity_right {p: Prop} {q: Prop} {r: Prop} (h: p ∧ (q ∧ r)) : (p ∧ q) ∧ r :=
have hqr: q ∧ r, from h.right,
have hq: q, from hqr.left,
have hr: r, from hqr.right,
have hp: p, from h.left,
have hpq: p ∧ q, from ⟨hp, hq⟩,
show (p ∧ q) ∧ r, from ⟨hpq, hr⟩


-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := 
iff.intro 
  (conjuction_associativity_left)
  (conjuction_associativity_right)



def disjunction_associativity_right {p: Prop} {q: Prop} {r: Prop} (h: (p ∨ q) ∨ r) : p ∨ (q ∨ r) :=
or.elim h
  (assume hpq: p ∨ q,
    or.elim hpq
      (assume hp: p,
        show p ∨ (q ∨ r), from or.inl hp )
      (assume hq: q,
        have hqr: q ∨ r, from or.inl hq,
        show p ∨ (q ∨ r), from or.inr hqr))
  (assume hr: r,
   have hqr: q ∨ r, from or.inr hr,
   show p ∨ (q ∨ r), from or.inr hqr)

def disjunction_associativity_left {p: Prop} {q: Prop} {r: Prop} (h: p ∨ (q ∨ r)) : (p ∨ q) ∨ r :=
or.elim h
  (assume hp: p,
   have hpq: p ∨ q, from or.inl hp,
   show (p ∨ q) ∨ r, from or.inl hpq)
  (assume hqr: q ∨ r,
    or.elim hqr
      (assume hq: q,
        have hpq: p ∨ q, from or.inr hq,
        show (p ∨ q) ∨ r, from or.inl hpq)
      (assume hr: r,
        show (p ∨ q) ∨ r, from or.inr hr ))



example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := 
iff.intro
  (disjunction_associativity_right)
  (disjunction_associativity_left)


-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := 
iff.intro
  (assume hpqr: p ∧ (q ∨ r),
   have hp: p, from hpqr.left,
   have hqr: q ∨ r, from hpqr.right,
   or.elim hqr
      (assume hq: q,
        have hpq: p ∧ q, from ⟨hp, hq⟩,
        show (p ∧ q) ∨ (p ∧ r), from or.inl hpq
      )
      (assume hr: r,
        have hpr: p ∧ r, from ⟨hp, hr⟩,
        show (p ∧ q) ∨ (p ∧ r), from or.inr hpr
      )
  )
  (assume pqpr: (p ∧ q) ∨ (p ∧ r),
    or.elim pqpr
      (assume pq: p ∧ q,
        have hp: p, from pq.left,
        have hq: q, from pq.right,
        have hqr: q ∨ r, from or.inl hq,
        show p ∧ (q ∨ r), from ⟨hp,hqr⟩
      )
      (assume pr: p ∧ r,
        have hp: p, from pr.left,
        have hr: r, from pr.right,
        have hqr: q ∨ r, from or.inr hr,
        show p ∧ (q ∨ r), from ⟨hp,hqr⟩ 
      )
  )


example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := 
iff.intro
  (assume hpqr: p → (q → r),
    assume hpq: p ∧ q,
    have hp: p, from hpq.left,
    have hq: q, from hpq.right,
    have hqr: q → r,from hpqr hp,
    show r, from hqr hq
  )
  (assume hpqr: p ∧ q → r,
    assume hp: p,
    assume hq: q,
    show r,from hpqr ⟨hp, hq⟩ 
  )



example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
iff.intro

(assume hpqr: (p ∨ q) → r,
 have hpr: p → r, from 
  assume hp: p, 
    have hpq: p ∨ q, from or.inl  hp, 
    show r, from hpqr hpq,
 have hqr: q → r, from
  assume hq: q,
    have hpq: p ∨ q, from or.inr hq,
    show r, from hpqr hpq,
 show (p → r) ∧ (q → r), from ⟨hpr, hqr⟩ )

(assume hprqr: (p → r) ∧ (q → r),
  assume hpq: p ∨ q,
    or.elim hpq 
      (assume hp: p,
        show r, from hprqr.left hp)
      (assume hq: q,
        show r, from hprqr.right hq)) 


example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := 
iff.intro

(assume npq: ¬(p ∨ q),
have np: ¬p, from
  assume hp: p,
    have hpq: p ∨ q, from or.inl hp,
    show false, from npq hpq,
have nq: ¬q, from 
  assume hq: q,
    have hpq: p ∨ q, from or.inr hq,
    show false, from npq hpq,
show ¬p ∧ ¬q, from ⟨np, nq⟩)

(assume npnq: ¬p ∧ ¬q,
assume pq: p ∨ q,
 or.elim pq
 (assume hp: p,
  show false, from npnq.left hp)
 (assume hq: q,
  show false, from npnq.right hq)
)

example : ¬p ∨ ¬q → ¬(p ∧ q) := 
assume npnq: ¬p ∨ ¬q,
assume hpq: p ∧ q,
or.elim npnq
(assume hnp: ¬p,
show false, from hnp hpq.left)
(assume hnq: ¬q,
show false, from hnq hpq.right)


example : ¬(p ∧ ¬p) := 
assume npq: p ∧ ¬p,
show false, from npq.right npq.left 

example : p ∧ ¬q → ¬(p → q) := 
assume hpnq: p ∧ ¬q,
assume hpq: p → q,
show false, from hpnq.right (hpq hpnq.left)

example : ¬p → (p → q) := 
assume hnp: ¬p,
assume hp: p,
show q, from absurd hp hnp

example : (¬p ∨ q) → (p → q) := 
assume hnpq: ¬p ∨ q,
assume hp: p,
or.elim hnpq
(assume nhp: ¬p,
show q, from absurd hp nhp
)
(assume hq: q,
show q, from hq)

example : p ∨ false ↔ p := 
iff.intro
(assume hpf: p ∨ false,
or.elim hpf
  (assume hp: p,
  show p , from hp)
  (assume hf: false,
  show p, from false.elim hf))
(assume hp: p,
show p ∨ false, from or.intro_left false hp )

example : p ∧ false ↔ false := 
iff.intro
(assume hpf: p ∧ false,
show false, from hpf.right)
(assume hf: false,
show p ∧ false, from false.elim hf)

example : (p → q) → (¬q → ¬p) := 
assume hpq: p → q,
assume hnq: ¬q,
assume hp: p,
have hq: q, from hpq hp,
show false, from hnq hq 



open classical

variables s : Prop



example : (p → r ∨ s) → ((p → r) ∨ (p → s)) := 
assume hprs: p → r ∨ s,
or.elim (em r)
  (assume vr: r,
    or.inl 
      (show p → r, from
        assume hp: p,
        vr)
  )
  (assume hnr: ¬r,
    or.inr
      (show p → s, from
        assume hp: p,
        or.elim (hprs hp)
          (assume hr: r,
           show s, from absurd hr hnr)
          (assume hs: s,
           show s, from hs
          )
        )
  )



example : ¬(p ∧ q) → ¬p ∨ ¬q := 
or.elim (em p)
  (assume hp : p,
    or.inr
      (show ¬q, from
        assume hq : q,
        h ⟨hp, hq⟩))
  (assume hp : ¬p,
    or.inl hp)

example : ¬(p → q) → p ∧ ¬q := sorry
example : (p → q) → (¬p ∨ q) := sorry
example : (¬q → ¬p) → (p → q) := sorry
example : p ∨ ¬p := sorry
example : (((p → q) → p) → p) := sorry