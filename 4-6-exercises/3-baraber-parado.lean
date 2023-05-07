variables (men : Type*) (barber : men)
variable  (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) :
show false, 
from (
  have bsb_iif_bnsb: (shaves barber barber ↔ ¬ shaves barber barber), from h barber,
  have bsb_bnsb: (shaves barber barber →  ¬ shaves barber barber), from iff.elim_left bsb_iif_bnsb,

  iff.elim_left (h barber)
)


type mismatch at application
  pisnotp.mp pisnotp
term
  pisnotp
has type
  p ↔ ¬p
but is expected to have type
  pLean