module b4seminar where
-- 2014 snippet

module dayhoge where
  open import Data.Nat
  open import Data.Bool

  Num : Set
  Num = ℕ

  postulate
    wadai machine : Set

  data joken : Set where
    mkJoken : wadai → machine → joken


  handan : Set
  handan = Bool

  _naraba1_ : {w1 w2 : wadai} {m1 m2 : machine} → joken → joken → handan
  a naraba1 b = {!!}


module day20141112 where
  
  postulate 
    Person : Set

  _は_の親 : Person → Person → Set
  x は y の親 = {!!}

  record _∧_ {A : Set} (a1 a2 : A) : Set where
    constructor ∧-intro
    field
      ∧-elim1 : A
      ∧-elim2 : A
