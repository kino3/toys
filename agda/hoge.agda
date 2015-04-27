module hoge where

data ⊥ : Set where

⊥Elim : {P : Set} → ⊥ → P
⊥Elim ()
