module ppl2015 where

data Object (A B : Set) : Set where
  runObject : Object A B

-- oleg's introduction about tagless-final term.

open import Data.Integer
data Exp : Set where
  Lit : ℤ → Exp
  Neg : Exp → Exp
  Add : Exp → Exp → Exp

ti1 = Add (Lit (+ 8)) (Neg (Add (Lit (+ 1)) (Lit (+ 2))))

eval : Exp → ℤ
eval (Lit n) = n
eval (Neg e) = - eval e
eval (Add e1 e2) = eval e1 + eval e2
