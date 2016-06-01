module PRF where
-- primitive recursive function
-- by K. Takahashi's Book

open import Data.Nat renaming (zero to nzero; suc to nsuc)
open import Data.Product
--open import Relation.Binary.PropositionalEquality
open import Data.Empty
--open import Relation.Nullary using (yes;no)

-- cartesian product
_^_ : Set → ℕ → Set
s ^ 0  = ⊥
s ^ nsuc nzero = s
s ^ nsuc n     = s × (s ^ n)

{-
record Proj (n : ℕ) : Set where
  field
    product : ℕ ^ n

  proj : (i : ℕ) → 1 ≤ i → i ≤ n → ℕ
  proj nzero () prf2
  proj (nsuc nzero) (s≤s z≤n) a     = {!!}
  proj (nsuc (nsuc i)) (s≤s prf1) a = {!!}
-}
{-
Proj : (n : ℕ) → (i : ℕ) → i ≤ n → ℕ ^ n → ℕ 
Proj nzero           nzero          z≤n ()
Proj nzero          (nsuc i)        () 
Proj (nsuc nzero)    nzero          z≤n x       = x
Proj (nsuc (nsuc n))  nzero          z≤n xs      = proj₁ xs
Proj (nsuc nzero)    (nsuc nzero)    (s≤s prf) x  = x
Proj (nsuc nzero)    (nsuc (nsuc i)) (s≤s ())  x
Proj (nsuc (nsuc n)) (nsuc i)       (s≤s prf) xs = Proj (nsuc n) i prf (proj₂ xs)
-}
open import Data.Vec

-- Primitive Recursive Function
data PRF : ℕ → Set where
  -- (1)
  zero : PRF 0
  suc  : ℕ → PRF 1
  proj : {n i : ℕ} → ℕ ^ n → 1 ≤ i → i ≤ n → PRF n
  -- (2)
  cmp  : {m n : ℕ} {prf : 1 ≤ m} → PRF m → Vec (PRF n) m → PRF n


-- PRFはAgdaの関数ではないので、関数の評価方法を定めないと動かない。(f xと書けない)
eval : {n : ℕ} → PRF n → ℕ
eval zero           = 0
eval (suc x)        = x + 1
eval (proj {nzero}  {nzero}  prod () prf2)
eval (proj {nzero}  {nsuc i} prod prf1 ())
eval (proj {nsuc n} {nzero}  prod () prf2)
----------- n               i              ----------
eval (proj {nsuc nzero}    {nsuc nzero}    n prf1 prf2)    = n -- p^1_1 s.t. identity
eval (proj {nsuc nzero}    {nsuc (nsuc i)} prod (s≤s z≤n) (s≤s ()))
eval (proj {nsuc (nsuc n)} {nsuc nzero}    (x , xs) prf1 prf2) = x
eval (proj {nsuc (nsuc n)} {nsuc (nsuc i)} (x , xs) prf1 (s≤s p))
  = eval (proj {nsuc n} {nsuc i} xs (s≤s z≤n) p)
eval (cmp prf prfs) = {!!}

{-
comp : ∀ {m n} → PRF m → Vec (PRF n) m → 1 ≤ m → PRF n 
comp g []              ()
comp (suc x)             (g1 ∷ []) (s≤s z≤n) = {!!}
comp (proj xs prf1 prf2) (g1 ∷ []) (s≤s z≤n) = {!!}
comp g (g1 ∷ g2 ∷ gjs) (s≤s z≤n) = {!!}
-}
