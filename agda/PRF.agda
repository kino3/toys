module PRF where
-- primitive recursive function
-- by K. Takahashi's Book

open import Data.Nat renaming (zero to nzero; suc to nsuc)
open import Data.Product
open import Data.Empty using (⊥)

-- cartesian product
_^_ : Set → ℕ → Set
s ^ 0  = ⊥
s ^ nsuc nzero = s
s ^ nsuc n     = s × (s ^ n)

{-
proj : {n i : ℕ} {prf : 1 ≤ i} {prf2 : i ≤ n} → ℕ ^ n → ℕ
proj {nzero}  {nzero}  {()} 
proj {nzero}  {nsuc i} {s≤s prf} {()} 
proj {nsuc n} {nzero}  {()}
proj {nsuc nzero}    {nsuc .0}       {s≤s z≤n} {s≤s z≤n}   n       = n
proj {nsuc (nsuc n)} {nsuc .0}       {s≤s z≤n} {s≤s z≤n}  (x , xs) = x
proj {nsuc (nsuc n)} {nsuc (nsuc i)} {s≤s z≤n} {s≤s prf2} (x , xs) = proj {nsuc n} {nsuc i} {s≤s z≤n} {prf2} xs

data PRF : {n : ℕ} → (ℕ ^ n → ℕ) → Set where
  zero : PRF {0} (λ ())
  suc  : PRF {1} (λ n → n + 1)
  p    : {n i : ℕ} {prf : 1 ≤ i} {prf2 : i ≤ n} → PRF {n} (λ ns → proj {n} {i} {prf} {prf2} ns)
-}


data PRF2 : Set → Set where
  zero : PRF2 (ℕ ^ 0)
  suc  : ℕ → PRF2 (ℕ)
  p    : (n i : ℕ) {prf : 1 ≤ i} {prf2 : i ≤ n} → PRF2 (ℕ ^ n)

eval : {f : Set} → PRF2 f → ℕ
eval zero = nzero
eval suc = {!!}
eval (p n i) = {!!}

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

{-
open import Data.Vec

-- Primitive Recursive Function
data PRF : ℕ → Set where
  -- (1)
  zero : PRF 0
  suc  : ℕ → PRF 1
  proj : {n i : ℕ} → ℕ ^ n → 1 ≤ i → i ≤ n → PRF n


-- PRFはAgdaの関数ではないので、関数の評価方法を定めないと動かない。(f xと書けない)
eval : {n : ℕ} → PRF n → ℕ
-- (1)
eval zero           = 0
eval (suc x)        = nsuc x
eval (proj {nzero}  {nzero}  prod () prf2)
eval (proj {nzero}  {nsuc i} prod prf1 ())
eval (proj {nsuc n} {nzero}  prod () prf2)
----------- n               i              ----------
eval (proj {nsuc nzero}    {nsuc nzero}    n prf1 prf2)    = n -- p^1_1 s.t. identity
eval (proj {nsuc nzero}    {nsuc (nsuc i)} prod (s≤s z≤n) (s≤s ()))
eval (proj {nsuc (nsuc n)} {nsuc nzero}    (x , xs) prf1 prf2) = x
eval (proj {nsuc (nsuc n)} {nsuc (nsuc i)} (x , xs) prf1 (s≤s p))
  = eval (proj {nsuc n} {nsuc i} xs (s≤s z≤n) p)

-- (2)
cmp  : {m n : ℕ} {prf : 1 ≤ m} → PRF m → Vec (PRF n) m → PRF n
cmp g gjs = {!!}
-}
{-
eval (cmp {nzero} {_} {()} g gjs)
eval (cmp {nsuc .0} {nzero} (suc x) (zero ∷ []))          = 1 --eval (suc (eval zero))
eval (cmp {nsuc .0} {nzero} (suc x) (proj () _ _ ∷ []))
eval (cmp {nsuc .0} {nzero} (suc x) (cmp g gjs ∷ []))     = {!!} --eval (suc (eval (cmp g gjs)))
eval (cmp {nsuc .0} {nzero} (proj n prf1 prf2) (g1 ∷ [])) = eval g1
eval (cmp {nsuc .0} {nzero} {prf} (cmp {_} {_} {prf2} g gjs) (zero ∷ [])) = {!!}
eval (cmp {nsuc .0} {nzero} (cmp g gjs) (proj x x₁ x₂ ∷ [])) = {!!}
eval (cmp {nsuc .0} {nzero} (cmp g gjs) (cmp g1 x ∷ [])) = {!!}
eval (cmp {nsuc _}  {nzero} g (g1 ∷ g2 ∷ g3s)) = {!!}
eval (cmp {nsuc m} {nsuc n} {prf} g gjs) = {!!}
-}
