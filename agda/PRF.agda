module PRF where

-- Primitive Recursive Function (PRF)
-- by K. Takahashi's Book

open import Data.Nat renaming (zero to nzero; suc to nsuc) hiding (pred)
open import Data.Vec hiding ([_])

-- 定義1.3.1
data PRF : ℕ → Set where
  -- (1)
  zero : PRF 0
  suc  : PRF 1
  p    : (n : ℕ) {prf : 1 ≤ n} → PRF n
  -- (2)
  cmp  : {m n j : ℕ} {prf1 : 1 ≤ j} {prf2 : j ≤ m}
         → PRF m → Vec (PRF n) j → PRF n
  -- (3)

-- function application
{-# NON_TERMINATING #-}
_[_] : {n : ℕ} → PRF n → Vec ℕ n → ℕ
zero [ [] ]     = nzero
suc  [ x ∷ [] ] = nsuc x
p nzero {()} [ xs ]
p (nsuc nzero)    {s≤s prf} [ x ∷ xs ] = x
p (nsuc (nsuc n)) {s≤s prf} [ x ∷ xs ] = (p (nsuc n) {s≤s z≤n}) [ xs ]
cmp {_}     {_} {nzero}  {()}       {_}  g gj [ _ ]
cmp {nzero} {_} {nsuc j} {s≤s prf1} {()} g gj [ _ ]
cmp {nsuc nzero}    {0} {nsuc .0} {s≤s z≤n} {s≤s z≤n} g (g1 ∷ []) [ xs ] =  g [ (g1 [ xs ]) ∷ [] ]
cmp {nsuc (nsuc m)} {0} {nsuc j}  {s≤s p1}  {s≤s p2}  g (g1 ∷ gj) [ xs ] = g [ (g1 [ xs ]) ∷ {!!} ]
cmp {nsuc nzero} {nsuc n} {nsuc .0} {s≤s z≤n} {s≤s z≤n} g (g1 ∷ []) [ xs ] = g [ (g1 [ xs ]) ∷ [] ]
cmp {nsuc (nsuc m)} {nsuc n} {nsuc j} {s≤s prf1} {s≤s prf2} g gj [ xs ] = g [ {!!} ]

{-
{-# NON_TERMINATING #-}
rec' : {n : ℕ} → (g : ℕ ^ n → ℕ) → (h : ℕ ^ (2 + n) → ℕ) → (ℕ ^ (nsuc n) → ℕ) 
rec' g h xs with last xs
rec' g h xs | nzero  = g (init xs)
rec' g h xs | nsuc y = h (init xs ∷ʳ y ∷ʳ rec' g h ((init xs) ∷ʳ y))

one : PRF (ℕ ^ 1 → ℕ)
one = {!!}
-}

{-
-- All functions in Vec are Primitive recursive.
data PRFs : {n m : ℕ} → Vec (ℕ ^ n → ℕ) m → Set where
    ⟦_⟧ : {x : ℕ} {f : ℕ ^ nsuc x → ℕ}
           → PRF {nsuc x} f
           → PRFs {nsuc x} {nsuc nzero} (f ∷ [])
    step : (x y : ℕ) (f : ℕ ^ nsuc x → ℕ)
           → (fs : Vec (ℕ ^ nsuc x → ℕ) y)
           → PRFs {nsuc x} {y} fs
           → PRFs {nsuc x} {nsuc y} (f ∷ fs)



rec  : {n : ℕ}
         → (g : ℕ ^ n → ℕ) → (prfg : PRF {n} g)
         → (h : ℕ ^ (nsuc (nsuc n)) → ℕ) → (prfh : PRF {(nsuc (nsuc n))} h)
         → PRF {nsuc n} (rec' {n} g h)
-}

{-
-- 例1.3.2

pred : ℕ ^ 1 → ℕ
pred (nzero  ∷ []) = nzero
pred (nsuc x ∷ []) = x

pred-is-prf : PRF {1} pred
pred-is-prf = {!!}
-}
