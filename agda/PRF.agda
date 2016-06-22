module PRF where

-- Primitive Recursive Function (PRF)
-- by K. Takahashi's Book

open import Data.Nat renaming (zero to nzero; suc to nsuc) hiding (pred)
open import Data.Vec hiding ([_])
open import Relation.Nullary using (yes;no)

-- 定義1.3.1

_^_ : Set → ℕ → Set
X ^ n = Vec X n

data PRF : Set → Set where
  -- (1)
  zero : PRF (ℕ ^ 0)
  suc  : ℕ → PRF (ℕ ^ 1)
  p    : (n : ℕ) (i : ℕ) {p1 : 1 ≤ i} {p2 : i ≤ n} → ℕ ^ n → PRF (ℕ ^ n)
  -- (2)
  cmp  : {m n : ℕ} {prf : 1 ≤ m}
         → PRF (ℕ ^ m) → Vec (PRF ℕ ^ n) m → PRF (ℕ ^ n)
  -- (3)
  rec  : {n : ℕ} → PRF (ℕ ^ n) → PRF (ℕ ^ (2 + n)) → PRF (ℕ ^ (1 + n)) 

-- FIXME: change apply to eval
-- function application 

{-# NON_TERMINATING #-}
_[_] : {n : ℕ} → PRF (ℕ ^ n) → Vec ℕ n → ℕ
f [ xs ] = {!!}

{-
zero [ [] ]     = nzero
suc  [ x ∷ [] ] = nsuc x
p       _        0  {()} {_}  [ xs ] 
p       0  (nsuc i) {_}  {()} [ xs ]
p (nsuc n) (nsuc nzero)    {s≤s z≤n} {s≤s p2} [ x ∷ xs ] = x
p (nsuc n) (nsuc (nsuc i)) {s≤s z≤n} {s≤s p2} [ x ∷ xs ] = p n (nsuc i) {s≤s z≤n} {p2} [ xs ]

{-
p nzero {()} [ xs ]
p (nsuc nzero)    {s≤s prf} [ x ∷ xs ] = x
p (nsuc (nsuc n)) {s≤s prf} [ x ∷ xs ] = (p (nsuc n) {s≤s z≤n}) [ xs ]
-}
cmp {nzero}  {_} {()}  g gj [ xs ] 
cmp {nsuc m} {n} {prf} g gj [ xs ] = g [ map (_[ xs ]) gj ]
rec g h [ xs ] with last xs
rec g h [ xs ] | nzero  = g [ init xs ]
rec g h [ xs ] | nsuc y = h [ (init xs) ∷ʳ y ∷ʳ (rec g h [ init xs ∷ʳ y ]) ]
-}
{-
one : PRF 0
one = cmp {prf = s≤s z≤n} suc (zero ∷ [])

pred : PRF 1
pred = rec {!!} (p 2 1) --rec {!!} (p 2 {s≤s z≤n})
-}


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
