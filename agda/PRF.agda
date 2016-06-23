module PRF where
-- Primitive Recursive Function (PRF)
-- by K. Takahashi's Book

open import Data.Nat renaming (zero to nzero; suc to nsuc) hiding (pred)
open import Data.Vec
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)

-- Vec can be seen as cartesian product 
_^_ : Set → ℕ → Set
s ^ n = Vec s n

data Initial : ℕ → Set where
  zero : Initial 0 
  suc  : (n : ℕ) → Initial 1
  p    : (n : ℕ) (i : ℕ) → Vec ℕ n → Initial n

hoge : Initial 2
hoge = p 2 1 (5 ∷ (10 ∷ []))

evalI : {n : ℕ} → Initial n → ℕ
evalI zero       = 0
evalI (suc n)    = nsuc n
evalI (p  nzero    _        []     ) = 0
evalI (p (nsuc n)  0        _      ) = 0
evalI (p (nsuc n)  1       (x ∷ xs)) = x
evalI (p (nsuc n) (nsuc i) (x ∷ xs)) = evalI (p n i xs)

data PRF : Set where
  ini : {n : ℕ} → Initial n → PRF
  rec : {n : ℕ} → PRF → PRF → ℕ ^ (nsuc n) → PRF

evalP : PRF → ℕ
evalP (ini f)   = evalI f
evalP (rec g h xs) with last xs
evalP (rec g h xs) | nzero  = evalP g
evalP (rec g h xs) | nsuc y = evalP h

one : PRF
one = ini (suc nzero)

pred : ℕ → PRF
pred  0       = ini zero
pred (nsuc y) = ini (p 2 2 ({!!} ∷ ({!!} ∷ [])))

{-
  {-# NON_TERMINATING #-}
  rec' : {n : ℕ} → (g : ℕ ^ n → ℕ) → (h : ℕ ^ (2 + n) → ℕ) → (ℕ ^ (nsuc n) → ℕ) 
  rec' {nzero}  g h xs = nzero
  rec' {nsuc n} g h xs with last xs
  rec' {nsuc n} g h xs       | nzero  = g (init xs) --g (init xs)
  rec' {nsuc n} g h (x ∷ xs) | nsuc y = h (init (x ∷ xs) ∷ʳ y ∷ʳ rec' g h (x ∷ xs)) --
-}

{-
  cmp : {m n : ℕ} {prf : 1 ≤ m}
         → (g : ℕ ^ m → ℕ) → PRF {m} g
         → (gjs : Vec (ℕ ^ n → ℕ) m) → PRFs {n} {m} gjs
         → PRF {n} (λ xs → g (gjs ⊛ replicate xs)) 
         
  -- All functions in Vec are Primitive recursive.
  data PRFs : {n m : ℕ} → Vec (ℕ ^ n → ℕ) m → Set where
    base : (x : ℕ) (f : ℕ ^ nsuc x → ℕ)
           → PRF {nsuc x} f
           → PRFs {nsuc x} {nsuc nzero} (f ∷ [])
    step : (x y : ℕ) (f : ℕ ^ nsuc x → ℕ)
           → (fs : Vec (ℕ ^ nsuc x → ℕ) y)
           → PRFs {nsuc x} {y} fs
           → PRFs {nsuc x} {nsuc y} (f ∷ fs)
-}
{-


proj2-1 : ℕ ^ 2 → ℕ
proj2-1 (x ∷ y ∷ []) = y

pred : ℕ ^ 1 → ℕ
pred (nzero ∷ []) = nzero
pred (nsuc x ∷ []) = x 

pred-is-prf : PRF {1} pred
pred-is-prf = {!!}
-}

{-
data Initial : {n : ℕ} → (ℕ ^ n → ℕ) → Set where
  zero : Initial {0} (λ x → 0)
  suc  : Initial {1} (λ {(n ∷ []) → nsuc n})
  p    : {n : ℕ} {i : Fin (nsuc n)} → Initial {nsuc n} (λ ns → lookup i ns)

mutual
  data PRF : {n : ℕ} → (ℕ ^ n → ℕ) → Set where
    ini : {x : ℕ} {f : ℕ ^ x → ℕ} → Initial {x} f → PRF {x} f
    cmp : {m n : ℕ} {prf : 1 ≤ m}
         → (g : ℕ ^ m → ℕ) → PRF {m} g
         → (gjs : Vec (ℕ ^ n → ℕ) m) → PRFs {n} {m} gjs
         → PRF {n} (λ xs → g (gjs ⊛ replicate xs)) 
    rec  : {n : ℕ}
         → (g : ℕ ^ n → ℕ) → (prfg : PRF {n} g)
         → (h : ℕ ^ (nsuc (nsuc n)) → ℕ) → (prfh : PRF {(nsuc (nsuc n))} h)
         → PRF {nsuc n} (rec' g h) 
         
  -- All functions in Vec are Primitive recursive.
  data PRFs : {n m : ℕ} → Vec (ℕ ^ n → ℕ) m → Set where
    base : (x : ℕ) (f : ℕ ^ nsuc x → ℕ)
           → PRF {nsuc x} f
           → PRFs {nsuc x} {nsuc nzero} (f ∷ [])
    step : (x y : ℕ) (f : ℕ ^ nsuc x → ℕ)
           → (fs : Vec (ℕ ^ nsuc x → ℕ) y)
           → PRFs {nsuc x} {y} fs
           → PRFs {nsuc x} {nsuc y} (f ∷ fs)

  {-# NON_TERMINATING #-}
  rec' : {n : ℕ} → (g : ℕ ^ n → ℕ) → (h : ℕ ^ (2 + n) → ℕ) → (ℕ ^ (nsuc n) → ℕ) 
  rec' {nzero}  g h xs = nzero
  rec' {nsuc n} g h xs with last xs
  rec' {nsuc n} g h xs       | nzero  = g (init xs) --g (init xs)
  rec' {nsuc n} g h (x ∷ xs) | nsuc y = h (init (x ∷ xs) ∷ʳ y ∷ʳ rec' g h (x ∷ xs)) --

proj2-1 : ℕ ^ 2 → ℕ
proj2-1 (x ∷ y ∷ []) = y

pred : ℕ ^ 1 → ℕ
pred (nzero ∷ []) = nzero
pred (nsuc x ∷ []) = x 

pred-is-prf : PRF {1} pred
pred-is-prf = {!!}
-}
{-

pred-is-prf = rec {0} (λ _ → 0) (ini {0} zero)
                      proj2-1   (ini {2} (p {1} {{!!}}))
-}
