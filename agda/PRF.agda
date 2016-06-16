module PRF where
-- Primitive Recursive Function (PRF)
-- by K. Takahashi's Book

open import Data.Nat renaming (zero to nzero; suc to nsuc)
open import Data.Vec
open import Data.Fin using (Fin)

-- Vec can be seen as cartesian product 
_^_ : Set → ℕ → Set
s ^ n = Vec s n

data Initial : {n : ℕ} → (ℕ ^ n → ℕ) → Set where
  zero : Initial {0} (λ x → 0)
  suc  : Initial {1} (λ {(n ∷ []) → nsuc n})
  p    : {n : ℕ} {i : Fin (nsuc n)} → Initial {nsuc n} (λ ns → lookup i ns)

--FIXME : need assumption that g,h is PRF

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
         → PRF {nsuc n} (rec' {n} g prfg h prfh)
         
  -- All functions in Vec are Primitive recursive.
  data PRFs : {n m : ℕ} → Vec (ℕ ^ n → ℕ) m → Set where
    base : (x : ℕ) (f : ℕ ^ nsuc x → ℕ)
           → PRF {nsuc x} f
           → PRFs {nsuc x} {nsuc nzero} (f ∷ [])
    step : (x y : ℕ) (f : ℕ ^ nsuc x → ℕ)
           → (fs : Vec (ℕ ^ nsuc x → ℕ) y)
           → PRFs {nsuc x} {y} fs
           → PRFs {nsuc x} {nsuc y} (f ∷ fs)

  rec' : {n : ℕ} → (g : ℕ ^ n → ℕ) → PRF g → (h : ℕ ^ (2 + n) → ℕ) → PRF h → (ℕ ^ (nsuc n) → ℕ) 
  rec' {nzero}  g prfg h prfh xs = nzero
  rec' {nsuc n} g prfg h prfh xs with last xs
  rec' {nsuc n} g prfg h prfh xs       | nzero  = {!!} --g (init xs)
  rec' {nsuc n} g prfg h prfh (x ∷ xs) | nsuc y = {!!} --h (init (x ∷ xs) ∷ʳ y ∷ʳ rec' g prfg h prfh (x ∷ xs))


