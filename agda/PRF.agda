module PRF where
-- Primitive Recursive Function (PRF)
-- by K. Takahashi's Book

import Data.Nat as N
open N using (ℕ)
import Data.Vec as V
open V
import Data.Fin as F renaming (zero to one) -- avoid confusion...
open F using (Fin)
import Function as Fun

-- Vec can be seen as cartesian product 
_^_ : Set → ℕ → Set
s ^ n = V.Vec s n

data INI : (n : ℕ) → Set where
  zero : INI 0 
  suc  : INI 1
  p    : {n : ℕ} → Fin n → INI n

hoge : INI 2
hoge = p F.one -- it means p^2_1

applyI : {n : ℕ} → INI n → ℕ ^ n → ℕ
applyI zero  = λ _ → 0
applyI suc   = λ x → N.suc (V.head x)
applyI (p i) = V.lookup i

data PRF : (n : ℕ) → Set where
  ini : {n : ℕ} → INI n → PRF n
  cmp : {n m : ℕ} → PRF m → Vec (PRF n) m → PRF n 
  rec : {n : ℕ} → PRF n → PRF (N.suc (N.suc n)) → PRF (N.suc n)

applyP : {n : ℕ} → PRF n → ℕ ^ n → ℕ
applyP (ini funI)    = applyI funI
applyP (cmp g gjs)   = applyP g Fun.∘ applyP' gjs
  where
    applyP' : {n k : ℕ} → Vec (PRF n) k → ℕ ^ n → ℕ ^ k
    applyP' []         xs = []
    applyP' (g1 ∷ gjs) xs = applyP g1 xs ∷ applyP' gjs xs
applyP (rec g h) (N.zero  ∷ xs) = applyP g xs
applyP (rec g h) (N.suc x ∷ xs) = applyP h (x ∷ applyP (rec g h) (x ∷ xs) ∷ xs)

