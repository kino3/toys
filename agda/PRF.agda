module PRF where
-- Primitive Recursive Function (PRF)
-- by K. Takahashi's Book

open import Data.Nat renaming (zero to nzero; suc to nsuc)
open import Data.Product
open import Data.Empty using (⊥)

-- cartesian product
_^_ : Set → ℕ → Set
s ^ 0  = ⊥
s ^ nsuc nzero = s
s ^ nsuc n     = s × (s ^ n) -- (s ^ n) × s ?

proj : {n i : ℕ} {prf : 1 ≤ i} {prf2 : i ≤ n} → ℕ ^ n → ℕ
proj {nzero}  {nzero}  {()} 
proj {nzero}  {nsuc i} {s≤s prf} {()} 
proj {nsuc n} {nzero}  {()}
proj {nsuc nzero}    {nsuc .0}       {s≤s z≤n} {s≤s z≤n}   n       = n
proj {nsuc (nsuc n)} {nsuc .0}       {s≤s z≤n} {s≤s z≤n}  (x , xs) = x
proj {nsuc (nsuc n)} {nsuc (nsuc i)} {s≤s z≤n} {s≤s prf2} (x , xs) = proj {nsuc n} {nsuc i} {s≤s z≤n} {prf2} xs

data Initial : {n : ℕ} → (ℕ ^ n → ℕ) → Set where
  zero : Initial {0} (λ ())
  suc  : Initial {1} (λ n → n + 1)
  p    : {n i : ℕ} {prf : 1 ≤ i} {prf2 : i ≤ n} → Initial {n} (λ ns → proj {n} {i} {prf} {prf2} ns)
     
open import Data.Vec hiding (init)
open import Data.Bool

-- extract functions out of a vector
extract : {m n : ℕ} → Vec (ℕ ^ n → ℕ) (nsuc m) → ℕ ^ n → ℕ ^ nsuc m
extract {nzero}  {n} (f ∷ []) x = f x
extract {nsuc m} {nzero} (f ∷ fs) ()
extract {nsuc m} {nsuc nzero}    (f ∷ fs) x  = f x  , extract {m} {nsuc nzero} fs x
extract {nsuc m} {nsuc (nsuc n)} (f ∷ fs) x→ = f x→ , extract {m} {nsuc (nsuc n)} fs x→

comp : {m n : ℕ} (g : ℕ ^ m → ℕ) (gjs : Vec (ℕ ^ n → ℕ) m) → (ℕ ^ n → ℕ)
comp {nzero}  {nzero}  g gjs = λ ()
comp {nzero}  {nsuc n} g []  = λ xs → nzero -- temporary
comp {nsuc m} {nzero}  g gjs = λ ()
comp {nsuc nzero}    {nsuc n}        g (g1 ∷ [])  x  = g (g1 x)
comp {nsuc (nsuc m)} {nsuc nzero}    g (g1 ∷ gjs) x  = g (g1 x  , extract {m} {nsuc nzero}    gjs x )
comp {nsuc (nsuc m)} {nsuc (nsuc n)} g (g1 ∷ gjs) x→ = g (g1 x→ , extract {m} {nsuc (nsuc n)} gjs x→)

rec : {n : ℕ} → (ℕ ^ n → ℕ) → (ℕ ^ (nsuc (nsuc n)) → ℕ) → (ℕ ^ (nsuc n) → ℕ)
rec {0} g h nzero = 0
rec {0} g h (nsuc x) = 0
-- since _,_ is left-assoc, we exchange arguments such as (x,0) (x,y+1) -> (0,x) (y+1,x)
rec {1} g h (     0 , x)              = g x
rec {1} g h (nsuc y , x)              = h (y , (x , (rec {1} g h (y , x))))
rec {nsuc (nsuc x)} g h (     0 , xs) = g xs
rec {nsuc (nsuc x)} g h (nsuc y , xs) = ?

mutual
  data PRF : {n : ℕ} → (ℕ ^ n → ℕ) → Set where
    init : {x : ℕ} {f : ℕ ^ x → ℕ} → Initial {x} f → PRF {x} f
    cmp  : {m n : ℕ} {prf : 1 ≤ m}
         → (g : ℕ ^ m → ℕ) → PRF {m} g
         → (gjs : Vec (ℕ ^ n → ℕ) m) → PRFs {n} {m} gjs
         → PRF {n} (comp {m} {n} g gjs)
    --rec  : 

  -- All functions in Vec are Primitive recursive.
  data PRFs : {n m : ℕ} → Vec (ℕ ^ n → ℕ) m → Set where
    base : (x : ℕ) (f : ℕ ^ nsuc x → ℕ)
           → PRF {nsuc x} f
           → PRFs {nsuc x} {nsuc nzero} (f ∷ [])
    step : (x y : ℕ) (f : ℕ ^ nsuc x → ℕ)
           → (fs : Vec (ℕ ^ nsuc x → ℕ) y)
           → PRFs {nsuc x} {y} fs
           → PRFs {nsuc x} {nsuc y} (f ∷ fs)

{-
rec : {n : ℕ} → PRF (ℕ ^ n → ℕ) → PRF (ℕ ^ (n + 2) → ℕ) → PRF (ℕ ^ (n + 1) → ℕ)
rec g h = {!!}
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
