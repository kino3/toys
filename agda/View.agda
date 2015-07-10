module View where
-- Dependently typed programming in Agda
-- 3 Programming Techniques

-- 3.1 Views

-- Natural number parity

open import Data.Nat renaming (ℕ to Nat) 

data Parity : Nat → Set where
  even : (k : Nat) → Parity (k * 2)
  odd  : (k : Nat) → Parity (1 + k * 2)

parity : (n : Nat) → Parity n
parity zero    = even zero
parity (suc n) with parity n
parity (suc .(k * 2))       | even k = odd k
parity (suc .(suc (k * 2))) | odd  k = even (suc k)

half : Nat → Nat
half n with parity n
half .(k * 2)       | even k = k
half .(suc (k * 2)) | odd  k = k

