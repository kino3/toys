module Knuth1-2-3 where

-- The Art of Computer Programming I
-- 1.2.3 Page.27

open import Data.Nat
open import Data.List
open import Data.Bool
open import Data.Product using (_×_;proj₁;proj₂)

index : List ℕ → List ℕ
index [] = []
index (x ∷ xs) = index xs ∷ʳ (length (x ∷ xs))

iList : List ℕ → List (ℕ × ℕ)
iList xs = zip (index xs) xs

Σ' : (ℕ → Bool) → List (ℕ × ℕ) → ℕ
Σ' cond []       = 0
Σ' cond (x ∷ xs) with cond (proj₁ x)
Σ' cond (x ∷ xs) | true  = proj₂ x + Σ' cond xs
Σ' cond (x ∷ xs) | false = Σ' cond xs

Σ : (ℕ → Bool) → List ℕ → ℕ
Σ cond xs = Σ' cond (iList xs)

