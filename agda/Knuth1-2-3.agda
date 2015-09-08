module Knuth1-2-3 where

-- The Art of Computer Programming I
-- 1.2.3 Page.27

open import Data.Nat
open import Data.List
open import Data.Bool
open import Data.Product using (_×_;proj₁;proj₂;_,_)
open import Function

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

open import Relation.Nullary
cond1 : ℕ → Bool
cond1 n with 1 ≤? n
cond1 n | yes p with n ≤? 5
cond1 n | yes p | yes p2 = true
cond1 n | yes p | no ¬p2 = false
cond1 n | no ¬p = false

sample : List ℕ 
sample = 30 ∷ 20 ∷ 10 ∷ 40 ∷ 50 ∷ [] 

x : ℕ
x = Σ cond1 sample

