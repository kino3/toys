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


open import Data.Fin
func2list : {n : ℕ} → (Fin n → ℕ) → List (ℕ × ℕ)
func2list {zero} f  = {!!}
func2list {suc n} f = {!!}

Σ2 : {n : ℕ} → (Fin n → Bool) → (Fin n → ℕ) → ℕ
Σ2 cond f = {!!}

Σ3 : (ℕ → Bool) → (ℕ → ℕ) → ℕ
Σ3 cond f = foldl {!!} 0 {!!}
