module TPPmark2016 where

open import Data.List as L
open import Data.Nat as N

-- first implementation with respect to ocaml sample code.
-- http://pllab.is.ocha.ac.jp/~asai/tpp2016/remove.ml
remove : {A : Set} → List A → ℕ → List A
remove []        j      = []
remove (x ∷ xs) zero    = xs
remove (x ∷ xs) (suc j) = remove xs j

remove-lst : {A : Set} → List (List A) → ℕ → ℕ → List (List A)
remove-lst [] i j                   = []
remove-lst (first ∷ rest) zero j    = remove first j ∷ rest
remove-lst (first ∷ rest) (suc i) j = first ∷ remove-lst rest i j

open import Data.Unit hiding (_≤_)
open import Data.Empty

get : {A : Set} → List A → ℕ → A
get = {!!}

remove-lst' : {A : Set} → (lst : List (List A)) → (i : ℕ) → (j : ℕ)
  → suc i ≤ length lst  → suc j ≤ length (get lst i) → List (List A)
remove-lst' lst i j prf1 prf2 = {!!}
