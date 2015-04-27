module Ronri5-1 where

open import Data.Nat

true : ℕ → (ℕ → ℕ)
true x = λ y → x

false : ℕ → (ℕ → ℕ)
false x = λ y → y

if_then_else_ : (P : ℕ → (ℕ → ℕ)) → ℕ → ℕ → ℕ
if P then x else y = (P x) y 

-- true 1 2 を C-c C-n で評価すると 1
-- false 1 2 を C-c C-n で評価すると 2

open import Relation.Binary.Core
lemma1 : ∀ x y → if true then x else y ≡ x
lemma1 x y = refl

lemma2 : ∀ x y → if false then x else y ≡ y
lemma2 x y = refl

-- ということなので、うえのtrue,falseを一般的な⊤,⊥とかんがえる「ことができる」。
-- みためはちがうけれども、おなじようなものとかんがえることができる、ということ。
-- 実際、以下の標準ライブラリの定義とはちがうよね。
open import Data.Bool

church0 : (ℕ → ℕ) → (ℕ → ℕ)
church0 = λ f → (λ x → x)

church1 : (ℕ → ℕ) → (ℕ → ℕ)
church1 = λ f → (λ x → f x)

open import Data.String
data Lambda-Term : Set where
  var : String → Lambda-Term
  [_,_] : Lambda-Term → Lambda-Term → Lambda-Term
  --入_,_ : 

hoge : Lambda-Term
hoge = [ var "x" , var "y" ]

{-# NO_TERMINATION_CHECK #-}
church : ℕ → ((ℕ → ℕ) → ℕ → ℕ)
church zero    = λ f x → x
church (suc x) = λ f x → f (church x f x)

