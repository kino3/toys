module ronri20150317 where

--open import Data.Nat

-- Inductive definition of Natural Numbers.
data ℕ : Set where
  zero : ℕ
  S    : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

plus : ℕ → ℕ → ℕ
plus zero y = y
plus (S x) y = S (plus x y)

_+_ : ℕ → ℕ → ℕ
x + y = plus x y

_*_ : ℕ → ℕ → ℕ
zero * y = zero
S x  * y = plus (x * y) y

_^_ : ℕ → ℕ → ℕ
x ^ zero = S zero
x ^ S y = (x ^ y) * x

pred : ℕ → ℕ
pred zero = zero
pred (S x) = x

monus : ℕ → ℕ → ℕ
monus x zero = x
monus x (S y) = pred (monus x y)

_∸_ : ℕ → ℕ → ℕ
x ∸ y = monus x y

-- bounded minimization
g : (f : ℕ → ℕ → ℕ) → ℕ → ℕ → ℕ
g f x z = h x z z where
  h : ℕ → ℕ → ℕ → ℕ
  h x z zero = zero
  h x z (S w) = ((S zero ∸ f x (z ∸ S w)) * (z ∸ S w))
              + ((S zero ∸ (S zero ∸ f x (z ∸ S w))) * h x z w)
f1 : ℕ → ℕ → ℕ
f1 x y = x ∸ ((S (S zero) * y) + S zero)

div2 : ℕ → ℕ
div2 x = g f1 x x

{-
data くだもの : Set where
  りんご : くだもの
  みかん : くだもの
  ばなな : ℕ → くだもの

きょうのおひる : くだもの
きょうのおひる = りんご
-}
