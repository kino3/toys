module Ronri4-2 where
-- 論理と計算のしくみ 4.2 帰納的関数

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
infixl 5 _+_
{-# BUILTIN NATPLUS _+_ #-}

_*_ : ℕ → ℕ → ℕ
zero * y = zero
S x  * y = plus (x * y) y
{-# BUILTIN NATTIMES _*_ #-}


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
--{-# BUILTIN NATMINUS _∸_ #-}

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

-- coding
p : ℕ → ℕ → ℕ
p x y = div2 ((x + y + 1) * (x + y)) + y

p1' : ℕ → ℕ → ℕ
p1' z x = p x (g (λ x y → (p x y ∸ z) + (z ∸ p x y)) x (z + 1))

p1 : ℕ → ℕ 
p1 z = g (λ z x → (p1' z x ∸ z) + (z ∸ p1' z x)) z (z + 1)

{-
open import Relation.Binary.Core
theorem : (x y : ℕ) → x ≡ p1 (p x y)
theorem zero zero = refl
theorem zero (S zero) = refl
theorem zero (S (S y)) = {!refl!}
theorem (S x) y = {!!}
-}
p2 : ℕ → ℕ
p2 z = {!!}

b : ℕ → ℕ → ℕ 
b y zero = y
b y (S x) = {!!}



{-
div2' : ℕ → ℕ
div2' x with x ∸ S zero
div2' x | zero = zero
div2' x | S y = div2' (x ∸ 2) + 1
-}

