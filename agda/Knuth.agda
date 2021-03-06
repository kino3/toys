module Knuth where

-- The Art of Computer Programming
-- 1.2.2 Page.22

-- law of exponents
open import Data.Nat
open import Relation.Binary.Core
open import Relation.Binary.EqReasoning

-- def of exponential
_^_ : ℕ → ℕ → ℕ
b ^ zero = 1
b ^ suc n = b ^ n * b

theorem1 : (b x y : ℕ) → b ^ (x + y) ≡ (b ^ x) * (b ^ y)
theorem1 b zero zero = refl
theorem1 b zero (suc n) = {!!} 
{-  begin
    b ^ (zero + suc n)
  ≈⟨ ? ⟩
    ?
  ∎-}
theorem1 b (suc x) zero = {!!}
theorem1 b (suc x) (suc y) = {!!}

theorem2 : (b x y : ℕ) → (b ^ x) ^ y ≡ b ^ (x * y)
theorem2 b x y = {!!}

{-
n*0≡0 : ∀ n → n * 0 ≡ 0
n*0≡0 zero    = refl
n*0≡0 (suc n) =
  begin
    suc n * 0
  ≈⟨ refl ⟩
    n * 0 + 0
  ≈⟨ refl ⟩
    n * 0
  ≈⟨ n*0≡0 n ⟩
    0
  ∎
-}

{-
open import Data.Rational
open import Data.Vec
q : (k : ℕ) → Vec ℕ k → Vec ℚ k
q zero [] = []
q (suc x) (n ∷ ns) = record { numerator = {!!} ; denominator-1 = {!!} ; isCoprime = {!!} } ∷ {!!}

hoge : Vec ℕ 3
hoge = 2 ∷ 1 ∷ 4 ∷ []
-}
{-
q : (k : ℕ) → Vec ℕ k → Vec ℚ k
        /|\
         |
下記のコードのこの ℕ に関してエラーが出ます．

====================================

module sigma where
-}
open import Data.Nat
open import Data.Vec
open import Data.Rational

q : (k : ℕ) → Vec ℕ k → Vec ℚ k
q = {!!}
{-
====================================


また，僕が昨日まで質問していた sigma の定義では，
ベクタのどの要素から足し始めるかの i を与えること
については考えていなかったことに気づきました．

よって，Σ の型は下記のようになると考えます．おかし
いところがあったら教えて下さい．
-}
Σ : (k : ℕ) -> (i : ℕ) -> Vec ℚ k -> ℚ
Σ k i = {!!}

Σ2 : ∀ k i -> Vec ℕ (k ∸ i + 1) -> Vec ℕ (k ∸ i + 1)
Σ2 = {!!}
