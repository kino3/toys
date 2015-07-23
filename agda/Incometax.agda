module Incometax where

open import Data.Nat --hiding (_<_)

-- view
data _<=_ : ℕ → ℕ → Set where
  case1 : {n : ℕ} → n <= 1800000
  case2 :     1800001 <=  3600000 
  case3 :     3600001 <=  6600000
  case4 :     6600001 <= 10000000
  case5 :    10000001 <= 15000000
  case6 : {n : ℕ} → 15000001 <= n
{-
record 人情報 (n : ℕ) : Set where
  field
    給与年収 : 給与年収-型 n

給与所得の控除額 : ℕ → ℕ
給与所得の控除額 n = {!!}


所得税計算 : 人情報 → ℕ
所得税計算 a = {!!}
-}
