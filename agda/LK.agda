module LK where

-- 情報科学における論理 in Agda
-- http://www.nippyo.co.jp/book/1292.html

-- とりあえずＬＫのところをかいてみる。

open import Data.Char
open import Data.String using (String)

data Bool : Set where
  t f : Bool

record 命題変数 : Set where
  constructor _,_
  field
    Label : Char
    真偽 : Bool
    --{文} : String
    -- 命題変数を具体的にひとつ定義した時点で、真偽もきまっている、という立場。

-- 定義1.1

data 論理式 : Set where
  <_> : 命題変数 → 論理式
  _∧_ : 論理式 → 論理式 → 論理式
  _∨_ : 論理式 → 論理式 → 論理式
  _⊃_ : 論理式 → 論理式 → 論理式
  ¬_  : 論理式 → 論理式

infix 100 ¬_

-- 例1.1
sample1 : 論理式
sample1 = < 'p' , {!!} > ⊃ (< 'q' , {!!} > ∨ ¬ < 'r' , {!!} >)
-- 特にp,q,rに真偽は定めていない。しかし、みづらい。。。

付値 : 論理式 → Bool
付値 (< x >) = 命題変数.真偽 x
付値 (A ∧ B) with 付値 A | 付値 B
付値 (A ∧ B) | t | t = t
付値 (A ∧ B) | t | f = f
付値 (A ∧ B) | f | t = f
付値 (A ∧ B) | f | f = f
付値 (A ∨ B) with 付値 A | 付値 B
付値 (A ∨ B) | t | t = t
付値 (A ∨ B) | t | f = t
付値 (A ∨ B) | f | t = t
付値 (A ∨ B) | f | f = f
付値 (A ⊃ B) with 付値 A | 付値 B
付値 (A ⊃ B) | t | t = t
付値 (A ⊃ B) | t | f = f
付値 (A ⊃ B) | f | t = t
付値 (A ⊃ B) | f | f = t
付値 (¬ A) with 付値 A
付値 (¬ A) | t = f
付値 (¬ A) | f = t

open import Relation.Binary.Core

_はトートロジーである : 論理式 → Set
A はトートロジーである = 付値 A ≡ t

_は恒真である : 論理式 → Set
A は恒真である = A はトートロジーである

-- 定理1.1

-- 例1.3
ex1-3 : ∀ p q → ((p ∧ (p ⊃ q)) ⊃ q ) はトートロジーである
ex1-3 p q with 付値 p | 付値 q
ex1-3 p q | t | t = refl
ex1-3 p q | t | f = refl
ex1-3 p q | f | t = refl
ex1-3 p q | f | f = refl
-- めんどくさいが、論理式の形とその評価した値とを厳密に区別することはだいじ。
-- refl ではなくeqreasoningをつかってみるのもいいかもしれない。

