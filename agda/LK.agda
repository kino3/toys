module LK where

-- 情報科学における論理 in Agda
-- http://www.nippyo.co.jp/book/1292.html

-- とりあえずＬＫのところをかいてみる。

-- 定義1.1
postulate
  命題変数 : Set 

data 論理式 : Set where
  var : 命題変数 → 論理式
  _∧_ : 論理式 → 論理式 → 論理式
  _∨_ : 論理式 → 論理式 → 論理式
  _⊃_ : 論理式 → 論理式 → 論理式
  ¬_  : 論理式 → 論理式

infix 100 ¬_

data Bool : Set where
  t f : Bool

open import Data.Nat
open import Data.List
getVar : 論理式 → List 命題変数
getVar (var x) = x ∷ []
getVar (A ∧ B) = getVar A ++ getVar B 
getVar (A ∨ B) = getVar A ++ getVar B
getVar (A ⊃ B) = getVar A ++ getVar B
getVar (¬ A) = [] ++ getVar A


postulate
  命題変数の付値 : 命題変数 → Bool

付値 : 論理式 → Bool
付値 (var x) = 命題変数の付値 x
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

