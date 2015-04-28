module LK where

-- 情報科学における論理 in Agda
-- http://www.nippyo.co.jp/book/1292.html

-- とりあえずＬＫのところをかいてみる。

open import Data.Char
open import Data.String using (String)

data 真偽値 : Set where
  真 偽 : 真偽値

record 命題変数 : Set where
  field
    真偽 : 真偽値
    -- 命題変数を具体的にひとつ定義した時点で、真偽もきまっている、という立場。
    -- Labelについては、命題変数を具体的にひとつ定義した時点の名前とするのが自然なので、ここでは定義しない。
    -- そうすることで、名前の重複チェックをAgdaの検査に還元できる。

-- 定義1.1

data 論理式 : Set where
  <_> : 命題変数 → 論理式
  _∧_ : 論理式 → 論理式 → 論理式
  _∨_ : 論理式 → 論理式 → 論理式
  _⊃_ : 論理式 → 論理式 → 論理式
  ¬_  : 論理式 → 論理式

infix 100 ¬_

-- 例1.1
sample1 : (p q r : 命題変数) → 論理式
sample1 p q r = < p > ⊃ ( < q > ∨ ¬ < r >)
-- 特にp,q,rに真偽は定めていない。

data Bool : Set where
  t f : Bool

taiou : 真偽値 → Bool
taiou 真 = t
taiou 偽 = f

付値 : 論理式 → Bool
付値 (< x >) = taiou (命題変数.真偽 x) 
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

v[_] : 論理式 → Bool
v[ x ] = 付値 x  

open import Relation.Binary.Core renaming (_≡_ to _≈_)

_は_である : 論理式 → (論理式 → Set) → Set
a は P である = P a

トートロジー : 論理式 → Set
トートロジー A = 付値 A ≈ t

恒真 = トートロジー

-- 定理1.1

-- 例1.3
ex1-3 : ∀ p q → ((p ∧ (p ⊃ q)) ⊃ q ) は トートロジー である
ex1-3 p q with 付値 p | 付値 q
ex1-3 p q | t | t = refl
ex1-3 p q | t | f = refl
ex1-3 p q | f | t = refl
ex1-3 p q | f | f = refl
-- めんどくさいが、論理式の形とその評価した値とを厳密に区別することはだいじ。
-- refl ではなくeqreasoningをつかってみるのもいいかもしれない。

