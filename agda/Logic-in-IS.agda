module Logic-in-IS where

-- 情報科学における論理 in Agda
-- http://www.nippyo.co.jp/book/1292.html

-- とりあえずＬＫのところまでかいてみる。

postulate
  命題変数 : Set 

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

data Bool : Set where
  t f : Bool

命題変数の付値 : Set
命題変数の付値 = 命題変数 → Bool

hoge : 命題変数の付値
hoge x = t

付値 : Set
付値 = 論理式 → Bool

open import Relation.Binary.Core renaming (_≡_ to _≈_)
トートロジー : 論理式 → Set
トートロジー A = ∀ (v : 付値) → v A ≈ t

_は_である : 論理式 → (論理式 → Set) → Set
a は P である = P a

恒真 = トートロジー


{-
付値 (< x >) = 命題変数の付値 ?
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
-}

-- 特にp,q,rに真偽は定めていない。

-- 定理1.1
-- 与えられた論理式がトートロジーか否かは決定可能である。
{-
thm1-1 : {A : 論理式} → Decidable (A は トートロジー である)
thm1-1 = {!!}
-}


-- 例1.3
ex1-3 : ∀ p q → ((p ∧ (p ⊃ q)) ⊃ q ) は トートロジー である
ex1-3 p q v with v p | v q
ex1-3 p q v | t | t = {!!}
ex1-3 p q v | t | f = {!!}
ex1-3 p q v | f | t = {!!}
ex1-3 p q v | f | f = {!!}

{-
ex1-3 p q with p の付値 | q の付値 -- withで場合分け
ex1-3 p q | t | t = refl
ex1-3 p q | t | f = refl
ex1-3 p q | f | t = refl
ex1-3 p q | f | f = refl
-- めんどくさいが、論理式の形とその評価した値とを厳密に区別することはだいじ。
-- refl ではなくeqreasoningをつかってみるのもいいかもしれない。



open import Data.Product
open import Data.List
命題変数一覧 : 論理式 → List 命題変数
命題変数一覧 < x > = [ x ]
命題変数一覧 (A ∧ B) = 命題変数一覧 A ++ 命題変数一覧 B
命題変数一覧 (A ∨ B) = 命題変数一覧 A ++ 命題変数一覧 B
命題変数一覧 (A ⊃ B) = 命題変数一覧 A ++ 命題変数一覧 B
命題変数一覧 (¬ A) = 命題変数一覧 A

hoge : List 命題変数 → List Bool
hoge [] = []
hoge (x ∷ l) = 命題変数の付値 x ∷ hoge l


充足可能 : (A : 論理式) → Set
充足可能 A = {!(xs : 命題変数一覧 A) → ?!}

問1-2 : ∀ p q r → (((p ∨ q) ⊃ r) ∨ (p ∧ q)) は 充足可能 である
問1-2 p q r = {!!}
-}
