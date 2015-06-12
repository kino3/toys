module Logic-in-IS where

-- 情報科学における論理 in Agda
-- http://www.nippyo.co.jp/book/1292.html

-- とりあえずＬＫのところまでかいてみる。
module Semantics where

data 命題変数 : Set where
  p q r : 命題変数

-- 定義1.1
data 論理式 : Set where
  <_> : 命題変数 → 論理式
  _∧_ : 論理式 → 論理式 → 論理式
  _∨_ : 論理式 → 論理式 → 論理式
  _⊃_ : 論理式 → 論理式 → 論理式
  ¬_  : 論理式 → 論理式

infix 100 ¬_

-- 例1.1
例1-1 : 論理式
例1-1 = < p > ⊃ ( < q > ∨ ¬ < r >)

open import Data.Bool 
  renaming (true to t; false to f;_∧_ to _and_;_∨_ to _or_)
--data Bool : Set where
--  t f : Bool

付値 : Set
付値 = 命題変数 → Bool

-- 論理式の付値をさだめるときは、暗黙的に命題変数の付値がなにかしら決まっている世界を考えている。
-- そのため、{v : 付値} がある。これがないと< x >のときを定義できない。
論理式付値 : {v : 付値} → 論理式 → Bool
論理式付値 {v} < x > = v x
論理式付値 {v} (A ∧ B) with 論理式付値 {v} A | 論理式付値 {v} B
... | t | t = t
... | t | f = f
... | f | t = f
... | f | f = f
論理式付値 {v} (A ∨ B) with 論理式付値 {v} A | 論理式付値 {v} B
... | t | t = t
... | t | f = t
... | f | t = t
... | f | f = f
論理式付値 {v} (A ⊃ B) with 論理式付値 {v} A | 論理式付値 {v} B
... | t | t = t
... | t | f = f
... | f | t = t
... | f | f = t
論理式付値 {v} (¬ A) with 論理式付値 {v} A
... | t = f
... | f = t

open import Relation.Binary.Core renaming (_≡_ to _≈_)
-- ≡はあとで定義したいのでrenameする。


トートロジー : 論理式 → Set
トートロジー A = ∀ v → 論理式付値 {v} A ≈ t

open import Data.Product using (Σ;_×_) renaming (_,_ to _&_)
充足可能 : 論理式 → Set
充足可能 A = Σ 付値 (λ v → 論理式付値 {v} A ≈ t)

_は_である : 論理式 → (論理式 → Set) → Set
a は P である = P a

恒真 = トートロジー

-- 定理1.1
-- 与えられた論理式がトートロジーか否かは決定可能である。
{-
open import Relation.Nullary.Core using (Dec)
open import Data.Sum using (_⊎_)
thm1-1 : (A : 論理式) → Dec ((A は トートロジー である) ⊎ ¬ A は トートロジー である)
thm1-1 < x > = {!!}
thm1-1 (A ∧ A₁) = {!!}
thm1-1 (A ∨ A₁) = {!!}
thm1-1 (A ⊃ A₁) = {!!}
thm1-1 (論理式.¬ A) = {!!}
-}

--_の付値 : 論理式 → Bool
--_の付値 A = 論理式付値 {_} A
-- 例1.3

例1-3 : ((< p > ∧ (< p > ⊃ < q >)) ⊃ < q > ) は トートロジー である
例1-3 v with v p | v q 
例1-3 v | t | t = refl
例1-3 v | t | f = refl
例1-3 v | f | t = refl
例1-3 v | f | f = refl

-- めんどくさいが、論理式の形とその評価した値とを厳密に区別することはだいじ。
-- refl ではなくeqreasoningをつかってみるのもいいかもしれない。

問1-2 : (((< p > ∨ < q >) ⊃ < r >) ∨ (< p > ∧ < q >)) は 充足可能 である
問1-2 = v & refl --refl
  where
   v : 付値
   v p = f
   v q = t
   v r = t
   {-
   v p = f
   v q = f
   v r = t
   -}

-- equivalent
_≡_ : 論理式 → 論理式 → 論理式
A ≡ B = (A ⊃ B) ∧ (B ⊃ A)

infix 1 _≡_

-- 必要十分条件
_⇔_ : Set → Set → Set
A ⇔ B = (A → B) × (B → A)

infix 0 _⇔_
open import Data.Empty
問1-4 : {v : 付値} {A B : 論理式} → 論理式付値 {v} (A ≡ B) ≈ t ⇔ 論理式付値 {v} A ≈ 論理式付値 {v} B
問1-4 {v} {A} {B} with 論理式付値 {v} A | 論理式付値 {v} B
問1-4 | t | t = (λ x → refl) & (λ x → refl)
問1-4 | t | f = (λ ()) & (λ ())
問1-4 | f | t = (λ ()) & (λ ())
問1-4 | f | f = (λ x → refl) & (λ x → refl)
{-
問1-4 {x} {A} {B} v with v(A) | v(B)
問1-4 v | t | t = (λ left-t → refl) , (λ right-t → {!!})
問1-4 v | t | f = {!!} --(λ ()) , (λ ())
問1-4 v | f | t = {!!} --(λ ()) , (λ ())
問1-4 v | f | f = {!!} , {!!}
-}
sample : ∀ A → (A ≡ A ∧ A) は トートロジー である
sample A v with 論理式付値 {v} A
sample A v | t = refl
sample A v | f = refl

module LK where
-- P.23

open Semantics
open import Data.List renaming (_++_ to _,_)

-- 式
infix 1 _⟶_ -- U+27F6 
data _⟶_ : List 論理式 → List 論理式 → Set where
  始式 : (A : 論理式) → [ A ] ⟶ [ A ]
  -- 構造に関する推論規則 P.24
  weakening左 : ∀ Γ Δ A → (Γ ⟶ Δ) → ([ A ] , Γ ⟶ Δ)
  weakening右 : ∀ Γ Δ A → (Γ ⟶ Δ) → (Γ ⟶ Δ , [ A ])
  contraction左 : ∀ Γ Δ A → ([ A ] , [ A ] , Γ ⟶ Δ) → ([ A ] , Γ ⟶ Δ) 
  contraction右 : ∀ Γ Δ A → (Γ ⟶ Δ , [ A ] , [ A ]) → (Γ ⟶ Δ , [ A ]) 
  exchange左 : ∀ Γ Δ Π A B  → (Γ , [ A ] , [ B ] , Π ⟶ Δ) → (Γ , [ B ] , [ A ] , Π ⟶ Δ) 
  exchange右 : ∀ Γ Δ Σ A B  → (Γ ⟶ Δ , [ A ] , [ B ] , Σ) → (Γ ⟶ Δ , [ B ] , [ A ] , Σ) 
  cut : ∀ Γ Δ Π Σ A  → (Π ⟶ Δ , [ A ]) → ([ A ] , Π ⟶ Σ) → (Γ , Π ⟶ Δ , Σ) 
  -- 論理結合子に関する推論規則 P.26
  ∧左1 : ∀ Γ Δ A B → ([ A ] , Γ ⟶ Δ) → ([ A ∧ B ] , Γ ⟶ Δ) 
  ∧左2 : ∀ Γ Δ A B → ([ B ] , Γ ⟶ Δ) → ([ A ∧ B ] , Γ ⟶ Δ) 
  ∧右  : ∀ Γ Δ A B → (Γ ⟶ Δ , [ A ]) → (Γ ⟶ Δ , [ B ]) → (Γ ⟶ Δ , [ A ∧ B ])
  ∨左  : ∀ Γ Δ A B → ([ A ] , Γ ⟶ Δ) → ([ B ] , Γ ⟶ Δ) → ([ A ∨ B ] , Γ ⟶ Δ)
  ∨右1 : ∀ Γ Δ A B → (Γ ⟶ Δ , [ A ]) → (Γ ⟶ Δ , [ A ∨ B ])
  ∨右2 : ∀ Γ Δ A B → (Γ ⟶ Δ , [ B ]) → (Γ ⟶ Δ , [ A ∨ B ])
  ⊃左 : ∀ Γ Δ Π Σ A B → (Γ ⟶ Δ , [ A ]) → ([ B ] , Π ⟶ Σ) → ([ A ⊃ B ] , Γ , Π ⟶ Δ , Σ)
  ⊃右 : ∀ Γ Δ A B → ([ A ] , Γ ⟶ Δ , [ B ]) → (Γ ⟶ Δ , [ A ⊃ B ])
  ¬左 : ∀ Γ Δ A → (Γ ⟶ Δ , [ A ]) → ([ ¬ A ] , Γ ⟶ Δ)
  ¬右 : ∀ Γ Δ A → ([ A ] , Γ ⟶ Δ) → (Γ ⟶ Δ , [ ¬ A ])

例1-12 : ∀ A → [] ⟶ [ A ∨ ¬ A ] -- 問1-13でもある
例1-12 A = contraction右 ([]) ([]) (A ∨ ¬ A)
            (∨右1 [] [ A ∨ ¬ A ] A (¬ A) 
            (exchange右 [] [] [] A (A ∨ ¬ A) 
            (∨右2 [] [ A ] A (¬ A) 
            (¬右 [] [ A ] A 
            (始式 A))))) 
