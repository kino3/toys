module Logic-in-IS3 where
-- 付値かきなおしてみる 2015.07.23.

-- 情報科学における論理 in Agda
-- http://www.nippyo.co.jp/book/1292.html

-- とりあえずＬＫのところまでかいてみる。
module Semantics where

open import Data.Bool 
  renaming (true to t; false to f;_∧_ to _and_;_∨_ to _or_)

open import Data.Char
命題変数 = Char
付値' = 命題変数 → Bool

-- 定義1.1
data 論理式 (x : 付値') : Set where
  <_> : 命題変数 → 論理式 x
  ⊤ ⊥ : 論理式 x
  _∧_ : 論理式 x → 論理式 x → 論理式 x
  _∨_ : 論理式 x → 論理式 x → 論理式 x
  _⊃_ : 論理式 x → 論理式 x → 論理式 x
  ¬_  : 論理式 x → 論理式 x

infix 100 ¬_

-- 例1.1
例1-1 : {x : 付値'}(p q r : 論理式 x) → 論理式 x
例1-1 p q r = p ⊃ ( q ∨ ¬ r )


-- P.9


open import Data.Product renaming (_,_ to _&_)
open import Data.List
--拡張
piyo : {v : 付値'} → 論理式 v → Bool
piyo {v} < x > = v x
piyo (A ∧ B) with piyo A | piyo B
... | t | t = t
... | t | f = f
... | f | t = f
... | f | f = f
piyo (A ∨ B) with piyo A | piyo B
... | t | t = t
... | t | f = t
... | f | t = t
... | f | f = f
piyo (A ⊃ B) with piyo A | piyo B
... | t | t = t
... | t | f = f
... | f | t = t
... | f | f = t
piyo (¬ A) with piyo A
... | t = f
... | f = t
piyo ⊤ = t
piyo ⊥ = f

--open import Relation.Binary.Core renaming (_≡_ to _≈_)
-- ≡はあとで定義したいのでrenameする。
付値 : Set
付値 = Σ 付値' (λ x → 論理式 x → Bool)

a : 付値
a = (λ x → t) & piyo

-- 必要十分条件
{-
_⇔_ : Set → Set → Set
A ⇔ B = (A → B) かつ (B → A)
infix 1 _⇔_
-}
--open import Data.Sum renaming (_⊎_ to _または_)

data _≈_ : Bool → Bool → Set where
  refl : ∀ b → b ≈ b
infix 1 _≈_

{-
postulate
  p1 : (A B : 論理式)(v : 付値) → v(A ∧ B) ≈ v(A) and v(B)
  p2 : (A B : 論理式)(v : 付値) → v(A ∨ B) ≈ v(A) or v(B)
  p3 : (A B : 論理式)(v : 付値) → v(A ⊃ B) ≈ not(v(A)) or v(B)
  p4 : (A : 論理式)  (v : 付値) → v(¬ A)   ≈ not(v(A))
  p5 : (v : 付値) → v(⊤) ≈ t
  p6 : (v : 付値) → v(⊥) ≈ f
-}


トートロジー : {v' : 付値'} → 論理式 {!!} → Set
トートロジー A = (x : 付値) → (Σ.proj₂ x) {!A!} ≈ t
{-
充足可能 : 論理式 → Set
充足可能 A = Σ[ v ∈ 付値 ] v(A) ≈ t --Σ 付値 (λ v → v(A) ≈ t)

論理式_が_である : 論理式 → (論理式 → Set) → Set
論理式 a が P である = P a

恒真 = トートロジー
-}
{-
-- 定理1.1
-- 与えられた論理式がトートロジーか否かは決定可能である。
-}

{-
open import Relation.Nullary using (yes;no)
open import Relation.Binary.PropositionalEquality hiding ([_])
例1 : ∀ p → 論理式 (p ⊃ p) が トートロジー である
例1 p v = {!!}





例1-3 : ∀ p q → 論理式 ((p ∧ (p ⊃ q)) ⊃ q) が トートロジー である
例1-3 p q v with v(p) | v(q)
例1-3 p q v | t | t = {!!}
例1-3 p q v | t | f = {!!}
例1-3 p q v | f | t = {!!}
例1-3 p q v | f | f = {!!} 

{-

例1-3 v | t | t = refl
例1-3 v | t | f = refl
例1-3 v | f | t = refl
例1-3 v | f | f = refl
-}
{-
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


infix 0 _⇔_
open import Data.Empty
問1-4 : {v : 付値} {A B : 論理式} → 付値 {v} (A ≡ B) ≈ t ⇔ 付値 {v} A ≈ 付値 {v} B
問1-4 {v} {A} {B} with 付値 {v} A | 付値 {v} B
問1-4 | t | t = (λ x → refl) & (λ x → refl)
問1-4 | t | f = (λ ()) & (λ ())
問1-4 | f | t = (λ ()) & (λ ())
問1-4 | f | f = (λ x → refl) & (λ x → refl)

{-
問1-5 : {A B : 論理式} (v : 論理式 → Bool) → v (A ≡ B) ≈ v ((A ∧ B) ∨ (¬ A ∧ ¬ B))
問1-5 {A} {B} v with v A | v B
問1-5 v | t | t = refl
問1-5 v | t | f = refl
問1-5 v | f | t = refl
問1-5 v | f | f = refl
-}

定理1-3-1a : ∀ A → (A ∧ A ≡ A) は トートロジー である
定理1-3-1a A v with 付値 {v} A
定理1-3-1a A v | t = refl
定理1-3-1a A v | f = refl

toi1-1 : ∀ A B → (A ⊃ B) は 充足可能 である 
               → A は 充足可能 である 
               → B は 充足可能 である
toi1-1 A B (v & eq) (w & eq2) = {!!} & {!!}
-}


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
例1-12 A = contraction右 [] [] (A ∨ ¬ A)
          (∨右1 [] [ A ∨ ¬ A ] A (¬ A) 
          (exchange右 [] [] [] A (A ∨ ¬ A) 
          (∨右2 [] [ A ] A (¬ A) 
          (¬右 [] [ A ] A 
          (始式 A))))) 

-}
