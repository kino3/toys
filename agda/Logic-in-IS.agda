module Logic-in-IS where

-- 情報科学における論理 in Agda
-- http://www.nippyo.co.jp/book/1292.html

-- とりあえずＬＫのところまでかいてみる。

{-
 第1章 命題論理
-}

-------------------------
-- 1.1 形式化ということ

-------------------------
-- 1.2 命題と論理式

module Semantics where

open import Data.Char
命題変数 = Char

-- 定義1.1
data 論理式 : Set where
  <_> : 命題変数 → 論理式
  ⊤ : 論理式 -- P.12 命題定数
  ⊥ : 論理式 -- P.12 命題定数
  _∧_ : 論理式 → 論理式 → 論理式
  _∨_ : 論理式 → 論理式 → 論理式
  _⊃_ : 論理式 → 論理式 → 論理式
  ¬_  : 論理式 → 論理式

infix 100 ¬_

-- 例1.1
例1-1 : 論理式
例1-1 = < 'p' > ⊃ ( < 'q' > ∨ ¬ < 'r' >)

open import Data.Bool 
  renaming (true to t; false to f;_∧_ to _and_;_∨_ to _or_)


-------------------------
-- 1.3 論理式と真偽

-- P.9
付値 = 命題変数 → Bool

--論理式への拡張
_⟦_⟧ : 付値 → 論理式 → Bool
v ⟦ < x > ⟧   = v(x)
v ⟦ ⊤ ⟧       = t
v ⟦ ⊥ ⟧       = f
v ⟦ A ∧ B ⟧   = v ⟦ A ⟧ and v ⟦ B ⟧  
v ⟦ A ∨ B ⟧   = v ⟦ A ⟧ or  v ⟦ B ⟧ 
v ⟦ A ⊃ B ⟧   = not (v ⟦ A ⟧) or v ⟦ B ⟧
v ⟦ ¬ A ⟧     = not (v ⟦ A ⟧)

open import Relation.Binary.PropositionalEquality as PropEq 
  renaming (_≡_ to _≈_) hiding ([_])
-- ≡はあとで定義したいのでrenameする。

open import Data.Product renaming (_,_ to _&_)
-- 必要十分条件
_⇔_ : Set → Set → Set
A ⇔ B = (A → B) × (B → A)
infix 0 _⇔_

-- SetではなくDecなのではないか？
トートロジー : 論理式 → Set
トートロジー A = (v : 付値) → v ⟦ A ⟧ ≈ t

充足可能 : 論理式 → Set
充足可能 A = Σ[ v ∈ 付値 ] v ⟦ A ⟧ ≈ t

論理式_が_である : 論理式 → (論理式 → Set) → Set
論理式 a が P である = P a

恒真 = トートロジー

例1-3 : 論理式 ((< 'p' > ∧ (< 'p' > ⊃ < 'q' >)) ⊃ < 'q' > ) が トートロジー である
例1-3 v with v('p') | v('q') 
... | t | t = refl
... | t | f = refl
... | f | t = refl
... | f | f = refl

問1-2 : 論理式 (((< 'p' > ∨ < 'q' >) ⊃ < 'r' >) ∨ (< 'p' > ∧ < 'q' >)) が 充足可能 である
問1-2 = v & refl
  where
   v : 付値
   v 'p' = t
   v 'q' = f
   v 'r' = t
   v _   = f
-------------------------
-- 1.4 論理的に同値な論理式

-- equivalent
_≡_ : 論理式 → 論理式 → 論理式
A ≡ B = (A ⊃ B) ∧ (B ⊃ A)
infix 1 _≡_

問1-4 : {v : 付値} {A B : 論理式} → v ⟦ (A ≡ B) ⟧ ≈ t ⇔ v ⟦ A ⟧ ≈ v ⟦ B ⟧
問1-4 {v} {A} {B} with v ⟦ A ⟧ | v ⟦ B ⟧
問1-4 | t | t = (λ x → refl) & (λ x → refl)
問1-4 | t | f = (λ ()) & (λ ())
問1-4 | f | t = (λ ()) & (λ ())
問1-4 | f | f = (λ x → refl) & (λ x → refl)

問1-5 : {A B : 論理式} (v : 付値) → v ⟦ A ≡ B ⟧ ≈ v ⟦(A ∧ B) ∨ (¬ A ∧ ¬ B)⟧
問1-5 {A} {B} v with v ⟦ A ⟧ | v ⟦ B ⟧
問1-5 v | t | t = refl
問1-5 v | t | f = refl
問1-5 v | f | t = refl
問1-5 v | f | f = refl

定理1-3-1a : ∀ A → 論理式 (A ∧ A ≡ A) が トートロジー である
定理1-3-1a A v with v ⟦ A ⟧
定理1-3-1a A v | t = refl
定理1-3-1a A v | f = refl

定理1-3-1b : ∀ A → 論理式 (A ∨ A ≡ A) が トートロジー である
定理1-3-1b A v with v ⟦ A ⟧
定理1-3-1b A v | t = refl
定理1-3-1b A v | f = refl

_と_は_である : 論理式 → 論理式 → (論理式 → 論理式 → Set) → Set
A と B は P である = P A B

論理的に同値 : 論理式 → 論理式 → Set
論理的に同値 A B = 論理式 A ≡ B が トートロジー である

論理的に同値' : 論理式 → 論理式 → Set
論理的に同値' A B = ∀ v → v ⟦ A ⟧ ≈ v ⟦ B ⟧

_∼_ : 論理式 → 論理式 → Set
A ∼ B = A と B は 論理的に同値 である

定理1-4-1 : (A : 論理式) → A ∼ A
定理1-4-1 A v with v ⟦ A ⟧
定理1-4-1 A v | t = refl
定理1-4-1 A v | f = refl

_[_≔_] : 論理式 → 命題変数 → 論理式 → 論理式
< x > [ p ≔ A ] with p == x
... | t = A
... | f = < x >
⊤ [ p ≔ A ]         = ⊤
⊥ [ p ≔ A ]         = ⊥
(C1 ∧ C2) [ p ≔ A ] = C1 [ p ≔ A ] ∧ C2 [ p ≔ A ]
(C1 ∨ C2) [ p ≔ A ] = C1 [ p ≔ A ] ∨ C2 [ p ≔ A ]
(C1 ⊃ C2) [ p ≔ A ] = C1 [ p ≔ A ] ⊃ C2 [ p ≔ A ]
(¬ C) [ p ≔ A ]     = ¬ (C [ p ≔ A ])

lemma : (A B : 論理式) (v : 付値) → v ⟦ A ⟧ ≈ v ⟦ B ⟧ → v ⟦ A ≡ B ⟧ ≈ t
lemma A B v with v ⟦ A ⟧ 
lemma A B v | t with v ⟦ B ⟧
lemma A B v | t | t = λ _ → refl
lemma A B v | t | f = λ ()
lemma A B v | f with v ⟦ B ⟧
lemma A B v | f | t = λ ()
lemma A B v | f | f = λ _ → refl

lemma' : (A B : 論理式) (v : 付値) → v ⟦ A ≡ B ⟧ ≈ t → v ⟦ A ⟧ ≈ v ⟦ B ⟧ 
lemma' A B v prf with v ⟦ A ⟧
lemma' A B v prf | t with v ⟦ B ⟧
lemma' A B v prf | t | t = refl
lemma' A B v prf | t | f = sym prf
lemma' A B v prf | f with v ⟦ B ⟧
lemma' A B v prf | f | t = prf
lemma' A B v prf | f | f = refl

open ≡-Reasoning
-- 例1.7でもある。
定理1-4-4 : (A B C : 論理式) (p : 命題変数) → A ∼ B → C [ p ≔ A ] ∼ C [ p ≔ B ]
定理1-4-4 A B < q >   p A∼B v with p == q -- (1)
... | t = A∼B v  -- Cがある命題変数qに等しいとき、がこれ。
... | f = 定理1-4-1 < q > v -- qがpと異なるとき、がこれ。
定理1-4-4 A B ⊤       p A∼B v = refl
定理1-4-4 A B ⊥       p A∼B v = refl
定理1-4-4 A B (D ∧ E) p A∼B v = lemma1 (定理1-4-4 A B D p A∼B) (定理1-4-4 A B E p A∼B)
  where
    lemma1 : D [ p ≔ A ] ∼ D [ p ≔ B ] 
           → E [ p ≔ A ] ∼ E [ p ≔ B ] 
           → v ⟦ (D ∧ E) [ p ≔ A ] ≡ (D ∧ E) [ p ≔ B ] ⟧ ≈ t
    lemma1 Da∼Db Ea∼Eb = lemma ((D ∧ E) [ p ≔ A ]) ((D ∧ E) [ p ≔ B ]) v {!!}

{-
      begin 
        v ⟦ (D ∧ E) [ p ≔ A ] ≡ (D ∧ E) [ p ≔ B ] ⟧
      ≡⟨ {!!} ⟩ 
        {!(v ⟦ (D ∧ E) [ p ≔ A ] ⟧ ⊃ v ⟦ (D ∧ E) [ p ≔ B ] ⟧) ∧ (v ⟦ (D ∧ E) [ p ≔ B ] ⟧ ⊃ v ⟦ (D ∧ E) [ p ≔ A ] ⟧)!} 
      ≡⟨ {!!} ⟩
        {!!} 
      ≡⟨ {!!} ⟩
        t
      ∎
-}
{-
 Da∼Db
 v ⟦ D [ p ≔ A ] ≡ D [ p ≔ B ] ⟧ ≈ t

   v ⟦ (D ∧ E) [ p ≔ A ] ⟧ ≈ t
 → v ⟦ D [ p ≔ A ] ∧ E [ p ≔ A ] ⟧ ≈ t
 → v ⟦ D [ p ≔ A ] ⟧ and v ⟦ E [ p ≔ A ] ⟧ ≈ t
 → v ⟦ D [ p ≔ B ] ⟧ and v ⟦ E [ p ≔ B ] ⟧ ≈ t by I.H.
 → v ⟦ D [ p ≔ B ] ∧ E [ p ≔ B ] ⟧ ≈ t
 → v ⟦ (D ∧ E) [ p ≔ B ] ⟧ ≈ t
 → 
-}    


-- D [ p ≔ A ] ∼ D [ p ≔ B ] --> (v : 付値) → v ⟦ D [ p ≔ A ] ≡ D [ p ≔ B ] ⟧ ≈ t
-- E [ p ≔ A ] ∼ E [ p ≔ B ]
定理1-4-4 A B (D ∨ E) p A∼B v = {!!}
定理1-4-4 A B (D ⊃ E) p A∼B v = {!!}
定理1-4-4 A B (¬ D)   p A∼B v = {!!}

-------------------------
-- 1.5 標準形

postulate 
  nf : 論理式 → 論理式

_=!=_ : 論理式 → 論理式 → Bool
< x > =!= < y > = x == y
< x > =!= _ = f
⊤ =!= y = {!!}
⊥ =!= y = {!!}
(x ∧ x₁) =!= y = {!!}
(x ∨ x₁) =!= y = {!!}
(x ⊃ x₁) =!= y = {!!}
¬ x =!= y = {!!}

exam3-1 : (P : 論理式) → P ∼ nf(P)
exam3-1 p = {!!}

exam3-2 : {P Q : 論理式} → P ∼ Q → T (nf(P) =!= nf(Q))
exam3-2 prf = {!!}

-------------------------
-- 1.6 形式体系における証明

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

