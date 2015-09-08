module TPPMark2015 where

-- 情報科学における論理 in Agda

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

open import Data.Bool 
  renaming (true to t; false to f;_∧_ to _and_;_∨_ to _or_)

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

open import Data.Product renaming (_,_ to _&_)
-- 必要十分条件
_⇔_ : Set → Set → Set
A ⇔ B = (A → B) × (B → A)
infix 0 _⇔_

トートロジー : 論理式 → Set
トートロジー A = (v : 付値) → v ⟦ A ⟧ ≈ t

充足可能 : 論理式 → Set
充足可能 A = Σ[ v ∈ 付値 ] v ⟦ A ⟧ ≈ t

論理式_が_である : 論理式 → (論理式 → Set) → Set
論理式 a が P である = P a

恒真 = トートロジー

-- equivalent
_≡_ : 論理式 → 論理式 → 論理式
A ≡ B = (A ⊃ B) ∧ (B ⊃ A)
infix 1 _≡_

_と_は_である : 論理式 → 論理式 → (論理式 → 論理式 → Set) → Set
A と B は P である = P A B

論理的に同値 : 論理式 → 論理式 → Set
論理的に同値 A B = 論理式 A ≡ B が トートロジー である

_∼_ : 論理式 → 論理式 → Set
A ∼ B = A と B は 論理的に同値 である

nf : 論理式 → 論理式
nf (A ⊃ B) = (¬ nf A) ∨ nf B
nf (¬ (A ∧ B)) = nf (¬ A) ∨ nf (¬ B)
nf (¬ (A ∨ B)) = nf (¬ A) ∧ nf (¬ B)
nf x = x

_=!=_ : 論理式 → 論理式 → Bool
< x > =!= < y > = x == y
< x > =!= _ = f
⊤ =!= ⊤ = t
⊤ =!= _ = f
⊥ =!= ⊥ = t
⊥ =!= _ = f
(x1 ∧ x2) =!= (y1 ∧ y2) = x1 =!= y1 and x2 =!= y2
(x1 ∧ x2) =!= _ = f
(x1 ∨ x2) =!= (y1 ∨ y2) = x1 =!= y1 and x2 =!= y2
(x1 ∨ x2) =!= _ = f
(x1 ⊃ x2) =!= (y1 ⊃ y2) = x1 =!= y1 and x2 =!= y2
(x1 ⊃ x2) =!= _ = f
¬ x =!= ¬ y = x =!= y
¬ x =!= _ = f

exam3-1 : (P : 論理式) → P ∼ nf(P)
exam3-1 < x > v = {!!}
exam3-1 ⊤ v = refl
exam3-1 ⊥ v = refl
exam3-1 (A ∧ B) v = {!!}
exam3-1 (A ∨ B) v = {!!}
exam3-1 (A ⊃ B) v = {!!}
exam3-1 (¬ A) v = {!!}

exam3-2 : {P Q : 論理式} → P ∼ Q → T (nf(P) =!= nf(Q))
exam3-2 prf = {!!}
