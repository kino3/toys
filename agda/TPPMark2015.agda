module TPPMark2015 where

open import Data.Char
open import Data.Bool 
  renaming (true to t; false to f;_∧_ to _and_;_∨_ to _or_)
open import Relation.Binary.PropositionalEquality as PropEq 
open import Data.Product

命題変数 = Char

data 論理式 : Set where
  <_> : 命題変数 → 論理式
  _∧_ : 論理式 → 論理式 → 論理式 
  _∨_ : 論理式 → 論理式 → 論理式
  _⊃_ : 論理式 → 論理式 → 論理式
  ¬_  : 論理式 → 論理式
infix 100 ¬_
infixl 70 _∧_
infixl 50 _∨_
infixr 30 _⊃_

付値 = 命題変数 → Bool

--論理式への拡張
_⟦_⟧ : 付値 → 論理式 → Bool
v ⟦ < x > ⟧   = v(x)
v ⟦ A ∧ B ⟧   = v ⟦ A ⟧ and v ⟦ B ⟧  
v ⟦ A ∨ B ⟧   = v ⟦ A ⟧ or  v ⟦ B ⟧ 
v ⟦ A ⊃ B ⟧   = not (v ⟦ A ⟧) or v ⟦ B ⟧
v ⟦ ¬ A ⟧     = not (v ⟦ A ⟧)

_と_は_である : 論理式 → 論理式 → (論理式 → 論理式 → Set) → Set
A と B は P である = P A B

同値 : 論理式 → 論理式 → Set
同値 A B = (v : 付値) → v ⟦ A ⟧ ≡ v ⟦ B ⟧

-- algorithm for normal form
⊃-elim : 論理式 → 論理式
⊃-elim < x >   = < x >
⊃-elim (A ∧ B) = ⊃-elim A ∧ ⊃-elim B
⊃-elim (A ∨ B) = ⊃-elim A ∨ ⊃-elim B
⊃-elim (A ⊃ B) = ¬ ⊃-elim A ∨ ⊃-elim B
⊃-elim (¬ A)   = ¬ ⊃-elim A

deMorgan : 論理式 → 論理式
deMorgan < x >       = < x >
deMorgan (A ∧ B)     = deMorgan A ∧ deMorgan B
deMorgan (A ∨ B)     = deMorgan A ∨ deMorgan B
deMorgan (A ⊃ B)     = deMorgan A ⊃ deMorgan B
deMorgan (¬ < x >)   = ¬ deMorgan < x >
deMorgan (¬ (A ∧ B)) = deMorgan (¬ A) ∨ deMorgan (¬ B) 
deMorgan (¬ (A ∨ B)) = deMorgan (¬ A) ∧ deMorgan (¬ B)
deMorgan (¬ (A ⊃ B)) = ¬ deMorgan (A ⊃ B)
deMorgan (¬ ¬ A)     = ¬ deMorgan (¬ A)

dne : 論理式 → 論理式
dne < x >   = < x >
dne (A ∧ B) = dne A ∧ dne B
dne (A ∨ B) = dne A ∨ dne B
dne (A ⊃ B) = dne A ⊃ dne B
dne (¬ < x >)   = ¬ < x >
dne (¬ (A ∧ B)) = ¬ (dne A ∧ dne B)
dne (¬ (A ∨ B)) = ¬ (dne A ∨ dne B)
dne (¬ (A ⊃ B)) = ¬ (dne A ⊃ dne B)
dne (¬ (¬ A))   = dne A

dist : 論理式 → 論理式
dist < x > = < x >
dist (A ∧ (B ∨ C)) = dist ((A ∧ B) ∨ (A ∧ C))
dist ((A ∨ B) ∧ C) = dist ((A ∧ C) ∨ (B ∧ C))
dist (A ∧ B) = dist A ∧ dist B
dist (A ∨ B) = dist A ∨ dist B
dist (A ⊃ B) = dist A ⊃ dist B
dist (¬ A) = ¬ dist A

nf : 論理式 → 論理式
nf A = dist (dne (deMorgan (⊃-elim A)))

t1 : 論理式
t1 = ¬ (< 'x' > ⊃ (< 'y' > ∧ < 'z' > ∨ < 'z' > ∧ ¬ < 'x' >))

_=!=_ : 論理式 → 論理式 → Bool
< x > =!= < y > = x == y
< x > =!= _ = f
(x1 ∧ x2) =!= (y1 ∧ y2) = x1 =!= y1 and x2 =!= y2
(x1 ∧ x2) =!= _ = f
(x1 ∨ x2) =!= (y1 ∨ y2) = x1 =!= y1 and x2 =!= y2
(x1 ∨ x2) =!= _ = f
(x1 ⊃ x2) =!= (y1 ⊃ y2) = x1 =!= y1 and x2 =!= y2
(x1 ⊃ x2) =!= _ = f
¬ x =!= ¬ y = x =!= y
¬ x =!= _ = f

lemma1 : (P : 論理式) → P と ⊃-elim(P) は 同値 である
lemma1 < x > v = refl
lemma1 (A ∧ B) v rewrite lemma1 A v | lemma1 B v = refl
lemma1 (A ∨ B) v rewrite lemma1 A v | lemma1 B v = refl
lemma1 (A ⊃ B) v rewrite lemma1 A v | lemma1 B v = refl
lemma1 (¬ A) v   rewrite lemma1 A v = refl

lemma2 : (P : 論理式) → P と deMorgan(P) は 同値 である
lemma2 < x > v = refl
lemma2 (A ∧ B) v rewrite lemma2 A v | lemma2 B v = refl
lemma2 (A ∨ B) v rewrite lemma2 A v | lemma2 B v = refl
lemma2 (A ⊃ B) v rewrite lemma2 A v | lemma2 B v = refl
lemma2 (¬ < x >)   v = refl
lemma2 (¬ (A ∧ B)) v = ?
lemma2 (¬ (A ∨ B)) v = ?
lemma2 (¬ (A ⊃ B)) v rewrite lemma2 A v | lemma2 B v = refl
lemma2 (¬ (¬ A))   v rewrite lemma2 (¬ A) v = refl

lemma3 : (P : 論理式) → P と dne(P) は 同値 である
lemma3 < x > v   = refl
lemma3 (A ∧ B) v rewrite lemma3 A v | lemma3 B v = refl
lemma3 (A ∨ B) v rewrite lemma3 A v | lemma3 B v = refl
lemma3 (A ⊃ B) v rewrite lemma3 A v | lemma3 B v = refl
lemma3 (¬ < x >) v   = refl
lemma3 (¬ (A ∧ B)) v rewrite lemma3 A v | lemma3 B v = refl
lemma3 (¬ (A ∨ B)) v rewrite lemma3 A v | lemma3 B v = refl
lemma3 (¬ (A ⊃ B)) v rewrite lemma3 A v | lemma3 B v = refl
lemma3 (¬ (¬ A)) v   rewrite lemma3 A v with v ⟦ dne A ⟧
... | t = refl
... | f = refl

lemma4 : (P : 論理式) → P と dist(P) は 同値 である
lemma4 < x >   v = {!!}
lemma4 (A ∧ (B ∨ C)) v rewrite lemma4 A v | lemma4 B v | lemma4 C v = {!!}
lemma4 ((A ∨ B) ∧ C) v = {!!}
lemma4 (A ∧ B) v = {!!}
lemma4 (A ∨ B) v rewrite lemma4 A v | lemma4 B v = {!!}
lemma4 (A ⊃ B) v rewrite lemma4 A v | lemma4 B v = {!!}
lemma4 (¬ A)   v rewrite lemma4 A v = {!!}

exam3-1 : (P : 論理式) → P と nf(P) は 同値 である
exam3-1 P v 
  rewrite lemma1 P v | 
          lemma2 (⊃-elim P) v | 
          lemma3 (deMorgan (⊃-elim P)) v | 
          lemma4 (dne (deMorgan (⊃-elim P))) v = refl

exam3-2 : (P Q : 論理式) → P と Q は 同値 である → T (nf(P) =!= nf(Q))
exam3-2 P Q prf = {!!}
