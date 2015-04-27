module LKNat where

{-
An implementation of LK in Agda.
Deep embedding, but use HOAS (Higher Order Abstract Syntax).
Version as of 2008.11.5.
Author: Yoshiki Kinoshita. yoshiki@m.aist.go.jp
-}

data _≡_ {X : Set} : X -> X -> Set where
  /_/ : (x : X) -> x ≡ x
infix 6 _≡_  -- should be weaker than ⊢

data ℕ : Set where
  zero : ℕ
  succ : ℕ -> ℕ

data List (X : Set) : Set where
  [] : List X
  _::_ : X -> List X -> List X

infixr 22 _::_

[_] : {X : Set} -> X -> List X
[ x ] = x :: []

[_,_] : {X : Set} -> X -> X -> List X
[ x , y ] = x :: (y :: [])

[_,_,_] : {X : Set} -> X -> X -> X -> List X
[ x , y , z ] = x :: (y :: (z :: []))

infix 20 [_] [_,_] [_,_,_]

_$_ : {X : Set} -> List X -> List X -> List X
[] $ ys = ys
(x :: xs) $ ys = x :: (xs $ ys)

infixl 18 _$_

data Term : Set where
  # : ℕ -> Term -- variables
  O : Term -- capital O for zero
  _′ : Term -> Term
  _+_ : Term -> Term -> Term
  _×_ : Term -> Term -> Term

infix 60 _′
infixl 50 _×_
infixl 48 _+_

data Pred : Set where
  ⊤ : Pred
  ⊥ : Pred
  _≈_ : Term -> Term -> Pred
  _∧_ : Pred -> Pred -> Pred
  _∨_ : Pred -> Pred -> Pred
  _⇒_ : Pred -> Pred -> Pred
  ¬ : Pred -> Pred
  all : (Term -> Pred) -> Pred
  ∃ : (Term -> Pred) -> Pred

infix 46 _≈_
infix 44 ¬
infixl 42 _∧_
infixl 40 _∨_
infixr 38 _⇒_

data Seq : Set where -- Sequent of LK
  _⊢_ : List Pred -> List Pred -> Seq
infix 10 _⊢_

data 〈_〉 : Seq -> Set where
  〈∧左〉 : {A B : Pred} -> {Γ Δ : List Pred} ->
    〈 A :: B :: Γ  ⊢ Δ 〉 -> 〈 A ∧ B :: Γ ⊢ Δ 〉
  〈∧右〉 : {A B : Pred} -> {Γ Δ : List Pred} ->
    〈 Γ ⊢ A :: Δ 〉 -> 〈 Γ ⊢ B :: Δ 〉 -> 〈 Γ ⊢ A ∧ B :: Δ 〉
  〈∨左〉 : {A B : Pred} -> {Γ Δ : List Pred} ->
    〈 A :: Γ ⊢ Δ 〉 -> 〈 B :: Γ ⊢ Δ 〉 -> 〈 A ∨ B :: Γ ⊢ Δ 〉
  〈∨右〉 : {A B  : Pred} -> {Γ Δ : List Pred} ->
    〈 Γ ⊢ A :: B :: Δ 〉 -> 〈 Γ ⊢ A ∨ B :: Δ 〉
  〈⇒左〉 : {A B : Pred} -> {Γ Δ : List Pred} ->
    〈 B :: Γ ⊢ Δ 〉 -> 〈 Γ ⊢ A :: Δ 〉 -> 〈 A ⇒ B :: Γ ⊢ Δ 〉
  〈⇒右〉 : {A B : Pred} -> {Γ Δ : List Pred} ->
    〈 A :: Γ ⊢ B :: Δ 〉 -> 〈 Γ ⊢ A ⇒ B :: Δ 〉
  〈¬左〉 : {A : Pred} -> {Γ Δ : List Pred} ->
    〈 Γ ⊢ A :: Δ 〉 -> 〈 ¬ A :: Γ ⊢ Δ 〉
  〈¬右〉 : {A : Pred} -> {Γ Δ : List Pred} ->
    〈 A :: Γ ⊢ Δ 〉 -> 〈 Γ ⊢ ¬ A :: Δ 〉
  〈公理〉 : {A : Pred} -> {Γ Δ : List Pred} ->
    〈 A :: Γ ⊢ A :: Δ 〉
-------------------
  〈緩め左〉 : {A : Pred} -> {Γ Δ : List Pred} ->
    〈 Γ ⊢ Δ 〉 -> 〈 A :: Γ ⊢ Δ 〉
  〈緩め右〉 : {A : Pred} -> {Γ Δ : List Pred} ->
    〈 Γ ⊢ Δ 〉 -> 〈 Γ ⊢ A :: Δ 〉
  〈三段論法〉 : {A : Pred} -> {Γ Δ : List Pred} ->
    〈 Γ ⊢ A :: Δ 〉 -> 〈 A :: Γ ⊢ Δ 〉 -> 〈 Γ ⊢ Δ 〉
  〈換左〉 : {Δ : List Pred}-> (Γ1 : List Pred)-> {A B : Pred} -> {Γ2 : List Pred} -> 
    〈 Γ1 $ B :: A :: Γ2 ⊢ Δ 〉 -> 〈 Γ1 $ A :: B :: Γ2 ⊢ Δ 〉
  〈換右〉 : {Γ : List Pred}-> (Δ1 : List Pred)-> {A B : Pred} -> {Δ2 : List Pred} -> 
    〈 Γ ⊢ Δ1 $ B :: A :: Δ2 〉 -> 〈 Γ ⊢ Δ1 $ A :: B :: Δ2 〉
---------------------
  〈all左〉 : {P : Term -> Pred} -> {Γ Δ : List Pred} -> (t : Term) ->
    〈 P t :: all P :: Γ ⊢ Δ 〉 -> 〈 all P :: Γ ⊢ Δ 〉
  〈all右〉 : {P : Term -> Pred} -> {Γ Δ : List Pred} ->
    ((a : Term) -> 〈 Γ ⊢ P a :: Δ 〉) -> 〈 Γ ⊢ all P :: Δ 〉
  〈∃左〉 : {P : Term -> Pred} -> {Γ Δ : List Pred} -> 
    ((a : Term) -> 〈 P a :: Γ ⊢ Δ 〉) -> 〈 ∃ P :: Γ ⊢ Δ 〉
  〈∃右〉 : {P : Term -> Pred} -> {Γ Δ : List Pred} -> (t : Term) ->
    〈 Γ ⊢ P t :: ∃ P :: Δ 〉 -> 〈 Γ ⊢ ∃ P :: Δ 〉
---------------------
  〈反射律〉 : {Γ Δ : List Pred} ->
    〈 Γ ⊢ (all \x -> x ≈ x) :: Δ 〉
  〈対称律〉 : {Γ Δ : List Pred} ->
    〈 Γ ⊢ (all \x -> all \y -> x ≈ y ⇒ y ≈ x) :: Δ 〉
  〈推移律〉 : {Γ Δ : List Pred} ->
    〈 Γ ⊢ (all \x -> all \y -> all \z -> x ≈ y ⇒ y ≈ z ⇒ x ≈ z) :: Δ 〉
  〈Peano3〉 : {Γ Δ : List Pred} ->
    〈 Γ ⊢ (all \x -> all \y -> x ′ ≈ y ′ ⇒ x ≈ y) :: Δ 〉
  〈Peano4〉 : {Γ Δ : List Pred} ->
    〈 Γ ⊢ (all \x -> ¬ (x ′ ≈ O)) :: Δ 〉
  〈Peano5〉 : {Γ Δ : List Pred} -> {A : Term -> Pred} ->
                     〈 Γ ⊢ A O ∧ (all \x -> A x ⇒ A (x ′)) ⇒ (all \x -> A x) :: Δ 〉
  〈+交換〉 : {Γ Δ : List Pred} ->
    〈 Γ ⊢ (all \x -> all \y -> x + y ≈ y + x) :: Δ 〉
  〈+単位元〉 : {Γ Δ : List Pred} ->
    〈 Γ ⊢ (all \x -> O + x ≈ x) :: Δ 〉
  〈+と′〉 : {Γ Δ : List Pred} ->
    〈 Γ ⊢ (all \x -> all \y -> x ′ + y ≈ (x + y)′) :: Δ 〉
  〈×交換〉 : {Γ Δ : List Pred} ->
    〈 Γ ⊢ (all \x -> all \y -> x × y ≈ y × x) :: Δ 〉
  〈×零元〉 : {Γ Δ : List Pred} ->
    〈 Γ ⊢ (all \x -> all \y -> O × x ≈ O) :: Δ 〉
  〈×と′〉 : {Γ Δ : List Pred} ->
    〈 Γ ⊢ (all \x -> all \y -> x ′ × y ≈ x × y + y) :: Δ 〉
infix 8 〈_〉

_≦_ : Term -> Term -> Pred
x ≦ y = ∃ \u -> x + u ≈ y
infix 46 _≦_

{-
≦反射律 : {Γ Δ : List Pred} -> 〈 Γ ⊢ (all \x -> x ≦ x) :: Δ 〉
≦反射律 = {! !}
≦半対称律 : {Γ Δ : List Pred} ->
    〈 Γ ⊢ (all \x -> all \y -> x ≦ y ∧ y ≦ x ⇒ x ≈ y) :: Δ 〉
≦半対称律 = {! !}
≦推移律 : {Γ Δ : List Pred} ->
    〈 Γ ⊢ (all \x -> all \y -> all \z -> x ≦ y ∧ y ≦ z ⇒ x ≦ z) :: Δ 〉
≦推移律 = {! !}
≦全順序 : {Γ Δ : List Pred} ->
    〈 Γ ⊢ (all \x -> all \y -> x ≦ y ∨ y ≦ x) :: Δ 〉
≦全順序 = {! !}
-}

_∧左_ : {A B : Pred} -> {Γ Δ : List Pred} -> 
  {conseq : Seq} -> (conseq ≡ A ∧ B :: Γ ⊢ Δ) ->
  〈 A :: B :: Γ  ⊢ Δ 〉 -> 〈 A ∧ B :: Γ ⊢ Δ 〉
_ ∧左 d =  〈∧左〉 d
_∧右_⋘_⋙ : {A B : Pred} -> {Γ Δ : List Pred} ->
  {conseq : Seq} -> (conseq ≡ Γ ⊢ A ∧ B :: Δ) ->
  〈 Γ ⊢ A :: Δ 〉 -> 〈 Γ ⊢ B :: Δ 〉 -> 〈 Γ ⊢ A ∧ B :: Δ 〉
_ ∧右 d1 ⋘ d2 ⋙ = 〈∧右〉 d1 d2
_∨左_⋘_⋙ : {A B : Pred} -> {Γ Δ : List Pred} ->
  {conseq : Seq} -> (conseq ≡ A ∨ B :: Γ ⊢ Δ) ->
  〈 A :: Γ ⊢ Δ 〉 -> 〈 B :: Γ ⊢ Δ 〉 -> 〈 A ∨ B :: Γ ⊢ Δ 〉
_ ∨左 d1 ⋘ d2 ⋙ = 〈∨左〉 d1 d2
_∨右_ : {A B  : Pred} -> {Γ Δ : List Pred} ->
  {conseq : Seq} -> (conseq ≡ Γ ⊢ A ∨ B :: Δ) ->
  〈 Γ ⊢ A :: B :: Δ 〉 -> 〈 Γ ⊢ A ∨ B :: Δ 〉
_ ∨右 d = 〈∨右〉 d
_⇒左_⋘_⋙ : {A B : Pred} -> {Γ Δ : List Pred} ->
  {conseq : Seq} -> (conseq ≡ A ⇒ B :: Γ ⊢ Δ) ->
  〈 B :: Γ ⊢ Δ 〉 -> 〈 Γ ⊢ A :: Δ 〉 -> 〈 A ⇒ B :: Γ ⊢ Δ 〉
_ ⇒左 d1 ⋘ d2 ⋙ = 〈⇒左〉 d1 d2
_⇒右_ : {A B : Pred} -> {Γ Δ : List Pred} ->
  {conseq : Seq} -> (conseq ≡ Γ ⊢ A ⇒ B :: Δ) ->
  〈 A :: Γ ⊢ B :: Δ 〉 -> 〈 Γ ⊢ A ⇒ B :: Δ 〉
_ ⇒右 d = 〈⇒右〉 d
_¬左_ : {A : Pred} -> {Γ Δ : List Pred} ->
  {conseq : Seq} -> (conseq ≡ ¬ A :: Γ ⊢ Δ) ->
  〈 Γ ⊢ A :: Δ 〉 -> 〈 ¬ A :: Γ ⊢ Δ 〉
_ ¬左 d = 〈¬左〉 d
_¬右_ : {A : Pred} -> {Γ Δ : List Pred} ->
  {conseq : Seq} -> (conseq ≡ Γ ⊢ ¬ A :: Δ) ->
  〈 A :: Γ ⊢ Δ 〉 -> 〈 Γ ⊢ ¬ A :: Δ 〉
_ ¬右 d = 〈¬右〉 d
_公理 : {A : Pred} -> {Γ Δ : List Pred} ->
  {conseq : Seq} -> (conseq ≡ A :: Γ ⊢ A :: Δ) ->
  〈 A :: Γ ⊢ A :: Δ 〉
_ 公理 = 〈公理〉
-------------------
_緩め左_ : {A : Pred} -> {Γ Δ : List Pred} ->
  {conseq : Seq} -> (conseq ≡ A :: Γ ⊢ Δ) ->
  〈 Γ ⊢ Δ 〉 -> 〈 A :: Γ ⊢ Δ 〉
_ 緩め左 d = 〈緩め左〉 d
_緩め右_ : {A : Pred} -> {Γ Δ : List Pred} ->
  {conseq : Seq} -> (conseq ≡ Γ ⊢ A :: Δ) ->
  〈 Γ ⊢ Δ 〉 -> 〈 Γ ⊢ A :: Δ 〉
_ 緩め右 d = 〈緩め右〉 d
_三段論法_⋘_⋙ : {A : Pred} -> {Γ Δ : List Pred} ->
  {conseq : Seq} -> (conseq ≡ Γ ⊢ Δ) ->
  〈 Γ ⊢ A :: Δ 〉 -> 〈 A :: Γ ⊢ Δ 〉 -> 〈 Γ ⊢ Δ 〉
_ 三段論法 d1 ⋘ d2 ⋙ = 〈三段論法〉 d1 d2
≪_≫_換左_ :
  {Δ : List Pred}-> (Γ1 : List Pred)-> {A B : Pred} -> {Γ2 : List Pred} -> 
  {conseq : Seq} -> (conseq ≡ Γ1 $ A :: B :: Γ2 ⊢ Δ) ->
  〈 Γ1 $ B :: A :: Γ2 ⊢ Δ 〉 -> 〈 Γ1 $ A :: B :: Γ2 ⊢ Δ 〉
≪ Γ1 ≫ _ 換左 d = 〈換左〉 Γ1 d
≪_≫_換右_ :
  {Γ : List Pred}-> (Δ1 : List Pred) -> {A B : Pred} -> {Δ2 : List Pred} -> 
  {conseq : Seq} -> (conseq ≡ Γ ⊢ Δ1 $ A :: B :: Δ2) ->
  〈 Γ ⊢ Δ1 $ B :: A :: Δ2 〉 -> 〈 Γ ⊢ Δ1 $ A :: B :: Δ2 〉
≪ Δ1 ≫ _ 換右 d = 〈換右〉 Δ1 d
_all左〈_〉_ : {P : Term -> Pred} -> {Γ Δ : List Pred} ->
  {conseq : Seq} -> (conseq ≡ all P :: Γ ⊢ Δ) -> (t : Term) ->
 〈 P t :: all P :: Γ ⊢ Δ 〉 -> 〈 all P :: Γ ⊢ Δ 〉
_ all左〈 t 〉 d = 〈all左〉 t d
_all右_ : {P : Term -> Pred} -> {Γ Δ : List Pred} ->
  {conseq : Seq} -> (conseq ≡ Γ ⊢ all P :: Δ) ->
  ((t : Term) -> 〈 Γ ⊢ P t :: Δ 〉) -> 〈 Γ ⊢ all P :: Δ 〉
_ all右 d = 〈all右〉 d
_∃左_ : {P : Term -> Pred} -> {Γ Δ : List Pred} -> 
  {conseq : Seq} -> (conseq ≡ (∃ \x -> P x) :: Γ ⊢ Δ) ->
  ((t : Term) -> 〈 P t :: Γ ⊢ Δ 〉) -> 〈 ∃ P :: Γ ⊢ Δ 〉
_ ∃左 d = 〈∃左〉 d
_∃右〈_〉_ : {P : Term -> Pred} -> {Γ Δ : List Pred} ->
  {conseq : Seq} -> (conseq ≡ Γ ⊢ ∃ P :: Δ) -> (t : Term) ->
  〈 Γ ⊢ P t :: ∃ P :: Δ 〉 -> 〈 Γ ⊢ ∃ P :: Δ 〉
_ ∃右〈 t 〉 d = 〈∃右〉 t d
---------------------
{-
  〈反射律〉 : {Γ Δ : List Pred} ->
    〈 Γ ⊢ (all \x -> x ≈ x) :: Δ 〉
  〈対称律〉 : {Γ Δ : List Pred} ->
    〈 Γ ⊢ (all \x -> all \y -> x ≈ y ⇒ y ≈ x) :: Δ 〉
  〈推移律〉 : {Γ Δ : List Pred} ->
    〈 Γ ⊢ (all \x -> all \y -> all \z -> x ≈ y ⇒ y ≈ z ⇒ x ≈ z) :: Δ 〉
-}
Peano3 : {Γ Δ : List Pred} ->
  〈 Γ ⊢ (all \x -> all \y -> x ′ ≈ y ′ ⇒ x ≈ y) :: Δ 〉
Peano3 = 〈Peano3〉
Peano4 : {Γ Δ : List Pred} ->
  〈 Γ ⊢ (all \x -> ¬ (x ′ ≈ O)) :: Δ 〉
Peano4 = 〈Peano4〉
Peano5 : {Γ Δ : List Pred} -> {A : Term -> Pred} ->
                  〈 Γ ⊢ (A O ∧ (all \x -> A x ⇒ A (x ′)) ⇒ all \x -> A x) :: Δ 〉
Peano5 = 〈Peano5〉
+交換 : {Γ Δ : List Pred} ->
  〈 Γ ⊢ (all \x -> all \y -> x + y ≈ y + x) :: Δ 〉
+交換 = 〈+交換〉
+単位元 : {Γ Δ : List Pred} ->
  〈 Γ ⊢ (all \x -> O + x ≈ x) :: Δ 〉
+単位元 = 〈+単位元〉
+と′ : {Γ Δ : List Pred} ->
  〈 Γ ⊢ (all \x -> all \y -> x ′ + y ≈ (x + y)′) :: Δ 〉
+と′ = 〈+と′〉
×交換 : {Γ Δ : List Pred} ->
  〈 Γ ⊢ (all \x -> all \y -> x × y ≈ y × x) :: Δ 〉
×交換 = 〈×交換〉
×零元 : {Γ Δ : List Pred} ->
  〈 Γ ⊢ (all \x -> all \y -> O × x ≈ O) :: Δ 〉
×零元 = 〈×零元〉
×と′ : {Γ Δ : List Pred} ->
  〈 Γ ⊢ (all \x -> all \y -> x ′ × y ≈ x × y + y) :: Δ 〉
×と′ = 〈×と′〉

infixr 6 _∧左_ _∧右_⋘_⋙ _∨左_⋘_⋙ _∨右_ _⇒左_⋘_⋙ _⇒右_
  _¬左_ _¬右_ _緩め左_ _緩め右_ _三段論法_⋘_⋙
  ≪_≫_換左_ ≪_≫_換右_ _all左〈_〉_ _all右_ _∃左_ _∃右〈_〉_
