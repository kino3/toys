module CL where

-- combinatory logic

postulate
  Var : Set

data Const : Set where
  K S : Const

data CL-term : Set where
  atom1 : Var → CL-term
  atom2 : Const → CL-term
  ap : CL-term → CL-term → CL-term

data Formula : Set where
  _▻₁_ : CL-term → CL-term → Formula
  _▻_  : CL-term → CL-term → Formula
  _≡_  : CL-term → CL-term → Formula

-- axiom schemes
[ρ] : CL-term → Formula
[ρ] M = M ▻ M

[K] : (M N : CL-term) → Formula
[K] M N = ap (ap (atom2 K) M) N ▻₁ M

[S] : (M N R : CL-term) → Formula
[S] M N R = ap (ap (ap (atom2 S) M) N) R ▻₁ ap (ap M R) (ap N R)

-- rule of inference
data <_> : Formula → Set where
  μ : {M N R : CL-term} → < N ▻₁ R > → < ap M N ▻₁ ap M R >

hoge : Formula → Set 
hoge = {!!}

open import Data.Nat
data Vec (A : Set) : ℕ → Set where
  []  : Vec A zero 
  _∷_ : {n : ℕ} → A → Vec A n  → Vec A (suc n)

piyo : Vec Const (suc zero)
piyo = S ∷ []

data _t_ : Set where
 ∨-intro1 : {A B : Set} → A → A t B
