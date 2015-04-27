module TypedLambda where

open import Data.Char

data Type : Set where
  basic : Type
  _⇒_ : Type → Type → Type
  -- TODO: Product,Sum...

infixr 10 _⇒_

data Var : Type → Set where
  v : (A : Type) → Char → Var A

data λTerm : Type → Set where
  var : {A : Type} → Var A → λTerm A
  app : {A B : Type} → λTerm (A ⇒ B) → λTerm A → λTerm B
  lam : {A B : Type} → Var A → λTerm B → λTerm (A ⇒ B)

hoge : (A B : Type) → λTerm (A ⇒ B)
hoge = λ A B → lam (v A 'x') (var (v B 'y')) -- λ x → y

--TODO define rawLambdaTerm
data RawVar : Set where
  v : Char → RawVar

data RawλTerm : Set where
  var : RawVar → RawλTerm
  app : RawλTerm → RawλTerm → RawλTerm
  lam : RawVar → RawλTerm → RawλTerm

open import Data.List
open import Data.Product
TypeAssignment = List (RawVar × Type)

postulate
  typeJudgement : TypeAssignment → RawλTerm → Type

