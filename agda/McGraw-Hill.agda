module McGraw-Hill where

open import Relation.Unary
open import Level
open import Data.Empty
open import Data.Unit

data Pref : Set where
  Nara Kanagawa : Pref
  

hoge : Pred Pref zero
hoge Nara = ⊥
hoge Kanagawa = ⊤

proof : Kanagawa ∈ hoge
proof = tt

proof2 : Nara ∉ hoge
proof2 x = x

proof3 : hoge ⊆ hoge
proof3 a = a

proof4 : {a : Set} {l : Level} (A : Pred a l) → A ⊆ A
proof4 B = λ x → x

module Chapter2 (s : Set) (l : Level) (A B C : Pred s l) where
  open import Relation.Binary.PropositionalEquality --using (_≡_)
  open import Relation.Binary
  open import Data.Product

  Example2-7a1 : A ⊆ A
  Example2-7a1 = λ x∈A → x∈A

  _≈_ : {s : Set} {l : Level} → Pred s l → Pred s l → Set _
  A ≈ B = ∀ {x} → (x ∈ A → x ∈ B) × (x ∈ B → x ∈ A) --A ⊆ B × B ⊆ A

  Example2-7a3 : A ⊆ B → B ⊆ A → A ≈ B
  Example2-7a3 p1 p2 = p1 , p2

  Example2-7a3' : Antisymmetric {A = Pred s l} _⊆_ _≡_
  Example2-7a3' = {!!}

