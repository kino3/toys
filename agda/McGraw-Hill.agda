module McGraw-Hill where

open import Relation.Unary

_≡_ : ∀ {A B l} → Pred A l → Pred B l → Set l
a ≡ b = {!!}

hoge : ∀ a l → (A : Pred _ l) → A a → (A ∪ A) a
hoge = λ a l A x → {!!}

{-
Th10 : ∀ A B → ∁ (A ∪ B) → ∁ A ∩ ∁ B 
Th10 = ?
-}
