module ProgSem20160527 where
open import Data.Product
open import Relation.Nullary

test : {A B C : Set} → (A → B → C) → 
       ((A → B) → (A → C))
test p q a = p a (q a)

test2 : {A B C : Set} →
        ((A × B) → C) → (A → B → C)
test2 p a b = p (a , b)

test3 : {A B C : Set} →
        (A → B → C) → (A × B → C)
test3 p ab = p (proj₁ ab) (proj₂ ab)

{-
test4 : {A B C : Set} →
        (A → B) → (¬ B → ¬ A)

test5 : {A B C : Set} →
        (¬(¬ A) → A) →
        (¬ B → ¬ A) → (A → B)
-}
