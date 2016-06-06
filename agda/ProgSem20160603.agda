module ProgSem20160603 where
open import Data.Product
open import Data.Sum
open import Data.Empty
open import Relation.Nullary

{-
*  目標: Agda と 論理の関係について理解する。
   - "Proposition as Types, Proofs as Programs"
   - "Curry-Howard Isomorphism"
* 基本
  - 命題は、証明の集合である。
| 命題       | 証明                           | Agda での 型 |
| A ならば B | Aの証明から、Bの証明を作る関数 | A → B        |
| A かつ B   | ペア (Aの証明 , Bの証明)       | A × B        |
| 偽         | (なし)                         |  ⊥  |
| not A      | A ならば 偽                    |  ¬ A     (A → ⊥) |
-}

foo : {A B : Set} → A → ( B → A × B )
foo a b = a , b

test : {A B C : Set} →
       (A → B → C) → (A → B) → A → C
test p q a = p a (q a)

test2 : {A B C : Set} →
        ((A × B) → C) → (A → B → C)
test2 p a b = p (a , b)

test3 : {A B C : Set} → 
        (A → B → C) → (A × B → C)
test3 p ab = p (proj₁ ab) (proj₂ ab)


test3′ : {A B C : Set} → 
        (A → B → C) → (A × B → C)
test3′ p (a , b) = p a b



¬-elim : {A : Set} → A → ¬ A → ⊥
¬-elim a na = na a
¬-intro : {A : Set} → (A → ⊥) → ¬ A
¬-intro na = na

×-intro : {A B : Set} → A → B → A × B
×-intro a b = a , b
×-elim1 : {A B : Set} → A × B → A
×-elim1 (a , b) = a
×-elim2 : {A B : Set} → A × B → B
×-elim2 (a , b) = b

-- ¬ A := A → ⊥

test4 : {A B C : Set} →
        (A → B) → (¬ B → ¬ A)
--test4 : {A B C : Set} →
--        (A → B) → (B → ⊥) → A → ⊥
test4 f nb a = nb (f a)
{-
test4 = λ f nb a → nb (f a)
-}

-- ⊎  --- \uplus
-- inj₁ --- inj\_1


⊎-intro1 : {A B : Set} → A → A ⊎ B
⊎-intro1 = λ a → inj₁ a
⊎-intro2 : {A B : Set} → B → A ⊎ B
⊎-intro2 = λ b → inj₂ b
⊎-elim : {A B C : Set} → A ⊎ B → (A → C) → (B → C) → C
⊎-elim (inj₁ a) f _ = f a
⊎-elim (inj₂ b) _ g = g b

test6 : {A B : Set} → A × B → A ⊎ B
test6 (a , _) = inj₁ a
test7 : {A B : Set} → A × B → A ⊎ B
test7 (_ , b) = inj₂ b

test8 : {A B C : Set} → A × (B ⊎ C) → A × B ⊎ A × C
test8 (a , inj₁ b) = inj₁ (a , b)
test8 (a , inj₂ c) = inj₂ (a , c)

test9 : {A B : Set} → ¬ A ⊎ ¬ B → ¬ (A × B)
test9 p = λ x → ⊎-elim p (λ x₁ → ¬-elim (×-elim1 x) x₁) (λ x₁ → ¬-elim (×-elim2 x) x₁)

test5 : {A B C : Set} →
        (¬(¬ A) → A) → 
        (¬ B → ¬ A) → (A → B)
{-
test5 : {A B C : Set} →
        (¬(¬ A) → A) → 
        (¬ B → ¬ A) →
        A →
        B
-}
test5 {A} {B} {C} dne c a = ⊎-elim (→-to-⊎ c)
                             {!!}
                             (λ ¬a → ⊥-elim (¬-elim a ¬a))
  where
    →-to-⊎ : {X Y : Set} → (X → Y) → ¬ X ⊎ Y
    →-to-⊎ {X} {Y} f = {!!}
