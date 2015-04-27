module Takeyama201503 where
open import Data.Product
open import Relation.Binary.PropositionalEquality

-- difference between a record type and a one-constructor data type

×-eta1 : {A B : Set}
         (x : A × B) → x ≡ (proj₁ x , proj₂ x)
×-eta1 x = refl

×-elim : {A B : Set}
          (C : A × B → Set) →
          (f : (a : A)(b : B) → C(a , b)) →
          (x : A × B) → C x
×-elim C f x = f (proj₁ x) (proj₂ x)

×-eta2 : {A B : Set} 
        (x : A × B) →
        ×-elim (λ _ → A × B) _,_ x ≡ x
×-eta2 x = refl


data _×′_ (A B : Set)  : Set where
  _,_ : A → B → A ×′ B

×′-elim : {A B : Set}
          (C : A ×′ B → Set) →
          (f : (a : A)(b : B) → C(a , b)) →

          (x : A ×′ B) → C x
×′-elim C f (a , b) = f a b

proj₁′ : {A B : Set} → A ×′ B → A
proj₁′ {A}{B} = ×′-elim (λ _ → A) (λ a _ → a)
proj₂′ : {A B : Set} → A ×′ B → B
proj₂′ {A}{B} = ×′-elim (λ _ → B) (λ _ b → b)

×′-eta1 : {A B : Set}
          (x : A ×′ B) → x ≡ (proj₁′ x , proj₂′ x)
-- ×′-eta1 x = refl
×′-eta1 (a , b) = refl

×′-eta11 : {A B : Set}
           (x : A ×′ B) → x ≡ (proj₁′ x , proj₂′ x)
×′-eta11 = ×′-elim
           (λ y → y ≡ (proj₁′ y , proj₂′ y))
           (λ a b → refl)
          
×′-eta2 : {A B : Set} 
         (x : A ×′ B) →
         ×′-elim (λ _ → A ×′ B) _,_ x ≡ x
-- ×′-eta x = refl
×′-eta2 {A}{B} = ×′-elim
                 (λ y → ×′-elim (λ _ → A ×′ B) _,_ y ≡ y)
                 (λ a b → refl)
