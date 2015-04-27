module Logic where

-- want to define new deontic logic in Agda.

-- at first, define pred. Logic.

data ⊥ : Set where

⊥-elim : {X : Set} → ⊥ → X
⊥-elim = λ ()

data ⊤ : Set where
  tt : ⊤

data _∧_ (A B : Set) : Set where
  ∧-intro : A → B → A ∧ B

∧-elim1 : {A B : Set} → A ∧ B → A 
∧-elim1 (∧-intro A B) = A
∧-elim2 : {A B : Set} → A ∧ B → B 
∧-elim2 (∧-intro A B) = B

data _∨_ (A B : Set) : Set where
  ∨-intro1 : A → A ∨ B
  ∨-intro2 : B → A ∨ B

∨-elim : {A B C : Set} → A ∨ B →
  (A → C) → (B → C) → C
∨-elim (∨-intro1 a) f g = f a
∨-elim (∨-intro2 b) f g = g b

data ¬_ (A : Set) : Set where
  ¬-intro : (A → ⊥) → ¬ A

¬-elim : {A : Set} → A → ¬ A → ⊥
¬-elim a (¬-intro f) = f a

data _⇒_ (A B : Set) : Set where
  ⇒-intro : (A → B) → A ⇒ B

⇒-elim : {A B : Set} → A ⇒ B → A → B
⇒-elim (⇒-intro f) a = f a

prop1 : {A B : Set} → (¬ A) ∨ B → A ⇒ B
prop1 (∨-intro1 ¬a) = ⇒-intro (λ a → ⊥-elim (¬-elim a ¬a))
prop1 (∨-intro2 b)  = ⇒-intro (λ a → b)

