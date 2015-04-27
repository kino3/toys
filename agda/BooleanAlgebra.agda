module BooleanAlgebra where

open import Level
data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  refl : x ≡ x
infix 4 _≡_

record BoolAlg : Set1 where
  field
    A : Set  
    _∪_ : A → A → A
    _∩_ : A → A → A
    _` : A → A
    c0 : A
    c1 : A
    
    -- axiom
    ax1-1 : ∀ a → a ∩ a ≡ a
    ax1-2 : ∀ a → a ∪ a ≡ a
    ax2-1 : ∀ a b c → a ∩ (b ∩ c) ≡ (a ∩ b) ∩ c
    ax2-2 : ∀ a b c → a ∪ (b ∪ c) ≡ (a ∩ b) ∩ c
    ax3-1 : ∀ a b → a ∩ b ≡ b ∩ a
    ax3-2 : ∀ a b → a ∪ b ≡ b ∪ a
    ax4-1 : ∀ a b → a ∩ (a ∪ b) ≡ a
    ax4-2 : ∀ a b → a ∪ (a ∩ b) ≡ a
    ax5-1 : ∀ a b c → a ∩ (b ∪ c) ≡ (a ∩ b) ∪ (a ∩ c)
    ax5-2 : ∀ a b c → a ∪ (b ∩ c) ≡ (a ∪ b) ∩ (a ∪ c)
    ax6-1 : ∀ a → a ∪ (a `) ≡ c0
    ax6-2 : ∀ a → a ∩ (a `) ≡ c1
    ax7-1 : ∀ a → a ∪ c0 ≡ a
    ax7-2 : ∀ a → a ∪ c1 ≡ c1

data Bool : Set where
  t f : Bool

_∧_ : Bool → Bool → Bool
t ∧ t = t
t ∧ f = f
f ∧ t = f
f ∧ f = f

_∨_ : Bool → Bool → Bool
t ∨ t = t
t ∨ f = t
f ∨ t = t
f ∨ f = f

¬_ : Bool → Bool
¬ t = f
¬ f = t

    
two : BoolAlg
two = record {
        A = Bool;
        _∪_ = _∨_;
        _∩_ = _∧_;
        _` = ¬_;
        c0 = f;
        c1 = t;
        ax1-1 = λ a → proof1 a;
        ax1-2 = λ a → {!!};
        ax2-1 = λ a b c → {!!};
        ax2-2 = λ a b c → {!!};
        ax3-1 = λ a b → {!!};
        ax3-2 = λ a b → {!!};
        ax4-1 = λ a b → {!!};
        ax4-2 = λ a b → {!!};
        ax5-1 = λ a b c → {!!};
        ax5-2 = λ a b c → {!!};
        ax6-1 = λ a → {!!};
        ax6-2 = λ a → {!!};
        ax7-1 = λ a → {!!};
        ax7-2 = λ a → {!!}}
  where
    proof1 : ∀ a → a ∧ a ≡ a
    proof1 t = refl
    proof1 f = refl



