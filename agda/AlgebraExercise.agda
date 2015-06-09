module AlgebraExercise where

open import Algebra
open import Data.Nat
open import Level renaming (zero to lzero; suc to lsuc)
open import Algebra.FunctionProperties
import Relation.Binary.PropositionalEquality as PropEq
open PropEq using (isEquivalence;_≡_;refl)
import Data.Product
open Data.Product using (_,_)

x : Monoid lzero lzero
x = record { Carrier = ℕ ; _≈_ = _≡_ ; _∙_ = _+_ ; ε = zero ; 
             isMonoid = record { 
               isSemigroup = record { 
                 isEquivalence = isEquivalence;
                 assoc = N-assoc ; 
                 ∙-cong = {!!} } ; 
               identity = {!!} , {!!} } }
  where
    +-sym : ∀ {a b} → a + b ≡ b + a
    +-sym {a} {b} = {!!}

    lemma : ∀ n → n + zero ≡ n
    lemma zero = refl
    lemma (suc n) with n + zero | lemma n
    ... | .n | refl = refl
    --lemma (suc n) rewrite lemma n = refl

    open PropEq.≡-Reasoning
    N-assoc : Associative _≡_ _+_
    N-assoc zero    b c = refl
    --N-assoc (suc a) b c rewrite N-assoc a b c = refl
    N-assoc (suc a) b c with a + b + c | N-assoc a b c
    ... | ._ | refl = refl
    {-
    N-assoc zero    zero    zero    = refl
    N-assoc zero    zero    (suc c) = refl
    N-assoc zero    (suc b) zero    = refl
    N-assoc zero    (suc b) (suc c) = refl
    N-assoc (suc a) zero    zero    = 
           begin suc a + zero + zero 
               ≡⟨ refl ⟩ suc (a + zero) + zero 
               ≡⟨ lemma (suc (a + zero)) ⟩ suc a + zero 
               ≡⟨ refl ⟩ suc a + (zero + zero)
           ∎
    N-assoc (suc a) zero    (suc c) = {!!}
    N-assoc (suc a) (suc b) zero    = {!!}
    N-assoc (suc a) (suc b) (suc c) = {!!}
    -}

