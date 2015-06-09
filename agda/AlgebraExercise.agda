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
                 ∙-cong = +-cong } ; 
               identity = id-left , id-right } }
  where
    --open PropEq.≡-Reasoning
    id-left  : ∀ n → zero + n ≡ n
    id-left n = refl
 
    id-right : ∀ n → n + zero ≡ n
    id-right zero    = refl
    id-right (suc n) rewrite id-right n = refl

    N-assoc : Associative _≡_ _+_
    N-assoc zero    b c = refl
    --N-assoc (suc a) b c rewrite N-assoc a b c = refl
    N-assoc (suc a) b c with a + b + c | N-assoc a b c
    ... | ._ | refl = refl

    +-cong : ∀ {a1 a2 b1 b2 : ℕ} → a1 ≡ a2 → b1 ≡ b2 
             → a1 + b1 ≡ a2 + b2
    +-cong {x1} {.x1} {y1} {.y1} refl refl = refl
