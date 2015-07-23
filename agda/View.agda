module View where
-- Dependently typed programming in Agda
-- 3 Programming Techniques

-- 3.1 Views

-- Natural number parity

open import Data.Nat renaming (ℕ to Nat) 

data Parity : Nat → Set where
  even : (k : Nat) → Parity (k * 2)
  odd  : (k : Nat) → Parity (1 + k * 2)

parity : (n : Nat) → Parity n
parity zero    = even zero
parity (suc n) with parity n
parity (suc .(k * 2))       | even k = odd k
parity (suc .(suc (k * 2))) | odd  k = even (suc k)

half : Nat → Nat
half n with parity n
half .(k * 2)       | even k = k
half .(suc (k * 2)) | odd  k = k

-- Finding an element in a list

open import Function using (_∘_)
open import Data.List
open import Data.Bool renaming (T to isTrue)

infixr 30 _:all:_
data All {A : Set}(P : A → Set) : List A → Set where
  all[]   : All P []
  _:all:_ : ∀ {x xs} → P x → All P xs → All P (x ∷ xs)


satisfies : {A : Set} → (A → Bool) → A → Set
satisfies p x = isTrue (p x)

data Find {A : Set}(p : A → Bool) : List A → Set where
  found     : (xs : List A)(y : A) → satisfies p y → (ys : List A) 
              → Find p (xs ++ y ∷ ys)
  not-found : ∀ {xs} → All (satisfies (not ∘ p)) xs 
              → Find p xs

sample : List Nat
sample = 3 ∷ 5 ∷ 2 ∷ 1 ∷ 4 ∷ []

prop : Nat → Bool
prop 2 = true
prop 4 = true
prop _ = false

open import Data.Unit 
findsample : Find prop sample
findsample = found (3 ∷ 5 ∷ []) 2 tt (1 ∷ 4 ∷ [])

{-
find₁ : {A : Set}(p : A → Bool)(xs : List A) → Find p xs
find₁ p []       = not-found all[]
find₁ p (x ∷ xs) with p x
find₁ p (x ∷ xs) | true  = found [] x {!!} xs
find₁ p (x ∷ xs) | false = {!!}
-}

data _==_ {A : Set}(x : A) : A → Set where
  refl : x == x

data Inspect {A : Set}(x : A) : Set where
  it : (y : A) → x == y → Inspect x

inspect : {A : Set}(x : A) → Inspect x
inspect x = it x refl

trueIsTrue : {x : Bool} → x == true → isTrue x
trueIsTrue refl = _

isFalse : Bool → Set
isFalse x = isTrue (not x)

falseIsFalse : {x : Bool} → x == false → isFalse x
falseIsFalse refl = _

find : {A : Set}(p : A → Bool)(xs : List A) → Find p xs
find p []       = not-found all[]
find p (x ∷ xs) with inspect (p x)
... | it true  prf = found {!!} {!!} {!!} {!!}
... | it false prf = {!!}
