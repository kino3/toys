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

{-
parity2 : (n : Nat) → Parity n
parity2 zero    = even zero
parity2 (suc n) with parity2 n
parity2 (suc .(k * 2))       | even k = {!!}
parity2 (suc .(suc (k * 2))) | odd k  = {!!}
-}

half : Nat → Nat
half n with parity n
half .(k * 2)       | even k = k
half .(suc (k * 2)) | odd  k = k

open import Data.Bool renaming (T to isTrue)
isEven : Nat → Bool
isEven n with parity n
isEven .(k * 2)       | even k = true
isEven .(suc (k * 2)) |  odd k = false


-- Finding an element in a list

open import Function using (_∘_)
open import Data.List


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
open import Data.Empty

p : Nat → Set
p 2 = ⊤ --isTrue (prop n)
p _ = ⊥
{-
ponyo : All p sample
ponyo = {!!} :all: {!!} :all: tt :all: {!!} :all: {!!} :all: all[]
-}
findsample : Find prop sample
findsample = found (3 ∷ 5 ∷ []) 2 tt (1 ∷ 4 ∷ [])

sample2 : List Nat
sample2 = 3 ∷ 5 ∷ 1 ∷ []

findsample2 : Find prop sample2
findsample2 = not-found (tt :all: (tt :all: (tt :all: all[])))

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
trueIsTrue refl = tt

harada : Inspect 3
harada = it 3 refl

isFalse : Bool → Set
isFalse x = isTrue (not x)

falseIsFalse : {x : Bool} → x == false → isFalse x
falseIsFalse refl = tt

find : {A : Set}(p : A → Bool)(xs : List A) → Find p xs
find p []       = not-found all[]
find p (x ∷ xs) with inspect (p x)
... | it true  prf = found [] x (trueIsTrue prf) xs
... | it false prf with find p xs
find p (x ∷ .(xs ++ y ∷ ys)) | it false prf | found xs y py ys 
  = found (x ∷ xs) y py ys
find p (x ∷ xs)              | it false prf | not-found npxs     
  = not-found (falseIsFalse prf :all: npxs)



-- Indexing into a list
data _∈_ {A : Set}(x : A) : List A → Set where
  hd : ∀ {xs}   → x ∈ x ∷ xs
  tl : ∀ {y xs} → x ∈ xs     → x ∈ y ∷ xs
infix 4 _∈_

index : ∀ {A}{x : A}{xs} → x ∈ xs → Nat
index hd     = zero
index (tl p) = suc (index p) 

data Lookup {A : Set}(xs : List A) : Nat → Set where
  inside : (x : A)(p : x ∈ xs) → Lookup xs (index p)
  outside : (m : Nat) → Lookup xs (length xs + m)

lkpsample : Lookup sample 0
lkpsample = inside 3 hd

lkpsample2 : Lookup sample 1
lkpsample2 = inside 5 (tl hd)

lkpsample3 : Lookup sample 2
lkpsample3 = inside 2 (tl (tl hd))

lkpsample4 : Lookup sample 5
lkpsample4 = outside 0

lkpsample5 : Lookup sample 8
lkpsample5 = outside 3

_!_ : {A : Set}(xs : List A)(n : Nat) → Lookup xs n
[] ! n = outside n
(x ∷ xs) ! zero  = inside x hd
(x ∷ xs) ! suc n with xs ! n
(x ∷ xs) ! suc .(index p)       | inside y p = inside y (tl p)
(x ∷ xs) ! suc .(length xs + m) | outside m  = outside m

-- A type checker for λ-calculus
infixr 30 _⇒_
data Type : Set where
  ı   : Type
  _⇒_ : Type → Type → Type

data Equal? : Type → Type → Set where
  yes : ∀ {τ}   → Equal? τ τ
  no  : ∀ {σ τ} → Equal? σ τ

_=?=_ : (σ τ : Type) → Equal? σ τ
ı       =?= ı       = yes
ı       =?= (_ ⇒ _) = no
(_ ⇒ _) =?= ı       = no
σ₁ ⇒ τ₁ =?= σ₂ ⇒ τ₂ with σ₁ =?= σ₂ | τ₁ =?= τ₂
σ₁ ⇒ τ₁ =?= .σ₁ ⇒ .τ₁ | yes | yes = yes
σ₁ ⇒ τ₁ =?= σ₂ ⇒ τ₂   | _   | _   = no

infixl 80 _$_
data Raw : Set where
  var : Nat → Raw
  _$_ : Raw → Raw → Raw -- function application
  lam : Type → Raw → Raw

t1 : Type
t1 = ı

v1 : Raw
v1 = var 3

v2 : Raw
v2 = lam t1 v1

Cxt = List Type

data Term (Γ : Cxt) : Type → Set where
  var : ∀ {τ} → τ ∈ Γ → Term Γ τ
  _$_ : ∀ {σ τ} → Term Γ (σ ⇒ τ) → Term Γ σ → Term Γ τ
  lam : ∀ σ {τ} → Term (σ ∷ Γ) τ → Term Γ (σ ⇒ τ)

