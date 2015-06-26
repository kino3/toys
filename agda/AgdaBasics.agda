module AgdaBasics where
-- Dependently Typed Programming in Agda
-- B4 Seminar at KU Kinoshita-Lab 2015

-- 2015.04.15 (1) by Prof. Kinoshita

data Bool : Set where
  true  : Bool
  false : Bool

not : Bool → Bool
not true = false
not false = true

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

-- 2015.04.22 (2) by Mr. Ono

_+_ : Nat → Nat → Nat
zero  + m = m
suc n + m = suc (n + m)
-- 定義の意味を先生が解説。
-- suc n + m = suc n + m とすると、Agdaはおこる。赤い色がつく。
-- 1 + 3 を解説。Nat式のかきかた、式変形のやりかた。
-- 2 + 0 を中村くん。

-- {-# BUILTIN NATURAL Nat #-}

_*_ : Nat → Nat → Nat
zero  * m = zero
suc n * m = m + (n * m)

-- 解説。
-- 1 * 0 を小野くん。
-- 途中、どちらから簡約してもよい、という話。
-- 合流性、もしくはチャーチ=ロッサー性
-- 2 * 1 を大倉くん。
-- おわりそうにない気がしたが、ちゃんとおわる。
-- 休憩後、 2 * 2 を高植くん。
-- さらに、∸を日㘴くん。

_∸_ : Nat → Nat → Nat
m ∸ zero = m
suc n ∸ t = suc (n ∸ t)
zero ∸ suc n = zero

-- これはData.Natの定義とはすこし違う。

_or_ : Bool → Bool → Bool
false or x = x
true  or _ = true

if_then_else_ : {A : Set} -> Bool -> A -> A -> A
if true  then x else y = x
if false then x else y = y

infixl 60 _*_
infixl 40 _+_
infixr 20 _or_
infix 5 if_then_else_

-- 2015.05.20 by 菅野

infixr 40 _::_
data List (A : Set) : Set where
  [] : List A
  _::_ : A -> List A -> List A

{-
(A : Set)がわからない、というはなし。

-}


data _⋆ (α : Set) : Set where
  ε : α ⋆
  _◅_ : α -> α ⋆ -> α ⋆

-- 2015.05.27 by 高植 but absent...
-- 2015.06.17 by 高植 

-- 2.2 Dependent functions

identity : (A : Set) → A → A
identity A x = x

zero' : Nat
zero' = identity Nat zero 

apply : (A : Set) (B : A → Set) → ((x : A) → B x) → (a : A) → B a
apply A B f a = f a

apply2 :          (B : Bool → Set) → ((x : Bool) → B x) → (a : Bool) → B a
apply2 B f true = f true
apply2 B f false = f false

identity2 : (A : Set) → A → A
identity2 = λ(A : Set) x → x

-- 2.3 Implicit arguments

id : {A : Set} → A → A
id x = x

true' : Bool
true' = id true

silly : {A : Set}{x : A} → A
silly {_}{x} = x

false' : Bool
false' = silly {x = false}

one : Nat
one = identity _ (suc zero)

_∘_ : {A : Set}{B : A → Set}{C : (x : A) → B x → Set}
      (f : {x : A}(y : B x) → C x y)(g : (x : A) → B x)
      (x : A) → C x (g x)
(f ∘ g) x = f (g x)

plus-two = suc ∘ suc

map : {A B : Set} → (A → B) → List A → List B
map f []        = []
map f (x :: xs) = f x :: map f xs

_++_ : {A : Set} → List A → List A → List A
[]      ++ ys = ys
x :: xs ++ ys = x :: (xs ++ ys)

-- 2.4 Datatype families

data Vec (A : Set) : Nat → Set where
  []   : Vec A zero
  _::_ : {n : Nat} → A → Vec A n → Vec A (suc n)

head : {A : Set}{n : Nat} → Vec A (suc n) → A
head (x :: xs) = x

-- Dot patterns

vmap : {A B : Set}{n : Nat} → (A → B) → Vec A n → Vec B n
vmap f []        = []
vmap f (x :: xs) = f x :: vmap f xs

data Vec₂ (A : Set) : Nat → Set where
  nil  : Vec₂ A zero
  cons : (n : Nat) → A → Vec₂ A n → Vec₂ A (suc n)

vmap₂ : {A B : Set}(n : Nat) → (A → B) → Vec₂ A n → Vec₂ B n
vmap₂ .zero    f nil           = nil
vmap₂ .(suc n) f (cons n x xs) = cons n (f x) (vmap₂ n f xs)

-- TODO vmap₃

data Image_∋_ {A B : Set}(f : A -> B) : B -> Set where
  im : (x : A) -> Image f ∋ f x

inv : {A B : Set}(f : A -> B)(y : B) -> Image f ∋ y -> A
inv f .(f x) (im x) = x

g : Nat → Nat
g n = suc (suc n)

hoge : (x : Nat) → Image g ∋ g x
hoge zero = im zero
hoge (suc x) = im (suc x)

piyo : Nat
piyo = inv g (g zero) (im zero)

-- Absurd patterns

data Fin : Nat → Set where
  fzero : {n : Nat} → Fin (suc n)
  fsuc  : {n : Nat} → Fin n → Fin (suc n)

magic : {A : Set} → Fin zero → A
magic ()

data Empty : Set where
  empty : Fin zero → Empty

magic' : {A : Set} → Empty → A
magic' (empty ())

-- TODO _!_, tabulate
_!_ : {n : Nat}{A : Set} → Vec A n → Fin n → A
[] ! ()
x :: xs ! fzero  = x
x :: xs ! fsuc y = xs ! y

tabulate : {n : Nat}{A : Set} → (Fin n → A) → Vec A n
tabulate {zero}  f = []
tabulate {suc n} f = f fzero :: tabulate (f ∘ fsuc)



-- 2.5 Programs as proofs

data   False : Set where
record True  : Set where

trivial : True
trivial = record {}

isTrue : Bool → Set
isTrue true  = True
isTrue false = False

_<_ : Nat → Nat → Bool
_     < zero  = false
zero  < suc n = true
suc m < suc n = m < n

length : {A : Set} → List A → Nat
length []        = zero
length (x :: xs) = suc (length xs)

lookup : {A : Set}(xs : List A)(n : Nat) → isTrue (n < length xs) → A
lookup []        n ()
lookup (x :: xs) zero    p = x
lookup (x :: xs) (suc n) p = lookup xs n p

data _==_ {A : Set}(x : A) : A → Set where
  refl : x == x

-- less than or equals (leq)
data _≤_ : Nat → Nat → Set where
  leq-zero : {n : Nat} → zero ≤ n
  leq-suc  : {m n : Nat} → m ≤ n → suc m ≤ suc n

leq-trans : {l m n : Nat} → l ≤ m → m ≤ n → l ≤ n
leq-trans leq-zero    _           = leq-zero
leq-trans (leq-suc p) (leq-suc q) = leq-suc (leq-trans p q)

-- 2.6 More on pattern matching

-- The with construct
min : Nat → Nat → Nat
min x y with x < y
... | true  = x
... | false = y

filter : {A : Set} → (A → Bool) → List A → List A
filter p []        = []
filter p (x :: xs) with p x
... | true  = x :: filter p xs
... | false = filter p xs

data _≠_ : Nat → Nat → Set where
  z≠s : {n : Nat} → zero ≠ suc n
  s≠z : {n : Nat} → suc n ≠ zero
  s≠s : {m n : Nat} → m ≠ n → suc m ≠ suc n

data Equal? (n m : Nat) : Set where
  eq  : n == m → Equal? n m
  neq : n ≠ m  → Equal? n m

{-# BUILTIN NATURAL Nat #-} --こうすると数字がつかえる
hoge2 : Equal? 3 4
hoge2 = neq (s≠s (s≠s (s≠s z≠s)))

equal? : (n m : Nat) → Equal? n m
equal? zero    zero    = eq refl
equal? zero    (suc m) = neq z≠s
equal? (suc n) zero    = neq s≠z
equal? (suc n) (suc m) with equal? n m
equal? (suc n) (suc .n) | eq refl = eq refl
equal? (suc n) (suc m)  | neq p   = neq (s≠s p)

hoge3 : Equal? 3 4
hoge3 = equal? 3 4

infix 20 _⊆_
data _⊆_ {A : Set} : List A → List A → Set where
  stop : [] ⊆ []
  drop : ∀ {xs y ys} → xs ⊆ ys →      xs ⊆ y :: ys
  keep : ∀ {x xs ys} → xs ⊆ ys → x :: xs ⊆ x :: ys

lem-filter : {A : Set}(p : A → Bool)(xs : List A) → filter p xs ⊆ xs
lem-filter p []        = stop
lem-filter p (x :: xs) with p x
lem-filter p (x :: xs) | true  = keep (lem-filter p xs)
lem-filter p (x :: xs) | false = drop (lem-filter p xs)

{-
lem-plus-zero : (n : Nat) → n + zero == n
lem-plus-zero zero    = refl
lem-plus-zero (suc n) = {!!}
  ?0 : (suc n) + zero == suc n
-}
-- suc n + zero = suc (n + zero) by Agda
--              = suc m          by me

lem-plus-zero : (n : Nat) → n + zero == n
lem-plus-zero zero    = refl
lem-plus-zero (suc n) with n + zero | lem-plus-zero n
lem-plus-zero (suc n) | .n | refl = refl

  -- ?0 : suc m == suc n

-- 2.7 Modules

module M where
  data Maybe (A : Set) : Set where
    nothing : Maybe A
    just    : A → Maybe A

  maybe : {A B : Set} → B → (A → B) → Maybe A → B
  maybe b f nothing  = b
  maybe b f (just x) = f x

module A where
  private
   internal : Nat
   internal = zero

  exported : Nat → Nat
  exported n = n + internal

mapMaybe₁ : {A B : Set} → (A → B) → M.Maybe A → M.Maybe B
mapMaybe₁ f M.nothing  = M.nothing
mapMaybe₁ f (M.just x) = M.just (f x)

mapMaybe₂ : {A B : Set} → (A → B) → M.Maybe A → M.Maybe B
mapMaybe₂ f m = let open M in maybe nothing (just ∘ f) m

open M

mapMaybe₃ : {A B : Set} → (A → B) → Maybe A → Maybe B
mapMaybe₃ f m = maybe nothing (just ∘ f) m

open M hiding (maybe)
  renaming (Maybe to _option; nothing to none; just to some)

mapOption : {A B : Set} → (A → B) → A option → B option
mapOption f none     = none
mapOption f (some x) = some (f x)

mtrue : Maybe Bool
mtrue = mapOption not (just false)

-- Parameterised modules
module Sort (A : Set)(_<_ : A → A → Bool) where
  insert : A → List A → List A
  insert y []        = y :: []
  insert y (x :: xs) with x < y
  insert y (x :: xs) | true  = x :: insert y xs
  insert y (x :: xs) | false = y :: x :: xs

  sort : List A → List A
  sort []        = []
  sort (x :: xs) = insert x (sort xs)

sort₁ : (A : Set)(_<_ : A → A → Bool) → List A → List A
sort₁ = Sort.sort

module SortNat = Sort Nat _<_

sort₂ : List Nat → List Nat
sort₂ = SortNat.sort

x = sort₂ (5 :: 3 :: 1 :: [])

-- 2.9 Exercises

-- Exercise 2.1. Matrix transposition

Matrix : Set → Nat → Nat → Set
Matrix A n m = Vec (Vec A n) m

vec : {n : Nat}{A : Set} → A → Vec A n
vec {zero}  x = []
vec {suc n} x = x :: vec x

infixl 90 _$_
_$_ : {n : Nat}{A B : Set} → Vec (A → B) n → Vec A n → Vec B n
[] $ [] = []
(f :: fs) $ (x :: xs) = f x :: fs $ xs

transpose : forall {A n m} → Matrix A n m → Matrix A m n
transpose []        = vec []
transpose (v :: vs) = ((vec _::_) $ v) $ transpose vs

--      _::_     :      A → (Vec A m → Vec A (suc m))
--  vec _::_     : Vec (A → (Vec A m → Vec A (suc m))) n
--  v            : Vec  A                              n
--  vec _::_ $ v : Vec (Vec A m → Vec A (suc m))) n
--  

trans23 : Matrix Nat 3 2 → Matrix Nat 2 3
trans23 ((x1 :: y1 :: z1 :: []) :: (x2 :: y2 :: z2 :: []) :: [])
  = ((x1 :: x2 :: []) :: (y1 :: y2 :: []) :: (z1 :: z2 :: []) :: []) 
m : Matrix Nat 3 0
m = []

