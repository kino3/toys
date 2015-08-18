{-
 Dependently typed programming in Agda
 3.2 Universes
-}
module Universes where

-- A familiar universe

-- The universe of decidable propositions
data   False : Set where
record True  : Set where

-- Bool is a code
data Bool : Set where
  true false : Bool

-- decoder
isTrue : Bool → Set
isTrue true  = True
isTrue false = False

infix 30 not_
infixr 25 _and_

not_ : Bool → Bool
not true  = false
not false = true

_and_ : Bool → Bool → Bool
true  and x = x
false and _ = false

notNotId : (a : Bool) → isTrue (not not a) → isTrue a
notNotId true x = x
notNotId false ()


