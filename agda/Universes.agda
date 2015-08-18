{-
 Dependently typed programming in Agda
 3.2 Universes
-}
module Universes where

-- A familiar universe

-- The universe of decidable propositions
data   False : Set where
record True  : Set where

-- code
data Bool : Set where
  true false : Bool

-- decoder
isTrue : Bool → Set
isTrue true  = True
isTrue false = False

