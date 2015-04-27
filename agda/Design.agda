module Design where

open import Function
open import Data.Bool
--open import Data.List
open import Data.String
open import Data.Vec
open import Data.Nat
open import Data.Product

record Button : Set where
  field
    label : String
    enabled : Bool

  switch : Bool → Bool
  switch true = false
  switch false = true

data Component : Set where
  mkButton : Button → Component

record Dialog : Set2 where
 field 
  components : {n : ℕ} → Vec Component n

run : Button
run = record { label = "Run" ; enabled = true }

--operation : Dialog → Dialog
--operation _ = {!!}

sample : Dialog
sample = {!!}

data Interaction : Set3 where
  see   : {n : ℕ} → Vec Button n → Interaction
  think : Interaction → String → Interaction
  ope   : Interaction

{-
testcase1 : List Interaction
testcase1 = think (see (Dialog.Buttons sample)) "Oh, it is a button!" ∷ 
  {!!} ∷ {!!}
-}

action1 : Σ[ x ∈ Component ] String
action1 = (Σ[ x ∈ Component ] String) ∋ (mkButton run) , "OK, push button."

