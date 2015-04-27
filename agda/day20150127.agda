module day20150127 where

open import Data.Bool


record button : Set where
  field
    flag : Bool

  switch : Bool → Bool
  switch true = false
  switch false = true

record dialog : Set1 where
 field 
  hoge : button

operation : dialog → dialog
operation _ = ?



sample : dialog
sample = record { hoge = record { flag = false } }

open import Data.String
data interaction : Set1 where
  see : dialog → interaction
  think : interaction → String → interaction
  ope : operation → interaction

open import Data.List
testcase1 : List interaction
testcase1 = think (see sample) "Oh, it is a button!" ∷ {!ope!}
