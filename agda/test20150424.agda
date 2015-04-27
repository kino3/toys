module test20150424 where

open import Data.Nat

record Sample : Set where
  constructor _,_,_
  field
    n1 : ℕ
    n2 : ℕ
    n3 : ℕ

hoge : Sample
hoge = record { n1 = 1 ; n2 = 2 ; n3 = 5 }


hoge2 : Sample
hoge2 = 1 , 4 , 5
