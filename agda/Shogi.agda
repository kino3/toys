module Shogi where

-- implementation of Tsume-Shogi

data Teban : Set where
  sente : Teban
  gote  : Teban


open import Data.Vec
open import Data.List

data Fu : Set where
  c1 : Fu

record Fu1 : Set where
  field
    a : Fu

data Kyo : Set where
  c1 : Kyo

data Kei : Set where
  c1 : Kei

data Koma : Set where
  c1 : Fu → Koma


data Masume : Set where
  0' : Masume
  1' : Koma → Masume

record B : Set where
  field
    Ban : Vec (Vec Masume 9) 9
    teban : Teban
    sente-mochi : List Koma
    gote-mochi  : List Koma
