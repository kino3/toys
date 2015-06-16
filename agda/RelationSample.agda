module RelationSample where

open import Relation.Binary.Core
open import Level

data A : Set where
  a1 a2 a3 : A
data B : Set where
  b1 b2 : B

open import Data.Unit
open import Data.Empty

hoge : REL A B zero
hoge a1 b1 = ⊤
hoge a1 b2 = ⊥
hoge a2 b = {!!}
hoge a3 b = {!!}
