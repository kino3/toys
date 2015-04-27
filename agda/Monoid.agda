module Monoid where

open import Relation.Binary

record Monoid : Set1 where
  field
    setoid : Setoid ? ?
