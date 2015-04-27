module Revision where

open import Data.String
open import Data.Nat
open import Data.Vec

record doc-rev1 : Set1 where
  constructor _,_,_,_,_
  field
    major : String
    name : String
    comment : String
    no : ℕ
    list : Vec String no

data Major : Set where
  Computer Biology Chemistry Others : Major

record doc-rev2 : Set1 where
  constructor _,_,_,_
  field
    major : Major
    name : String
    comment : String
    no : ℕ
    list : Vec String no

update : doc-rev1 → doc-rev2
update (major , name , comment , zero , list) = {!!}
update (major , name , comment , 1 , list) = {!!}
update (major , name , comment , _ , list) = {!!}
