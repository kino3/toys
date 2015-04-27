module ISO15288 where

open import Data.List
open import Data.String
open import Data.Bool

postulate
  Evidence-Type : Set

record Task : Set where
  field
    Name : String
    Detail : String
    Done? : Bool
    Evidence : Evidence-Type

record Activity : Set where
  field
    Tasks : List Task

record Process : Set where
  field
    Name : String
    Objective : String
    Outcome : List String
    Activities : List Activity
    
sampleTask : Task
sampleTask = record { Name = ? ; Detail = ? ; Done? = ? ; Evidence = ? }
