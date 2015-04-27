module ronri where

open import Data.Nat
open import Data.Nat.Primality
open import Relation.Nullary.Decidable
    
2-is-prime-proof : Prime 2
2-is-prime-proof = from-yes (prime? 2)

proof : Prime 9
proof = {!!}
