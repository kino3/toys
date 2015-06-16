module Proof where

open import Data.Nat

sample-proof : 2 ≤ 2
sample-proof = s≤s (s≤s z≤n)

sample-proof2 : 12 ≤ 15
sample-proof2 = s≤s
                  (s≤s
                   (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))))

open import Relation.Binary.Core using (_≡_;refl)

sample-proof3 : 2 + 4 ≡ 1 + 5
sample-proof3 = refl
