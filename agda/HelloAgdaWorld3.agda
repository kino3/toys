module HelloAgdaWorld3 where
open import IO.Primitive using (IO)
open import Foreign.Haskell -- Unit
open import Data.String

postulate
  putStrLnAgda : String → IO Unit
{-# COMPILED putStrLnAgda putStrLn #-}

main : IO Unit
main = putStrLnAgda "Hello, Agda."
