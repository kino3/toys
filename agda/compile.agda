module HelloAgdaWorld where
open import IO.Primitive
open import Foreign.Haskell
open import Data.String

main : IO Unit
main = putStrLn (toCostring "Hello, agda world!")
