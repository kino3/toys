module HelloAgdaWorld2 where
open import IO.Primitive
open import Foreign.Haskell
open import Data.String

main : IO Unit
main = putStr (toCostring "TEST") >>= (λ x 
     → putStrLn (toCostring " is finished.")) -- putStrLn (toCostring "はろーあぐだわーるど。")

-- 日本語はマシンのロケールに依存して文字コードがかわるとのこと。
-- Haskellのライブラリの仕様。(IO.Primitiveに解説あり。)
