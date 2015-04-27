module Address where

-- Japanese Address representation with Dependent types.

record にほんのじゅうしょ : Set where


data 市 : Set where
  平塚市 : 市

data 大字 : 市 → Set where
  田村 : 大字 平塚市

