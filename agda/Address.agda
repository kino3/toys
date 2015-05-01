module Address where

-- Japanese Address representation with Dependent types.


data 都道府県 : Set where
  神奈川県 : 都道府県 

data 市 : 都道府県 → Set where
  平塚市 : 市 神奈川県

data 郡 : 都道府県 → Set where

data 町 : (p : 都道府県) → (郡 p) → Set where
data 村 : (p : 都道府県) → (郡 p) → Set where

data 大字 : {p : 都道府県} → 市 p → Set where
  田村 : 大字 平塚市

data 日本の住所 : Set where
  ordinary : (p : 都道府県) → (c : 市 p) → (o : 大字 c) → 日本の住所

x : 日本の住所
x = ordinary 神奈川県 平塚市 田村
