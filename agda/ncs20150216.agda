module ncs20150216 where

data Ku : Set where
  Shibuya : Ku
  Shinjuku : Ku
  Meguro : Ku

data Machi : Ku → Set where
  Shimomeguro : Machi Meguro
  Kamimeguro : Machi Meguro
  Ebisu : Machi Shibuya
  Daikanyama : Machi Shibuya

hoge : Machi Shibuya
hoge = Ebisu
