module memo20141205 where

-- set levels
data human : Set where
  harada takemi sembokuya kinoshita : human

data what : human → Set where
  tatoeba : (a : human) → what a

hoge : what harada
hoge = tatoeba harada

data fruits : Set where
  apple orange peach banana : fruits

record address : Set1 where
  field
    pref : Set
    fruit : fruits
