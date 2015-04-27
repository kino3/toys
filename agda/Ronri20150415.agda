module Ronri20150415 where

data Prim : Set where
  mk : Prim

data Kata : Set where
  cons1 : Prim → Kata
  _⇒_ : Kata → Kata → Kata

α : Kata
α = cons1 mk
hoge2 : Kata
hoge2 =  ((cons1 mk) ⇒ (cons1 mk)) ⇒ (cons1 mk)
-- hoge2 = β → γ → β

{-
dainyu : Kata → Kata → Kata → Kata
dainyu (cons1 x) (cons1 x₁) c = {!!}
dainyu (a ⇒ a₁) (cons1 x) c = {!!}
dainyu a (A ⇒ B) c = {!!}
-}
