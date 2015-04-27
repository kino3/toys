module test where 

data Suit : Set where
  ♠ ♥ ♣ ♢ : Suit

spade : Suit
spade = ♠

data Suit2 : Set where
  ♠ : Suit2
  ♥ : Suit2
  ♣ : Suit2
  ♢ : Suit2

data Bool : Set where
  true false : Bool

case_♠∶_♥∶_♣∶_♢∶_ : Suit → Set → Set → Set → Set → Set
case ♠ ♠∶ x ♥∶ x₁ ♣∶ x₂ ♢∶ x₃ = x
case ♥ ♠∶ x ♥∶ x₁ ♣∶ x₂ ♢∶ x₃ = x₁
case ♣ ♠∶ x ♥∶ x₁ ♣∶ x₂ ♢∶ x₃ = x₂
case ♢ ♠∶ x ♥∶ x₁ ♣∶ x₂ ♢∶ x₃ = x₃

if_then_else_ : Bool → Suit → Suit → Suit
if true then x else x₁ = x
if false then x else x₁ = x₁
