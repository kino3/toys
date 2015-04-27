module DrinkerParadox where 
_∋_ : (A : Set) → A → A
A ∋ a = a

module 論理 where

  record ∃{A : Set}(P : A → Set) : Set where
    constructor _,_
    field
      具体例             : A
      例であることの証明 : P 具体例

  infixr 1 _∨_
  data _∨_(A B : Set) : Set where
    左 : A → A ∨ B
    右 : B → A ∨ B

  場合分け : {A B C : Set} → A ∨ B → (A → C) → (B → C) → C
  場合分け (左 a) f g = f a
  場合分け (右 b) f g = g b


  data ⊥ : Set where

  偽から何でも : {A : Set} → ⊥ → A
  偽から何でも ()

  infix 3 ¬_
  ¬_ : (A : Set) → Set
  ¬ A = A → ⊥

  偽から何でも′ : {A B : Set} → ¬ B →  B → A
  偽から何でも′ nb b = 偽から何でも (nb b)

  module 古典論理 where
    postulate
      排中律証明 : {A : Set} → A ∨ ¬ A 

    _か否かで場合分け : {C : Set}(A : Set) → (A → C) → (¬ A → C) → C
    A か否かで場合分け = 場合分け 排中律証明

    背理法 : {A : Set} → ¬ ¬ A → A
    背理法 {A} nna = (A か否かで場合分け) (λ a → a) (偽から何でも′ nna)

module 飲客逆説
       (客達 : Set)
       (飲 : 客達 → Set)
       (常連 : 客達) where
  open 論理
  open 古典論理

  _は_ : {A : Set} → A → (B : A → Set) → Set
  x は P = P x

  飲んでいる : 客達 → Set
  飲んでいる = 飲

  飲者逆説 = ∃ λ x → x は 飲んでいる  → ∀ y → 飲 y
  非飲者在 = ∃ λ x → ¬ 飲 x

  証明 : 飲者逆説 
  証明 = (非飲者在 か否かで場合分け) 場合1 場合2 where

    場合1 : 非飲者在 → 飲者逆説
    場合1 (x , x非飲証明) = (x , 偽から何でも′ x非飲証明)

    場合2 : ¬ 非飲者在 → 飲者逆説
    場合2 非飲者無証明 = (常連 , (λ _ → 全者飲証明)) where
      全者飲証明 : ∀ y → 飲 y
      全者飲証明 y =
        背理法 (λ y非飲証明 → 非飲者無証明 (y , y非飲証明))

module 飲客逆説:直観主義
       (客達 : Set)
       (飲 : 客達 → Set)
       (常連 : 客達) where
  open 論理

  飲者逆説 = ¬ ¬ ∃ λ x → ¬ ¬ 飲 x  → ∀ y → ¬ ¬ 飲 y

  証明 : 飲者逆説 
  証明 h = h (常連 , (λ _ y y非飲 →
                      h (y ,
                         (λ y非非飲 → 偽から何でも(y非非飲 y非飲)))))

