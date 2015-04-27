module day20150421 where

open import Data.Nat
open import Relation.Binary.Core

-- rewrite を使う
plus-id-example : (n m : ℕ) → n ≡ m → n + n ≡ m + m
plus-id-example n m eq
  rewrite eq = refl

{-
練習問題: ★ (plus-id-exercise)
Admitted.を削除し、証明を完成させなさい。
-}
-- 複数使う場合は | で
plus-id-exercise : (n m o : ℕ) → n ≡ m → m ≡ o → n + m ≡ m + o
plus-id-exercise n m o eq1 eq2 rewrite eq1 | eq2 = {!!}

{-
rewrite a = goal
きもちとしては、goalのかたのいちぶぶんを、等式aをつかってかきかえる、
それによってgoal型がかわる、そんなかんじ？
http://wiki.portal.chalmers.se/agda/pmwiki.php?n=ReferenceManual.PatternMatching


-}
  -- rewrite eq1
  --       | eq2
  --       = refl
