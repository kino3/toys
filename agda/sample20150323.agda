module sample20150323 where

data Day : Set where
  mon tue wed thu fri sat sun : Day

tomorrow : Day → Day
tomorrow mon = tue
tomorrow tue = wed
tomorrow wed = thu
tomorrow thu = fri
tomorrow fri = sat
tomorrow sat = sun
tomorrow sun = mon

yesterday : Day → Day
yesterday mon = sun
yesterday tue = mon
yesterday wed = tue
yesterday thu = wed
yesterday fri = thu
yesterday sat = fri
yesterday sun = sat

open import Relation.Binary.Core

theorem : (d : Day) → d ≡ yesterday (tomorrow d)
theorem mon = refl
theorem tue = refl
theorem wed = refl
theorem thu = refl
theorem fri = refl
theorem sat = refl
theorem sun = refl

