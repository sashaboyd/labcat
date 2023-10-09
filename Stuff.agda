open import Cat.Prelude
open import 1Lab.Reflection
open import Data.List

open import Data.Sum hiding ([_,_])
open import Cat.Monoidal.Base

module Stuff where

private
  variable
    ℓ ℓ′ : Level
    a b : Type ℓ

sep : ErrorPart
sep = strErr "\t∥\t"

{-# TERMINATING #-}
show-pattern : Arg Pattern → List ErrorPart
show-pattern (arg _ (con c ps)) = sep ∷ strErr (primStringAppend "𝒸" (primShowQName c)) ∷ concat (map show-pattern ps)
show-pattern (arg _ (dot t)) = [ sep , strErr "·", termErr t , sep ]
show-pattern (arg _ (var x)) = [ sep , strErr "𝓋", strErr (primShowNat x), sep ]
show-pattern (arg _ (lit l)) = [ sep , strErr "lit", sep ]
show-pattern (arg _ (proj f)) = [ sep , strErr "π", strErr (primShowQName f), sep ]
show-pattern (arg _ (Pattern.absurd x)) = [ sep , strErr "absurd", sep ]

𝒞 = Sets lzero
open Precategory 𝒞 renaming (Hom to _⇒_)

Maybe-to-TC : List ErrorPart → Maybe a → TC a
Maybe-to-TC errs nothing = typeError errs
Maybe-to-TC _ (just x) = pure x

lookup-dict : List (Name × Name) → Name → Maybe Name
lookup-dict [] _ = nothing
lookup-dict ((k , v) ∷ xs) key with (primQNameEquality k key)
...                                | true = just v
...                                | false = lookup-dict xs key

insert-dict : Name → Name → List (Name × Name) → List (Name × Name)
insert-dict k v dict = (k , v) ∷ dict

get-name : List (Name × Name) → Name → TC (List (Name × Name) × Name)
get-name mappings n =
  catchTC get-existing-name create-name
  where
    get-existing-name = do
      n′ ← Maybe-to-TC [] (lookup-dict mappings n)
      pure (mappings , n′)
    create-name = do
      let new-name-str = primStringAppend "Cat." (primShowQName n)

      n′ ← freshName new-name-str

      let new-mappings = insert-dict n n′ mappings
      pure (new-mappings , n′)

mk-morph : List (Name × Name) → TC ⊤
mk-morph mappings = do
  pure tt

module Output where
  unquoteDecl = mk-morph []
