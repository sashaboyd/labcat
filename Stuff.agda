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

mk-def : List (Name × Name) → Name → TC (List (Name × Name))
mk-def mappings n = do
  new-mappings , n′ ← get-name mappings n
  catchTC
    (getDefinition n′ >> pure tt)
    (do
      function cs ← getDefinition n
        where _ → typeError [ nameErr n , nameErr n′ ]
      ty ← inferType (def n [])
      declareDef (argN n′) ty
      defineFun n′ cs
    )
  pure new-mappings

mk-defs : List (Name × Name) → List Name → TC ⊤
mk-defs mappings [] = pure tt
mk-defs mappings (n ∷ ns) = do
  new-mappings ← mk-def mappings n
  mk-defs new-mappings ns

catify : List (Name × Name) → TC ⊤
catify mappings = do
  let ns = map snd mappings
  mk-defs mappings ns
  pure tt

module Input where
  hello : ⊤
  hello = tt

module Output where
  unquoteDecl = catify []
  -- FIXME: this fails because of ‘unsolved metavariables’
  -- unquoteDecl hello = catify [ quote Input.hello , hello ]
