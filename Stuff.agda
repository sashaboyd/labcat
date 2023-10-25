open import Cat.Prelude
open import 1Lab.Reflection renaming (typeError to typeError′)
open import Data.List

open import Data.Sum hiding ([_,_])
open import Cat.Monoidal.Base

module Stuff where

private
  variable
    ℓ ℓ′ : Level
    a b : Type ℓ

𝒞 = Sets lzero
open Precategory 𝒞 renaming (Hom to _⇒_)
open import Cat.Monoidal.Base using (Monoidal-category)

postulate
  𝒞-monoidal : Monoidal-category 𝒞

open Monoidal-category 𝒞-monoidal renaming (Unit to 𝟙)

postulate
  π₁ : ∀{x y : Ob} → (x ⊗ y) ⇒ x
  π₂ : ∀{x y : Ob} → (x ⊗ y) ⇒ y

ETC : Type ℓ → Type ℓ
ETC a = List (Name × Name) → TC (a × List (Name × Name))

get-mappings : ETC (List (Name × Name))
get-mappings mappings = pure (mappings , mappings)

map-fst : ∀{r : Type ℓ} → (a → b) → (a × r → b × r)
map-fst f (x , y) = f x , y

instance
  Map-ETC : Map (eff ETC)
  Map._<$>_ Map-ETC f etc mappings =
    map-fst f <$> etc mappings

  Idiom-ETC : Idiom (eff ETC)
  Idiom.Map-idiom Idiom-ETC = Map-ETC
  Idiom.pure Idiom-ETC x mappings = pure (x , mappings)
  Idiom._<*>_ Idiom-ETC etc-f etc-x mappings = do
    f , mappings′ ← etc-f mappings
    x , mappings′′ ← etc-x mappings′
    pure (f x , mappings′′)

  Bind-ETC : Bind (eff ETC)
  Bind._>>=_ Bind-ETC etc-x etc-f mappings = do
    x , mappings′ ← etc-x mappings
    etc-f x mappings′
  Bind.Idiom-bind Bind-ETC = Idiom-ETC

runETC : List (Name × Name) → ETC a → TC a
runETC mappings etc = fst <$> etc mappings

execETC : List (Name × Name) → ETC a → TC ⊤
execETC mappings etc = runETC mappings etc >> pure tt

liftTC : TC a → ETC a
liftTC tc mappings = tc <&> λ x → (x , mappings)

try_catch : ETC a → ETC a → ETC a
try_catch f handler mappings = catchTC (f mappings) (handler mappings)

typeError : List ErrorPart → ETC a
typeError es = liftTC (typeError′ es)

throw : ErrorPart → ETC a
throw e = typeError [ e ]

MaybeToETC : List ErrorPart → Maybe a → ETC a
MaybeToETC errs nothing = typeError errs
MaybeToETC _ (just x) = pure x

lookup-dict : List (Name × Name) → Name → Maybe Name
lookup-dict [] _ = nothing
lookup-dict ((k , v) ∷ xs) key with (primQNameEquality k key)
...                                | true = just v
...                                | false = lookup-dict xs key

insert-dict : Name → Name → List (Name × Name) → List (Name × Name)
insert-dict k v dict = (k , v) ∷ dict

get-name : Name → ETC Name
get-name n =
  try get-existing-name
  catch create-name
  where
    get-existing-name = do
      mappings ← get-mappings
      MaybeToETC [] (lookup-dict mappings n)
    create-name = do
      let new-name-str = primStringAppend "Cat." (primShowQName n)

      n′ ← liftTC (freshName new-name-str)

      insert-dict n n′ <$> get-mappings
      pure n′

get-or-mk-def : Name → ETC Term
get-or-mk-def n = do
  n′ ← get-name n
  liftTC $ catchTC
    (getDefinition n′ >> pure tt)
    (do
      function cs ← getDefinition n
        where _ → typeError′ [ nameErr n , nameErr n′ ]
      ty ← inferType (def n [])
      declareDef (argN n′) ty
      defineFun n′ cs
    )
  pure (def n′ [])

mk-defs : List Name → ETC ⊤
mk-defs [] = pure tt
mk-defs (n ∷ ns) = do
  get-or-mk-def n
  mk-defs ns

id-term : Term
id-term = def (quote id) []

comp-term : Term → Term → Term
comp-term f g = def (quote _∘_) [ argN f , argN g ]

prod-term : Term → Term → Term
prod-term f g = def (quote _⊗₁_) [ argN f , argN g ]

build-composite : Name → Term → ETC Term
build-prod : List (Arg Term) → ETC Term
convert-var : Telescope → Nat → ETC Term
convert-ap-term : Name → List (Arg Term) → ETC Term
convert-expr : Term → ETC Term

build-composite n t = do
  n′ ← get-name n
  let f = def n′ []
  g ← convert-expr t
  pure (comp-term f g)

build-prod [] = pure id-term
build-prod (t v∷ []) = convert-expr t
build-prod (t v∷ ts@(_ v∷ _)) =
  prod-term <$> convert-expr t <*> build-prod ts
build-prod (t v∷ (_ ∷ ts)) = build-prod (t v∷ ts)
build-prod (_ ∷ ts) = build-prod ts

convert-var [] n = throw "Variable not in scope"
convert-var (_ ∷ []) zero = pure id-term
convert-var (_ ∷ _) zero = pure (def (quote π₁) [])
convert-var (_ ∷ (_ ∷ [])) (suc zero) = pure (def (quote π₂) [])
convert-var (_ ∷ tel) (suc n) = do
  comp-term <$> convert-var tel n <*> pure (def (quote π₂) [])

convert-ap-term f [] = get-or-mk-def f
convert-ap-term f as@(_ ∷ _) =
  comp-term <$> get-or-mk-def f <*> build-prod as

convert-expr (var x _) = do
  tel ← liftTC getContext
  convert-var tel x
convert-expr (con c as) = convert-ap-term c as
convert-expr (def f as) = convert-ap-term f as
convert-expr unknown = throw "stub: convert-expr unknown"
convert-expr _ = throw "stub: convert-expr _"

convert-pattern : Pattern → ETC Term
convert-pattern (con c _) = get-or-mk-def c
convert-pattern (dot t) = throw "stub: convert-pattern (dot t)"
convert-pattern (var x) = pure id-term
convert-pattern (lit l) = throw "stub: convert-pattern (lit l)"
convert-pattern (proj f) = get-or-mk-def f
convert-pattern (Pattern.absurd x) = throw "stub: convert-pattern (Pattern.absurd x)"

convert-patterns : List (Arg Pattern) → ETC Term
convert-patterns [] = pure id-term
convert-patterns (p v∷ ps) = do
  f ← convert-pattern p
  comp-term f <$> convert-patterns ps
convert-patterns _ = throw "stub: convert-patterns _"

catify : List (Name × Name) → TC ⊤
catify mappings = do
  let ns = map snd mappings
  execETC mappings (mk-defs ns)

module Input where
  postulate
    Thing : Type
    thing : ⊤ → Thing

  hello : ⊤ → Thing
  hello x = thing x

postulate
  Thing : Ob
  thing : 𝟙 ⇒ Thing

hello : 𝟙 ⇒ Thing
