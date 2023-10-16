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
open import Cat.Diagram.Limit.Finite using (Finitely-complete)
open import Cat.Instances.Sets.Complete using (Sets-finitely-complete)
𝒞-finitely-complete : Finitely-complete 𝒞
𝒞-finitely-complete = Sets-finitely-complete
open Finitely-complete 𝒞-finitely-complete
open import Cat.Diagram.Terminal using (Terminal)
open Terminal terminal renaming (top to 𝟙)

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

throwStr : String → ETC a
throwStr s = throw (strErr s)

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

mk-def : Name → ETC ⊤
mk-def n = do
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

mk-defs : List Name → ETC ⊤
mk-defs [] = pure tt
mk-defs (n ∷ ns) = do
  mk-def n
  mk-defs ns

id-term : Term
id-term = def (quote id) []

comp-term : Term → Term → Term
comp-term f g = def (quote _∘_) [ argN f , argN g ]

to-def : Name → Term
to-def n = def n []

build-composite : Name → Term → ETC Term
convert-expr : Term → ETC Term

build-composite n t = do
  n′ ← get-name n
  let f = def n′ []
  g ← convert-expr t
  pure (comp-term f g)

convert-expr (var x _) = pure id-term
convert-expr (con c []) = to-def <$> get-name c
convert-expr (con c ((var x _) v∷ _)) = to-def <$> get-name c
convert-expr (con c (t v∷ _)) = build-composite c t
convert-expr (con c (_ ∷ as)) = convert-expr (con c as)
convert-expr (def f []) = to-def <$> get-name f
convert-expr (def f (t v∷ _)) = build-composite f t
convert-expr (def f (_ ∷ as)) = convert-expr (def f as)
convert-expr unknown = throwStr "stub: convert-expr unknown"
convert-expr _ = throwStr "stub: convert-expr _"

convert-pattern : Pattern → ETC Term
convert-pattern (con c _) = pure (to-def c)
convert-pattern (dot t) = throwStr "stub: convert-pattern (dot t)"
convert-pattern (var x) = pure id-term
convert-pattern (lit l) = throwStr "stub: convert-pattern (lit l)"
convert-pattern (proj f) = pure (to-def f)
convert-pattern (Pattern.absurd x) = throwStr "convert-pattern (Pattern.absurd x)"

convert-patterns : List (Arg Pattern) → ETC Term
convert-patterns [] = pure id-term
convert-patterns (p v∷ ps) = do
  f ← convert-pattern p
  comp-term f <$> convert-patterns ps
convert-patterns _ = throwStr "stub: convert-patterns _"

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
