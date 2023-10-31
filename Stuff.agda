open import Cat.Prelude
open import 1Lab.Reflection renaming (typeError to typeError′ ; inContext to inContext′)
open import Data.List

open import Data.Sum hiding ([_,_])
open import Cat.Monoidal.Base

module Stuff where

open import Cat.Instances.Free

private
  variable
    ℓ ℓ′ : Level
    a b : Type ℓ

_⋄_ : String → String → String
_⋄_ = primStringAppend

infixr 10 _⋄_

graph : Graph lzero lzero
Graph.vert graph = el! Bool
Graph.edge graph false false = el! ⊤
Graph.edge graph false true = el! ⊤
Graph.edge graph true false = el! ⊥
Graph.edge graph true true = el! ⊥

open Graph graph

path-cat : Precategory lzero lzero
path-cat = Path-category graph

-- 𝒞 = Sets lzero
𝒞 = path-cat

open Precategory 𝒞 renaming (Hom to _⇒_)
open import Cat.Monoidal.Base using (Monoidal-category)

postulate
  𝒞-monoidal : Monoidal-category 𝒞

open Monoidal-category 𝒞-monoidal renaming (Unit to 𝟙)

postulate
  π₁ : ∀{x y : Ob} → (x ⊗ y) ⇒ x
  π₂ : ∀{x y : Ob} → (x ⊗ y) ⇒ y

data Converted {ℓ} (a : Type ℓ) : Type ℓ where
  conv : a → Converted a

fromConv : Converted a → a
fromConv (conv x) = x

Mappings : Type
Mappings = List (Name × Converted Name)

ETC : Type ℓ → Type ℓ
ETC a = Mappings → TC (a × Mappings)

get-mappings : ETC Mappings
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

runETC : Mappings → ETC a → TC a
runETC mappings etc = fst <$> etc mappings

execETC : Mappings → ETC a → TC ⊤
execETC mappings etc = runETC mappings etc >> pure tt

liftTC : TC a → ETC a
liftTC tc mappings = tc <&> λ x → (x , mappings)

try_catch_ : ETC a → ETC a → ETC a
try_catch_ f handler mappings = catchTC (f mappings) (handler mappings)

infixr 0 try_catch_

typeError : List ErrorPart → ETC a
typeError es = liftTC (typeError′ es)

throw : ErrorPart → ETC a
throw e = typeError [ e ]

_DEBUG_ : ErrorPart → ETC a → ETC a
e DEBUG etc = liftTC (debugPrint "" 0 [ strErr "⋆ ⋆ ⋆ ⋆ ⋆ ⋆ ⋆ ⋆ ⋆ ⋆ " , e ]) >> etc

infixr 0 _DEBUG_

STUB : ErrorPart → ETC a
STUB e = typeError [ "stub: " , e ]

inContext : Telescope → ETC a → ETC a
inContext tel etc mappings = inContext′ tel (etc mappings)

MaybeToETC : List ErrorPart → Maybe a → ETC a
MaybeToETC errs nothing = typeError errs
MaybeToETC _ (just x) = pure x

lookup-mapping : Mappings → Name → Maybe (Converted Name)
lookup-mapping [] _ = nothing
lookup-mapping ((k , v) ∷ xs) key with (primQNameEquality k key)
...                                | true = just v
...                                | false = lookup-mapping xs key

insert-mapping : Name → Converted Name → Mappings → Mappings
insert-mapping k v dict = (k , v) ∷ dict

get-name : Name → ETC (Converted Name)
get-name n =
  try get-existing-name
  catch create-name
  where
    get-existing-name = do
      mappings ← get-mappings
      MaybeToETC [] (lookup-mapping mappings n)
    create-name = do
      let new-name-str = primStringAppend "Cat." (primShowQName n)

      n′ ← conv <$> liftTC (freshName new-name-str)

      insert-mapping n n′ <$> get-mappings
      pure n′

id-term : Converted Term
id-term = conv (def (quote id) [])

comp-term : Converted Term → Converted Term → Converted Term
comp-term (conv f) (conv g) =
  conv (def (quote _∘_) [ argN f , argN g ])

prod-term : Converted Term → Converted Term → Converted Term
prod-term (conv f) (conv g) =
  conv (def (quote _⊗₁_) [ argN f , argN g ])

solve : Converted Name → List (Converted Term × Converted Term) → ETC ⊤
get-or-mk-def : Name → ETC (Converted Term)
mk-defs : List Name → ETC ⊤
build-composite : Name → Term → ETC (Converted Term)
build-prod : List (Arg Term) → ETC (Converted Term)
convert-clauses : Name → List Clause → ETC (List (Converted Term × Converted Term))
convert-var : Telescope → Nat → ETC (Converted Term)
convert-ap-term : Name → List (Arg Term) → ETC (Converted Term)
convert-expr : Term → ETC (Converted Term)
convert-pattern : Pattern → ETC (Converted Term)
convert-patterns : List (Arg Pattern) → ETC (Converted Term)

-- Create a definition for the given `Name` based on a list of equations
solve _ [] = STUB "solve _ []"
solve (conv n) ((conv (def f args) , conv rhs) ∷ []) =
  if n name=? f
  then
    liftTC (
      do tel ← getContext
         defineFun f [ clause tel [] rhs ])
  else
    STUB "solve: equation too complex"
solve n ((lhs , rhs) ∷ []) = STUB "solve: equation too complex"
solve _ (_ ∷ _ ∷ _) = STUB "solve: more than one equation"

{-# TERMINATING #-}
get-or-mk-def n = do
  n′ ← get-name n
  dfn ← liftTC (getDefinition (fromConv n′))
  mk-dfn n′ dfn
  pure (conv (def (fromConv n′) []))

  where
    mk-dfn : Converted Name → Definition → ETC ⊤
    mk-dfn n′ (function []) = do
      function cs ← liftTC (getDefinition n)
        where _ → typeError
                    [ "Not a function" , nameErr n , nameErr (fromConv n′) ]
      cs′ ← convert-clauses n cs
      solve n′ cs′
    mk-dfn _ _ = pure tt

mk-defs [] = pure tt
mk-defs (n ∷ ns) = do
  get-or-mk-def n
  mk-defs ns

build-composite n t = do
  conv n′ ← get-name n
  let f = conv (def n′ [])
  g ← convert-expr t
  pure (comp-term f g)

build-prod [] = pure id-term
build-prod (t v∷ []) = convert-expr t
build-prod (t v∷ ts@(_ v∷ _)) =
  prod-term <$> convert-expr t <*> build-prod ts
build-prod (t v∷ (_ ∷ ts)) = build-prod (t v∷ ts)
build-prod (_ ∷ ts) = build-prod ts

-- Insert the symbol being defined into its list of Patterns. Idempotent.
insert-name : Name → List (Arg Pattern) → List (Arg Pattern)
insert-name n ps@(arg i (dot (def n′ [])) ∷ _) = ps
insert-name n (arg i (proj f) ∷ ps) = arg i (proj f) ∷ insert-name n ps
insert-name n ps = argN (dot (def n [])) ∷ ps

convert-clauses _ [] = pure []
convert-clauses f (clause tel ps t ∷ cs) = do
  let ps′ = insert-name f ps
  eqn ← inContext tel (_,_ <$> convert-patterns ps′ <*> convert-expr t)
  (eqn ∷_) <$> convert-clauses f cs
convert-clauses _ (absurd-clause _ _ ∷ _) =
  STUB "convert-clauses _ absurd-clause"

convert-var [] n = throw "Variable not in scope"
convert-var (_ ∷ []) zero = pure id-term
convert-var (_ ∷ _) zero = pure (conv (def (quote π₁) []))
convert-var (_ ∷ (_ ∷ [])) (suc zero) = pure (conv (def (quote π₂) []))
convert-var (_ ∷ tel) (suc n) = do
  comp-term <$> convert-var tel n <*> pure (conv (def (quote π₂) []))

convert-ap-term f [] = get-or-mk-def f
convert-ap-term f as@(_ ∷ _) =
  comp-term <$> get-or-mk-def f <*> build-prod as

convert-expr (var x _) = do
  tel ← liftTC getContext
  convert-var tel x
convert-expr (con c as) = convert-ap-term c as
convert-expr (def f as) = convert-ap-term f as
convert-expr unknown = STUB "convert-expr unknown"
convert-expr _ = STUB "convert-expr _"

convert-pattern (con c _) = get-or-mk-def c
convert-pattern (dot t) = convert-expr t
convert-pattern (var x) = pure id-term
convert-pattern (lit l) = STUB "convert-pattern (lit l)"
convert-pattern (proj f) = get-or-mk-def f
convert-pattern (Pattern.absurd x) = STUB "convert-pattern (Pattern.absurd x)"

convert-patterns [] = pure id-term
convert-patterns (p v∷ []) = convert-pattern p
convert-patterns (p v∷ (var _ v∷ ps)) = convert-patterns (p v∷ ps)
convert-patterns (p v∷ ps) = do
  f ← convert-pattern p
  comp-term f <$> convert-patterns ps
convert-patterns _ = STUB "convert-patterns _"

catify : Mappings → TC ⊤
catify mappings = do
  let ns = map fst mappings
  execETC mappings (mk-defs ns)

module Input where
  postulate
    Going : Type
    Gone : Type
    step : Going → Going
    stop : Going → Gone

  step-stop : Going → Gone
  step-stop x = stop (step x)

Going Gone : Ob
Going = false
Gone = true

step : Going ⇒ Going
step = cons tt nil

stop : Going ⇒ Gone
stop = cons tt nil

step-stop : Going ⇒ Gone
unquoteDef step-stop =
  catify
  ((quote Input.step-stop , conv step-stop)
  ∷ (quote Input.step , conv (quote step))
  ∷ (quote Input.stop , conv (quote stop))
  ∷ []
  )
