> module Quotient

> %default total

goal define a type class for types that can be takes as
quotients of a type by an equivalence relation

preliminary definitions

> data BinRel : Type -> Type where
>   MkBinRel :  {A : Type} -> 
>               (A -> A -> Type) -> 
>               BinRel A

> unwrapBinRel :  {A : Type} -> 
>                 BinRel A -> 
>                 A -> A -> Type
> unwrapBinRel (MkBinRel rel) = rel

> ||| Type of functions that map related members to equal 
> ||| values. Such compatible functions should be liftable 
> ||| to the quotient, see below.
>
> Compatible :  {A, B : Type} -> 
>               (A -> B) -> 
>               BinRel A -> 
>               Type
> Compatible {A} {B} f (MkBinRel rel) = 
>               {x, x' : A} -> 
>               rel x x' -> 
>               f x = f x'

> ||| We also want to be able to lift compatible functions
> ||| of two arguments A -> A -> B to functions Q -> Q -> B.
> ||| In particular we want this for maps A -> A -> Q obtained 
> ||| by composing a binary relation on A with the canonical 
> ||| map A -> Q.
> ||| 
> ||| If we had function extensionality, liftability in this 
> ||| sense of |f : A -> A -> B| where |Compatible2 f rel| is 
> ||| inhabited would follow from liftability (|liftC| and 
> ||| |liftCComp| in the quotient class below) of any Compatible 
> ||| function:
> ||| 
> ||| For |x : A|, |Compatible2 f rel| implies |Compatible (f x) rel|,
> ||| so there exists |liftC (f x) : Q -> B|. From the computation
> ||| rule |liftCComp| for |liftC| and surjectivity of |cla| we see 
> ||| that for related |x, x' : A|, |liftC (f x)| and |liftC (f x')|
> ||| are pointwise equal. If we had function extensionality, the map
> ||| | \x => lift1 (f x) | of type |A -> Q -> B| would be compatible 
> ||| and again using |liftC| we'd get the desired function of type 
> ||| |Q -> Q -> B|.
> ||| 
> ||| In absence of function extensionality, liftability of functions
> ||| |f : A -> A -> B| satisfying |Compatible2 f rel| is stronger
> ||| than |liftC|, and since we need it, we also specify |liftC2| and 
> ||| |liftC2Comp| within the Quotient class. 
> ||| That means more work in instance declarations, two more proofs 
> ||| have to be given. Usually, though, these will be just slight 
> ||| modifications of the proofs for |liftC| and |liftCComp|.
>
> Compatible2 : {A, B : Type} -> 
>               (A -> A -> B) -> 
>               BinRel A -> 
>               Type
> Compatible2 {A} {B} f (MkBinRel rel) = 
>               {x, x', y, y' : A} -> 
>               rel x x' ->
>               rel y y' ->
>               f x y = f x' y'
>

> {-- 
>     lifting property for dependent functions
>     probably can be deduced from lifting property
>     for independent functions ... ?
>
>     however, we don't need it now
>
> ||| type of compatible dependent functions
> ||| 
>
> CompatibleD : {A : Type} -> 
>               {B : A -> Type} ->
>               (f : (x : A) -> B x) ->
>               (rel : BinRel A) ->
>               (compB : Compatible B rel) -> 
>               Type
> CompatibleD {A} {B} f (MkBinRel rel) compB =
>               (x, y : A) ->
>               rel x y ->
>               f x = f y
> --}

 
> class Quotient (A : Type) (rel : BinRel A) (Q : Type) where
>   cla        : A -> Q
>   claC       : Compatible cla rel
>   liftC      : {B : Type} ->
>                (f : A -> B) ->
>                (Compatible f rel) ->
>                Q -> B
>   liftCComp  : {B : Type} ->
>                (f : A -> B) ->
>                (fC : Compatible f rel) ->
>                (x : A) -> (liftC f fC (cla x)) = f x
>   liftC2     : {B : Type} ->
>                (f : A -> A -> B) ->
>                (Compatible2 f rel) ->
>                Q -> Q -> B
>   liftC2Comp : {B : Type} ->
>                (f : A -> A -> B) ->
>                (fC : Compatible2 f rel) ->
>                (x, y : A) -> (liftC2 f fC (cla x) (cla y)) = f x y


