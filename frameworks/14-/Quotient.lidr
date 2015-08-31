> module Quotient

> import SplitQuotient

> %default total

goal define a type class for types that can be takes as
quotients of a type by an equivalence relation

preliminary definitions

> data BinRel : Type -> Type where
>   MkBinRel : {A : Type} -> (A -> A -> Type) -> BinRel A
>
> unwrapBinRel : {A : Type} -> BinRel A -> A -> A -> Type
> unwrapBinRel (MkBinRel rel) = rel


> class QuotientData (A : Type) (rel : BinRel A)  where
>   quotientType   :  Type
>   classOf        :  A -> quotientType
>   liftInvariant1 :  (f : A -> b) ->
>                     ((x, y : A) -> ((unwrapBinRel rel) x y) -> f x = fy) ->
>                     quotientType -> b


> Base : Type
> Base = Nat
> idempotentEndo : IdempotentEndo Base
> idempotentEndo = ( \x => 0 ** \x => Refl )
 

> kernel : (f : a -> b) -> BinRel a
> kernel f = MkBinRel rel where
>   rel x y = f x = f y

> kernelIdempotentEndo : BinRel Base
> kernelIdempotentEndo = kernel (getWitness idempotentEndo)
>
> allRel : BinRel Base
> allRel = MkBinRel rel where 
>   rel x y = ()


> instance QuotientData Base allRel where
>   quotientType = SQuot idempotentEndo
>   classOf = can idempotentEndo
>   liftInvariant1 f fIsInvariant = liftQ idempotentEndo f


