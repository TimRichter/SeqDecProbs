> module Finite
> import Prelude.Maybe
> import Data.Fin
> import Control.Isomorphism
> import EmbProj
> 
> %default total 


> ||| Notion of finiteness for types
> Finite : Type -> Type
> Finite A = Exists (\ n => Iso A (Fin n))

This definition requires an exact cardinality |n| which may be
difficult to compute. But it is enough to know a finite bound, so an
alternative definition which may be more convenient is the following:

> FiniteSub : Type -> Type
> FiniteSub A = Exists (\ n => EmbProj A (Fin n))
