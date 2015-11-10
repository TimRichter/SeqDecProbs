> module NatProperties2

> import Decidable.Order
> import Syntax.PreorderReasoning

> import NatPredicates
> import NatOperations
> import Preorder
> import TotalPreorder
> import Basics
> import Unique
> import EqualityProperties

> import Control.Isomorphism

> %default total


> LTE' : Nat -> Nat -> Type
> LTE' m n = ( l : Nat ** m + l = n )

> lte'Unique1 : (m, n : Nat) -> Unique1 (\ l => m + l = n)
> lte'Unique1 m n l = uniqueEq (m + l) n

> lteTolte' : (m, n : Nat) ->
>             (m `LTE`  n) ->
>             (m `LTE'` n)
>
> lteTolte' Z       n      LTEZero          = ( n ** Refl )
> lteTolte' (S m') (S n') (LTESucc m'lten') = ( l ** mPlEQn ) where
>   m'lte'n' : m' `LTE'` n'
>   m'lte'n' = lteTolte' m' n' m'lten'
>   l : Nat
>   l = getWitness m'lte'n'
>   m'PlEQn' : m' + l = n'
>   m'PlEQn' = getProof m'lte'n'
>   mPlEQn : (S m') + l = (S n')
>   mPlEQn = cong m'PlEQn'

> lte'Tolte : (m, n : Nat) ->
>             (m `LTE'` n) ->
>             (m `LTE`  n)
> lte'Tolte Z       n      _             = LTEZero
> lte'Tolte (S m')  Z     ( l ** mPlEQZ) = absurd (ZnotS (sym mPlEQZ))
> lte'Tolte (S m') (S n') ( l ** mPlEQn) = LTESucc m'LTEn' where
>   m'PlEQn' : m' + l = n'
>   m'PlEQn' = succInjective (m' + l) n' mPlEQn
>   m'LTEn' : m' `LTE` n'
>   m'LTEn' = lte'Tolte m' n' ( l ** m'PlEQn')


 lteIsoLte' : (m, n : Nat) ->
             Iso (LTE m n) (LTE' m n)
 lteIsoLte' m n = MkIso to from toFrom fromTo where
   to : LTE m n -> LTE' m n
   to LTEZero




