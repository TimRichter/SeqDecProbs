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

> shiftSucc : (a, b : Nat) -> (a + S b = S a + b)
> shiftSucc Z b = Refl
> shiftSucc (S a) b =
>   (S a + S b)    ={ Refl }=
>   (S (a + S b))  ={ cong {f = S} (shiftSucc a b) }=
>   (S (S a + b))  ={ Refl }=
>   (S (S a) + b)  QED

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


> lteLemma1' : (m, n : Nat) -> (S m) `LTE` n -> m `LTE` n
> lteLemma1' m n smLTEn with (lteTolte' (S m) n smLTEn)
>   | (l ** smPlEQn) = lte'Tolte m n ( (S l) ** mPslEQn ) where
>     mPslEQn : m + (S l) = n
>     mPslEQn = trans (shiftSucc m l) smPlEQn

> eqInLTE' : (m, n : Nat) -> m = n -> m `LTE` n
> eqInLTE' m n mEQn = lte'Tolte m n (0 ** mP0EQn) where
>   mP0EQn : m + 0 = n
>   mP0EQn = trans (plusZeroRightNeutral m) mEQn

> strengthenLT' : (m, n : Nat) -> LT m (S n) -> Not (m = n) -> LT m n
> strengthenLT' m n smLTEsn notmEQn with (lteTolte' (S m) (S n) smLTEsn)
>   | (Z ** smP0EQsn) = absurd (notmEQn mEQn) where
>     mEQn : m = n
>     mEQn = trans (sym (plusZeroRightNeutral m)) (succInjective (m + 0) n smP0EQsn)
>   | (S l ** smPslEQsn) = lte'Tolte (S m) n (l ** smPlEQn) where
>     smPlEQn : (S m) + l = n
>     smPlEQn = trans (sym (shiftSucc m l)) 
>                     (succInjective (m + (S l)) n smPslEQsn)

> myMinusLemma0 : (a, b: Nat) ->
>                 (a `LTE` b) ->
>                 (a + (b - a) = b)
> myMinusLemma0 Z Z LTEZero

 lteIsoLte' : (m, n : Nat) ->
             Iso (LTE m n) (LTE' m n)
 lteIsoLte' m n = MkIso to from toFrom fromTo where
   to : LTE m n -> LTE' m n
   to LTEZero




