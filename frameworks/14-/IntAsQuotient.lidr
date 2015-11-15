> module IntAsQuotient

> import KernelQuotient
> import SplitQuotient as SQ
> import NatOperations
> import NatProperties
> import NatProperties2
> import Syntax.PreorderReasoning

> %default total

> NatPairs : Type
> NatPairs = (Nat, Nat)

> instance Num NatPairs where
>   (x , y) + (x' , y') = (x + x' , y + y')
>   (x , y) * (x' , y') = (x * x' + y * y' , x * y' + x' * y)
>   fromInteger x = (fromInteger x, fromInteger 0)

> SQ.Base = NatPairs
> SQ.Relation (x,y) (x',y') = x + y' = x' + y
> SQ.normalize (x , y) = (x - y, y - x)

> myMinusLemma1 : (a, b, c : Nat) ->
>                 (c `LTE` a) ->
>                 (a = b + c) ->
>                 (a - c = b)
> myMinusLemma1 Z      Z      Z      _                  _      = Refl
> myMinusLemma1 Z      Z      (S c') _                  aEQbPc = absurd (ZnotS aEQbPc)
> myMinusLemma1 Z      (S b') c      _                  aEQbPc = absurd (ZnotS aEQbPc)
> myMinusLemma1 (S a') Z      Z      _                  aEQbPc = absurd (ZnotS (sym aEQbPc))
> myMinusLemma1 (S a') Z      (S c') _                  aEQbPc = minusLemma0 aEQbPc
> myMinusLemma1 (S a') (S b') Z      _                  aEQbPc = trans aEQbPc (plusZeroRightNeutral (S b'))
> myMinusLemma1 (S a') (S b') (S c') (LTESucc c'LTEa')  aEQbPc = aMcEQb where
>   a'EQbPc' : a' = (S b') + c'
>   a'EQbPc' =
>     (a')           ={ succInjective a' (b' + (S c')) aEQbPc }=
>     (b' + (S c'))  ={ shiftSucc b' c' }=
>     ((S b') + c')  QED
>   aMcEQb : a' - c' = (S b')
>   aMcEQb = myMinusLemma1 a' (S b') c' c'LTEa' a'EQbPc' 
 
> myMinusLemma2 : (a, b, c : Nat) ->
>                 (c `LTE` a) ->
>                 (a - c = b) ->
>                 (a = b + c)
> myMinusLemma2  Z      Z      Z      _           _      = Refl
> myMinusLemma2  Z     (S b')  Z      _           aMcEQb = absurd (ZnotS aMcEQb)
> myMinusLemma2  Z      b     (S c')  LTEZero     _        impossible
> myMinusLemma2  Z      b     (S c') (LTESucc _)  _        impossible
> myMinusLemma2 (S a')  b      Z      _           aMcEQb = trans aMcEQb (sym (plusZeroRightNeutral b))
> myMinusLemma2 (S a')  b     (S c') (LTESucc c'LTEa') aMcEQb = aEQbPc where
>   a'EQbPc' : a' = b + c'
>   a'EQbPc' = myMinusLemma2 a' b c' c'LTEa' aMcEQb
>   aEQbPc   : S a' = b + S c'
>   aEQbPc =
>     (S a')     ={ cong {f = S} a'EQbPc' }=
>     (S b + c') ={ sym (shiftSucc b c')  }=
>     (b + S c') QED

> myMinusLemma3 : (a, b, c : Nat) -> b `LTE` a -> (a - b) + c = (a + c) - b
> myMinusLemma3  Z     Z       Z     LTEZero = Refl
> myMinusLemma3  Z     Z      (S c') LTEZero = Refl
> myMinusLemma3 (S a') Z       Z     LTEZero = Refl
> myMinusLemma3 (S a') Z      (S c') LTEZero = Refl
> myMinusLemma3 (S a') (S b')  Z     _       = Refl  

> SQ.normalizeMapsRelatedToEQ (x, y) (x', y') xPy'EQx'Py 
