> module Main

> import Decidable.Order

> import Data.Fin
> import Data.Vect
> import Data.List
> import Data.List.Quantifiers
> import Data.So
> import Control.Isomorphism
> import Effects
> import Effect.Exception
> import Effect.StdIO
> import Syntax.PreorderReasoning

> import SeqDecProbsCoreAssumptions
> import SeqDecProbsCoreTheory
> import SeqDecProbsCoreUtils

> import ListOperations
> import ListProperties
> import BoundedNat
> import BoundedNatOperations
> import BoundedNatProperties
> import Sigma
> import SigmaOperations
> import SigmaProperties
> import NatProperties
> import Finite
> import FiniteOperations
> import FiniteProperties
> import Unique
> import Decidable
> import SingletonProperties
> import Opt
> import TotalPreorder
> import EffectException
> import EffectStdIO
> import FinOperations
> import PairsOperations

> %default total
> %auto_implicits off


> -- %logging 5

We reimplement "SeqDecProbsExample1.lidr", this time with |M = List|.



* The monad M (List):


** M is a monad:

> SeqDecProbsCoreAssumptions.M = List

> SeqDecProbsCoreAssumptions.fmap = ListOperations.fmap

> SeqDecProbsCoreAssumptions.ret = ListOperations.ret

> SeqDecProbsCoreAssumptions.bind = ListOperations.bind


** M is a container monad:

> SeqDecProbsCoreAssumptions.Elem = Data.List.Elem

> SeqDecProbsCoreAssumptions.All = Data.List.Quantifiers.All

> SeqDecProbsCoreAssumptions.tagElem = ListOperations.tagElem

> SeqDecProbsCoreAssumptions.containerMonadSpec3 = ListProperties.containerMonadSpec3


** M is measurable:

> SeqDecProbsCoreAssumptions.meas = sum

> SeqDecProbsCoreAssumptions.measMon = sumMon



* The decision process:

> maxColumn : Nat
> maxColumn = 10

> nColumns : Nat
> nColumns = S maxColumn


** States:

> SeqDecProbsCoreAssumptions.State t = LTB nColumns

> column : {t : Nat} -> State t -> Nat
> column = outl


** Actions:

> data Action = Left | Ahead | Right

> implementation Eq Action where
>   (==) Left   Left = True
>   (==) Left      _ = False
>   (==) Ahead Ahead = True
>   (==) Ahead     _ = False
>   (==) Right Right = True
>   (==) Right     _ = False

> implementation Show Action where
>   show Left  = "L"
>   show Ahead = "A"
>   show Right = "R"

*** Action is finite:

> to : Action -> Fin 3
> to Left  =        FZ
> to Ahead =     FS FZ
> to Right = FS (FS FZ)

> from : Fin 3 -> Action
> from             FZ   = Left
> from         (FS FZ)  = Ahead
> from     (FS (FS FZ)) = Right
> from (FS (FS (FS k))) = absurd k

> toFrom : (k : Fin 3) -> to (from k) = k
> toFrom             FZ   = Refl
> toFrom         (FS FZ)  = Refl
> toFrom     (FS (FS FZ)) = Refl
> toFrom (FS (FS (FS k))) = absurd k

> fromTo : (a : Action) -> from (to a) = a
> fromTo Left  = Refl
> fromTo Ahead = Refl
> fromTo Right = Refl

> fAction : Finite Action
> fAction = MkSigma 3 (MkIso to from toFrom fromTo)
> %freeze fAction


** Controls:

> SeqDecProbsCoreAssumptions.Ctrl t x = Action

*** Controls are finite:

> fCtrl : (t : Nat) -> (x : State t) -> Finite (Ctrl t x)
> fCtrl t x = fAction

*** Controls are not empty:

> nefCtrl : (t : Nat) -> (x : State t) -> NonEmpty (fCtrl t x)
> nefCtrl t x = nonEmptyLemma (fCtrl t x) Left


** Transition function:

> SeqDecProbsCoreAssumptions.step t (MkSigma Z prf) Left =
>   [MkSigma maxColumn (ltIdS maxColumn)]
> SeqDecProbsCoreAssumptions.step t (MkSigma (S n) prf) Left =
>   [MkSigma n (ltLemma1 n nColumns prf)]
> SeqDecProbsCoreAssumptions.step t (MkSigma n prf) Ahead =
>   [MkSigma n prf]
> SeqDecProbsCoreAssumptions.step t (MkSigma n prf) Right with (decLT n maxColumn)
>   | (Yes p)     = [MkSigma (S n) (LTESucc p)]
>   | (No contra) = [MkSigma  Z    (LTESucc LTEZero)]


** Reward function:

> SeqDecProbsCoreAssumptions.reward t x y x' =
>   if column {t = S t} x' == Z
>   then (S Z)
>   else if S (column {t = S t} x') == nColumns
>        then (S (S Z))
>        else Z



* Viable and Reachable

> -- Viable : (n : Nat) -> State t -> Type
> SeqDecProbsCoreAssumptions.Viable {t}  n    _  =  Unit

> -- viableSpec1 : (x : State t) -> Viable (S n) x -> Exists (\ y => All (Viable n) (step t x y))
> SeqDecProbsCoreAssumptions.viableSpec1 {t} {n} x _ = s3 where
>   y : Ctrl t x
>   y = Left
>   mx' : List (State (S t))
>   mx' = step t x y 
>   s2  : SeqDecProbsCoreAssumptions.All (Viable {t = S t} n) mx'
>   s2  = all mx' where
>     all : (xs : List (State (S t))) -> SeqDecProbsCoreAssumptions.All (Viable {t = S t} n) xs
>     all Nil = Nil
>     all (x :: xs) = () :: (all xs)
>   s3  : Exists {a = Ctrl t x} (\ y => SeqDecProbsCoreAssumptions.All (Viable {t = S t} n) (step t x y))
>   s3  = Evidence y s2

> -- Reachable : State t' -> Type
> SeqDecProbsCoreAssumptions.Reachable {t'} _ = Unit

> -- reachableSpec1 : (x : State t) -> Reachable {t' = t} x -> (y : Ctrl t x) -> All (Reachable {t' = S t}) (step t x y)
> SeqDecProbsCoreAssumptions.reachableSpec1 {t} x r y = all (step t x y) where
>   all : (xs : List (State (S t))) -> SeqDecProbsCoreAssumptions.All (Reachable {t' = S t}) xs
>   all Nil = Nil
>   all (x :: xs) = () :: (all xs)



* Max and argmax

We want to implement

< max    : {t : Nat} -> {n : Nat} -> 
<          (x : State t) -> 
<          .(Viable (S n) x) ->
<          (f : Sigma (Ctrl t x) (\ y => All (Viable n) (step t x y)) -> Nat) ->
<          Nat
< argmax : {t : Nat} -> {n : Nat} -> 
<          (x : State t) -> 
<          .(Viable (S n) x) ->
<          (f : Sigma (Ctrl t x) (\ y => All (Viable n) (step t x y)) -> Nat) ->
<          Sigma (Ctrl t x) (\ y => All (Viable n) (step t x y))

This can be easily done using |Opt.max| and |Opt.argmax| if we can show
that |Sigma (Ctrl t x) (\ y => All (Viable n) (step t x y))| is finite and
non-empty for every |t : Nat|, |x : State t| such that |Viable (S n) x|. If
we have finiteness

> fCtrlAV : (t : Nat) -> (n : Nat) -> (x : State t) -> Viable {t = t} (S n) x ->
>           Finite (Sigma (Ctrl t x) (\ y => SeqDecProbsCoreAssumptions.All (Viable {t = S t} n) (step t x y)))

non-emptiness is straightforward:

> neCtrlAV : (t : Nat) -> (n : Nat) -> (x : State t) -> (v : Viable {t = t} (S n) x) ->
>            NonEmpty (fCtrlAV t n x v)
> neCtrlAV t n x v = 
>   nonEmptyLemma {A = Sigma (Ctrl t x) (\ y => SeqDecProbsCoreAssumptions.All (Viable {t = S t} n) (step t x y))}
>                 (fCtrlAV t n x v) (MkSigma y av) where
>     yav : Exists {a = Ctrl t x} (\ y => SeqDecProbsCoreAssumptions.All (Viable {t = S t} n) (step t x y))
>     yav = viableSpec1 {t = t} {n = n} x v            
>     y   : Ctrl t x
>     y   = getWitness yav
>     av  : SeqDecProbsCoreAssumptions.All (Viable {t = S t} n) (step t x y)
>     av  = getProof yav

Thus, the problem is that of implementing |fCtrlAV|. We already know that
|Ctrl t x| is finite. If we manage to show that for every |y|, |All (Viable
n) (step t x y)| is also finite, we can apply |finiteSigmaLemma| from
|SigmaProperties| and we are done. We show the result in two steps

> fAll : {t : Nat} -> {P : State t -> Type} ->
>        Finite1 P -> (mx : List (State t)) -> Finite (SeqDecProbsCoreAssumptions.All P mx)
> fAll = finiteAllLemma

and

> mutual

>   fViable : (t : Nat) -> (n : Nat) -> (x : State t) -> Finite (Viable {t} n x)
>   fViable t  n    x  = finiteSingleton

>   f1AllViable : (t : Nat) -> (n : Nat) -> (x : State t) ->
>                 Finite1 (\ y => SeqDecProbsCoreAssumptions.All (Viable {t = S t} n) (step t x y))
>   f1AllViable t n x y = fAll {t = t} {P = (Viable {t = S t} n)} (fViable (S t) n) (step t x y)

With |f1AllViable| we can finally implement |fCtrlAV|

> fCtrlAV t n x v = finiteSigmaLemma0 (fCtrl t x) (f1AllViable t n x)

and |max|, |argmax|:

> SeqDecProbsCoreAssumptions.max  {t} {n} x v =
>   Opt.max {A = Sigma (Ctrl t x) (\ y => SeqDecProbsCoreAssumptions.All (Viable {t = S t} n) (step t x y))} 
>           {B = Nat} 
>           totalPreorderNatLTE 
>           (fCtrlAV t n x v) 
>           (neCtrlAV t n x v)

> SeqDecProbsCoreAssumptions.argmax  {t} {n} x v  =
>   Opt.argmax {A = Sigma (Ctrl t x) (\ y => SeqDecProbsCoreAssumptions.All (Viable {t = S t} n) (step t x y))} 
>              {B = Nat}
>              totalPreorderNatLTE 
>              (fCtrlAV t n x v) 
>              (neCtrlAV t n x v)

> SeqDecProbsCoreAssumptions.maxSpec {n} t x v =
>   Opt.maxSpec {A = Sigma (Ctrl t x) (\ y => SeqDecProbsCoreAssumptions.All (Viable {t = S t} n) (step t x y))} 
>               {B = Nat}
>               totalPreorderNatLTE 
>               (fCtrlAV t n x v) 
>               (neCtrlAV t n x v)

> SeqDecProbsCoreAssumptions.argmaxSpec {n} t x v =
>   Opt.argmaxSpec {A = Sigma (Ctrl t x) (\ y => SeqDecProbsCoreAssumptions.All (Viable {t = S t} n) (step t x y))} 
>                  {B = Nat}
>                  totalPreorderNatLTE 
>                  (fCtrlAV t n x v) 
>                  (neCtrlAV t n x v)



* Decidability of Viable

> dViable : {t : Nat} -> (n : Nat) -> (x : State t) -> Dec (Viable {t} n x)
> dViable {t} n x = Yes ()



* The computation:

> -- showState : {t : Nat} -> State t -> String
> SeqDecProbsCoreUtils.showState {t} x = show (column {t} x)

> -- showControl : {t : Nat} -> {x : State t} -> Ctrl t x -> String
> SeqDecProbsCoreUtils.showCtrl = show

> computation : { [STDIO] } Eff ()
> computation =
>   do putStr ("enter number of steps:\n")
>      nSteps <- getNat
>      putStr ("enter initial column:\n")
>      x0 <- getLTB nColumns
>      case (dViable {t = Z} nSteps x0) of
>        (Yes v0) => do putStrLn ("computing optimal policies ...")
>                       ps   <- pure (bi Z nSteps)
>                       putStrLn ("computing optimal controls ...")
>                       mxys <- pure (stateCtrlTrj x0 () v0 ps)
>                       putStrLn (show mxys)
>                       putStrLn ("done!")                       
>        (No _)   => putStrLn ("initial column non viable for " ++ cast {from = Int} (cast nSteps) ++ " steps")

> main : IO ()
> main = run computation

> ---}

-- Local Variables:
-- idris-packages: ("effects")
-- End:
