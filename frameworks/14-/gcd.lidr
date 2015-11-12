> module gcd

> import NatDivisor
> import NatDivisorOperations
> import NatGCD
> import NatGCDOperations
> import NatGCDProperties
> import NatCoprime
> import NatCoprimeProperties
> import NatProperties2
> import Syntax.PreorderReasoning

> syntax [x] "|" [y] = Divisor x y

> %default total

use NatDivisor.Divisor instead
 IsDiv : Nat -> Nat -> Type
 IsDiv d n = Sigma Nat (\k => d * k = n)

not used
 Divisors : Nat -> Type
 Divisors n = Sigma Nat (\d => IsDiv d n)

use NatDivisorOperations.quotient instead
 divide : {d , n : Nat} -> (IsDiv d n) -> Nat
 divide (k ** _) = k

use NatDivisorProperties.quotientLemma
 divideMultId : {d, n: Nat} -> (dDivn: d `Divisor` n) -> d * (quotient n d dDivn) = n
 divideMultId ( _ ** p) = p

> coDiv : {d, n : Nat} -> (dv : (d | n)) -> ((quotient n d dv) | n)
> coDiv {d} (Evidence k pf) = Evidence d  (trans (multCommutative k d) pf)

use NatDivisorProperties.anyDivisorZ
 anyDivZero : (d : Nat) -> IsDiv d Z
 anyDivZero d = (Z ** multZeroRightZero d)

use NatDivisorProperties.oneDivisorAny
 oneDivAny : (n : Nat) -> IsDiv (S Z) n
 oneDivAny n = (n ** multOneLeftNeutral n)

use NatDivisorProperties.anyDivisorAny
 anyDivSelf : (n : Nat) -> IsDiv n n
 anyDivSelf n = ((S Z) ** (multOneRightNeutral n))

> leftFactorDivProduct : (d, e : Nat) -> d | (d * e)
> leftFactorDivProduct d e = Evidence e Refl

> rightFactorDivProduct : (d, e : Nat) -> d | (e * d)
> rightFactorDivProduct d e = Evidence e (multCommutative d e))

use NatDivisorProperties.divisorPlusLemma1 of type:
< ||| Any divisor of two numbers is a divisor of their sum
< divisorPlusLemma1 : (m : Nat) -> (n : Nat) -> (d : Nat) ->
<                     d `Divisor` m -> d `Divisor` n -> d `Divisor` (m + n)
 divSum : (d, n, m : Nat) -> IsDiv d n -> IsDiv d m -> IsDiv d (n+m)
 divSum d n m (kn ** pfn) (km ** pfm) = ((kn+km) ** pf) where
     pf : d * (kn + km) = n + m
     pf = 
     (d * (kn + km))         ={ multDistributesOverPlusRight d kn km }=
     ((d * kn) + (d * km))   ={ cong {f = \x => x + (d * km)} pfn }=
     (n + (d * km))          ={ cong {f = \x => n + x} pfm }=
     (n + m)                 QED


use NatGCD.GCD 
 IsGCD : Nat -> Nat -> Nat -> Type
 IsGCD n m d = (IsDiv d n, IsDiv d m, 
     (e : Nat) -> IsDiv e n -> IsDiv e m -> IsDiv e d) 

use NatGCDOperations.gcdDivisorFst
 divFst : {n, m, d : Nat} -> IsGCD n m d -> IsDiv d n
 divFst (dn,_,_) = dn

use NatGCDOperations.gcdDivisorSnd
 divSnd : {n, m, d : Nat} -> IsGCD n m d -> IsDiv d m
 divSnd (_,dm,_) = dm

> gcdCommutative: {n, m, d : Nat} -> GCD n m d -> GCD m n d
> gcdCommutative (MkGCD dDivn dDivm f) = 
>     MkGCD dDivm dDivn (\e => \dm => \dn => f e dn dm) 

> gcdZero : (n : Nat) -> GCD Z n n
> gcdZero n = MkGCD (anyDivisorZ n) (anyDivisorAny n) (\e => \eDz => \eDn => eDn) 

use NatCoprime.Coprime
 CoPrime : Nat -> Nat -> Type
 CoPrime n m = IsGCD n m (S Z)

cancelling by gcd yields relatively prime numbers:
needs a lot of basic stuff about addition, multiplication
and order of Nat that is not in Prelude/Nat (didn't check 
in contrib)

in NatProperties2
 shiftSucc : (m, n : Nat) -> 
             m + S n = S m + n
 shiftSucc m n =
   (m + S n)   ={ plusCommutative m (S n) }=
   (S n + m)   ={ cong {f = S} (plusCommutative n m) }=
   (S m + n)   QED

> eqSumRevSummands :  (m, k, n, l : Nat) -> 
>                     (m + k = n + l) -> 
>                     compare k l = compare n m
> eqSumRevSummands Z     Z     Z     Z     _    = Refl
> -- m + k = 0, n + l > 0 
> eqSumRevSummands Z     Z     Z     (S l) Refl impossible
> eqSumRevSummands Z     Z     (S n) l     Refl impossible
> -- m + k > 0, n + l = 0
> eqSumRevSummands Z     (S k) Z     Z     Refl impossible
> eqSumRevSummands (S m) k     Z     Z     Refl impossible
> -- m = l = 0 or k = n = 0, the others being equal 
> -- automatically
> eqSumRevSummands Z     (S k) (S n) Z     _    = Refl
> eqSumRevSummands (S m) Z     Z     (S l) _    = Refl
> -- 4 cases a little more interesting 
> eqSumRevSummands Z     (S k) Z     (S l) p    = 
>   eqSumRevSummands Z k Z l (succInjective k l p)
> eqSumRevSummands Z     (S k) (S n) (S l) p    = 
>   eqSumRevSummands Z k (S n) l p' where
>   p' : (Z + k) = (S n) + l
>   p' =
>     (Z + k)     ={ succInjective k (n + (S l)) p }=
>     (n + (S l)) ={ shiftSucc n l }=
>     ((S n) + l) QED
> eqSumRevSummands (S m) (S k) Z     (S l) p    = 
>   eqSumRevSummands (S m) k Z l p' where
>   p' : (S m) + k = Z + l
>   p' =
>     ((S m) + k)  ={sym (shiftSucc m k) }=
>     (m + (S k))  ={succInjective (m + (S k)) l p}=
>     (Z + l)      QED
> eqSumRevSummands (S m) k     (S n) l     p    = 
>  eqSumRevSummands m k n l (succInjective (m + k) (n + l) p)

> compLemma : (m, k, n, l : Nat) -> 
>             (compare m n) = (compare k l) -> 
>             (compare (m + k) (n + l)) = (compare k l)
> -- cases where one summand on each side is Z
> compLemma Z     Z     Z     Z     _ = Refl
> compLemma Z     Z     (S n) (S l) _ = Refl
> compLemma (S m) (S k) Z     Z     _ = Refl
> -- cases where (compare m n) = (compare k l) is absurd
> compLemma Z     Z     Z     (S l) Refl impossible
> compLemma Z     Z     (S n) Z     Refl impossible
> compLemma Z     (S k) Z     Z     Refl impossible
> compLemma Z     (S k) (S n) Z     Refl impossible
> compLemma (S m) Z     Z     Z     Refl impossible
> compLemma (S m) Z     Z     (S l) Refl impossible
>
> compLemma Z     (S k) Z     (S l) p = 
>   compLemma Z k Z l p
> compLemma Z     (S k) (S n) (S l) p =
>   (compare (Z + (S k)) ((S n) + (S l)))  
>   ={ cong {f = \x => compare k x} (shiftSucc n l) }=
>   (compare k ((S n) + l)) 
>   ={ compLemma Z k (S n) l p }=
>   (compare (S k) (S l))                  
>   QED
> compLemma (S m) k     (S n) l     p = 
>   compLemma m k n l p
> compLemma (S m) (S k) Z     (S l) p = 
>   (compare ((S m) + (S k)) (Z + (S l)))  
>   ={ cong {f = \x => compare x l} (shiftSucc m k) }=
>   (compare ((S m) + k) l) 
>   ={ compLemma (S m) k Z l p }=
>   (compare (S k) (S l))                  
>   QED


> compLemma2 :  (m, k, n, l : Nat) -> 
>               (compare k l) = (compare m n) -> 
>               (compare (m + k) (n + l)) = (compare m n)
> compLemma2 m k n l p = 
>   (compare (m + k) (n + l))  
>   ={ cong {f = \x => (compare x (n + l))} (plusCommutative m k) }=
>   (compare (k + m) (n + l))
>   ={ cong {f = \x => (compare (k + m) x)} (plusCommutative n l) }=
>   (compare (k + m) (l + n))
>   ={ compLemma k m l n p }=
>   (compare m n)
>   QED


> compLemma3 : (d, m, n: Nat) -> 
>       compare ((S d) * m) ((S d) * n) = compare m n
> compLemma3 Z m n =
>   (compare ((S Z) * m) ((S Z) * n)) 
>   ={ cong {f = \x => compare x ((S Z)* n)} (multOneLeftNeutral m) }=
>   (compare m ((S Z) * n))
>   ={ cong {f = \x => compare m x} (multOneLeftNeutral n) }=
>   (compare m n) 
>   QED
> compLemma3 (S d) m n = 
>   (compare ((S (S d)) * m) ((S (S d)) * n))
>   ={ Refl }=
>   (compare (m + ((S d) * m)) (n + ((S d) * n)))
>   ={ compLemma2 m ((S d) * m) n ((S d) * n) (compLemma3 d m n) }=
>   (compare m n)
>   QED


> eqImpliesEqual : (m, n : Nat) -> compare m n = EQ -> m = n
> eqImpliesEqual Z     Z     Refl = Refl
> eqImpliesEqual Z     (S n) Refl impossible
> eqImpliesEqual (S m) Z     Refl impossible
> eqImpliesEqual (S m) (S n) p    = cong (eqImpliesEqual m n p)

> equalImpliesEQ : (m, n : Nat) -> m = n -> compare m n = EQ
> equalImpliesEQ Z Z     Refl = Refl
> equalImpliesEQ Z (S n) Refl impossible
> equalImpliesEQ (S n) Z Refl impossible
> equalImpliesEQ (S n) (S m) p = equalImpliesEQ n m (succInjective n m p)


> multCancelLeft: (d, m, n: Nat) -> (S d) * m = (S d) * n -> m = n
> multCancelLeft d m n p = eqImpliesEqual m n cmpEQ where
>   cmpEQ : compare m n = EQ
>   cmpEQ =
>     (compare m n) 
>     ={ sym (compLemma3 d m n) }=
>     (compare ((S d) * m) ((S d) * n))
>     ={ equalImpliesEQ ((S d) * m) ((S d) * n) p }=
>     EQ
>     QED

> multCancelRight: (d, m, n: Nat) -> m * (S d) = n * (S d) -> m = n
> multCancelRight d m n p = multCancelLeft d m n p' where
>   p' : (S d) * m = (S d) * n
>   p' =
>     ((S d) * m)  ={ multCommutative (S d) m }=
>     (m * (S d))  ={ p }=
>     (n * (S d))  ={ multCommutative n (S d) }=
>     ((S d) * n)  QED

> multExpandLeft: (d, m, n: Nat) -> m = n -> d * m = d * n
> multExpandLeft d m n p = cong {f = \x => d * x} p

> multExpandRight: (d, m, n: Nat) -> m = n -> m * d = n * d
> multExpandRight d m n p = cong {f = \x => x * d} p


> divTrans : (d, e, n : Nat) -> IsDiv d e -> IsDiv e n -> IsDiv d n
> divTrans d e n (k ** pfdDe) (l ** pfeDn) = ((k * l) ** pfdDn) where
>   pfdDn : d * (k * l) = n
>   pfdDn = 
>     (d * (k * l))   ={ multAssociative d k l }=
>     ((d * k) * l)   ={ cong {f = \x => x * l} pfdDe }=
>     (e * l)         ={ pfeDn }=
>     n               QED

> leftFactorIsDiv : (d, e, n: Nat) -> 
>                   IsDiv (d * e) n -> 
>                   IsDiv d n
> leftFactorIsDiv d e n deDn = 
>       divTrans d (d * e) n (leftFactorDivProduct d e) deDn

> rightFactorIsDiv : (d, e, n: Nat) -> IsDiv (d * e) n -> IsDiv e n
> rightFactorIsDiv d e n deDn = 
>       divTrans e (d * e) n (rightFactorDivProduct e d) deDn

> divTower :  (d, e, n : Nat) -> 
>             (dDn : IsDiv d n) -> 
>             IsDiv e (divide dDn) -> 
>             IsDiv (d * e) n
> divTower d e n (k ** pfdDn) (l ** pfeDk) = (l ** pfdeDn) where
>   pfdeDn : (d * e) * l = n
>   pfdeDn =
>     ((d * e) * l)   ={ sym (multAssociative d e l) }=
>     (d * (e * l))   ={ cong {f = \x => d * x} pfeDk }=
>     (d * k)         ={ pfdDn }=
>     (n)             QED

> divMultLeft : (d, e, n : Nat ) ->
>               IsDiv e n ->
>               IsDiv (d * e) (d * n)
> divMultLeft d e n (k ** eDn) = (k ** deDdn) where
>   deDdn : (d * e) * k = d * n
>   deDdn =
>     ((d * e) * k)   ={ sym (multAssociative d e k) }=
>     (d * (e * k))   ={ cong {f = \x => d * x} eDn }=
>     (d * n)         QED

> divCancel : (d, e, n : Nat) -> 
>             IsDiv ((S d) * e) ((S d) * n) ->
>             IsDiv e n
> divCancel d e n (k ** sdeDsdn) = (k ** eDn) where
>   sdekIssdn : (S d) * (e * k) = (S d) * n
>   sdekIssdn =
>     ((S d) * (e * k))  ={ multAssociative (S d) e k }=
>     (((S d) * e) * k)  ={ sdeDsdn }=
>     ((S d) * n)        QED
>   eDn : e * k = n
>   eDn = multCancelLeft d (e * k) n sdekIssdn

> divCancelOne :  (d, e : Nat) ->
>                 IsDiv ((S d) * e) (S d) ->
>                 IsDiv e 1
> divCancelOne d e (k ** sdekIssd) = divCancel d e (S Z) (k ** pf) where
>   pf : ((S d) * e) * k = (S d) * (S Z)
>   pf =
>     (((S d) * e) * k)   ={ sdekIssd }=
>     (S d)               ={ sym (multOneRightNeutral (S d)) }=
>     ((S d) * 1)         QED

> makeCoPrimeLemma : {n, m, d: Nat} -> (pf: IsGCD n m (S d)) ->
>   (e : Nat) ->  IsDiv e (divide (divFst pf)) -> 
>                 IsDiv e (divide (divSnd pf)) ->
>                 IsDiv e (S Z)
> makeCoPrimeLemma {n} {m} {d} (sdDn,sdDm,f) e eDnd eDmd = 
>     divCancelOne d e sdeDsd where
>       sdeDsd : IsDiv ((S d) * e) (S d)
>       sdeDsd = f  ((S d) * e)
>                   (divTower (S d) e n sdDn eDnd)
>                   (divTower (S d) e m sdDm eDmd)


> makeCoPrime: {n, m, d : Nat} -> (pf : IsGCD n m (S d)) -> 
>               CoPrime (divide (divFst pf)) (divide (divSnd pf))
> makeCoPrime {n} {m} {d} pf = 
>    (oneDivAny (divide (divFst pf)), 
>     oneDivAny (divide (divSnd pf)), 
>     makeCoPrimeLemma pf) 

compute gcd with Euclid: 

> GCD : Nat -> Nat -> Type
> GCD m n = Sigma Nat (IsGCD m n)

 gcd : (m, n : Nat) -> GCD m n
 gcd Z n = (n ** gcdZero n)
 gcd m n with (compare m n)
 gcd m n | EQ =   


> collect : (P : Nat -> Type) -> Nat -> Type
> collect P Z = P Z
> collect P (S n) = Pair (collect P n) (P (S n))

 projColl :  (P : Nat -> Type) -> (m, n : Nat) ->
             (c : collect P n) ->
             (m `LTE` n) ->
             P m

 


 nat2Ind : (P : Nat -> Nat -> Type) -> 
           (pfLT : (r, s : Nat) -> 
                   (r `LT` s) -> P (r - s) s -> P r s) ->
           (pfGT : (r, s : Nat) ->
                   (r `GT` s) -> P r (s - r) -> P r s) ->
           (m, n : Nat) -> P m n



