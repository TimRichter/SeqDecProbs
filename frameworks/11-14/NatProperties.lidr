> module NatProperties


> import Decidable.Order
> import Syntax.PreorderReasoning


> import Preorder
> import TotalPreorder


> %default total


> instance Uninhabited (S n = Z) where
>   uninhabited Refl impossible


> {-
> instance Uninhabited (LTE (S n) Z) where
>   uninhabited LTEZero impossible
>   uninhabited (LTESucc x) impossible

> lteRefl : LTE n n
> lteRefl {n = Z}   = LTEZero
> lteRefl {n = S k} = LTESucc lteRefl

> ---}


EQ properties

> predInjective : (left : Nat) -> (right : Nat) -> Not (S left = S right) -> Not (left = right)
> predInjective left right contra = contra . (eqSucc left right)

> succInjective' : (left : Nat) -> (right : Nat) -> Not (left = right) -> Not (S left = S right)
> succInjective' left right contra = contra . (succInjective left right)


LT, LTE properties

> |||
> lteLemma1 : (m : Nat) -> (n : Nat) -> LTE (S m) n -> LTE m n
> lteLemma1  Z     Z             prf  = absurd prf
> lteLemma1  Z    (S n)  LTEZero        impossible
> lteLemma1  Z    (S n) (LTESucc prf) = LTEZero
> lteLemma1 (S m)  Z             prf  = absurd prf
> lteLemma1 (S m) (S n)  LTEZero        impossible
> lteLemma1 (S m) (S n) (LTESucc prf) = LTESucc (lteLemma1 m n prf)


> |||
> ltLemma1 : (m : Nat) -> (n : Nat) -> LT (S m) n -> LT m n
> ltLemma1 m n prf = lteLemma1 (S m) n prf


> ||| LT is contained in LTE
> ltInLTE : (m : Nat) -> (n : Nat) -> LT m n -> LTE m n
> ltInLTE = lteLemma1


> ||| EQ is contained in LTE
> eqInLTE : (m : Nat) -> (n : Nat) -> m = n -> m `LTE` n
> eqInLTE  Z     n    prf = LTEZero
> eqInLTE (S m)  Z    prf = absurd prf
> eqInLTE (S m) (S n) prf = LTESucc (eqInLTE m n (succInjective m n prf))


> |||
> idSuccPreservesLTE : (m : Nat) -> (n : Nat) -> m `LTE` n -> m `LTE` (S n)
> idSuccPreservesLTE  Z     n    prf = LTEZero
> idSuccPreservesLTE (S m)  Z    prf = absurd prf
> idSuccPreservesLTE (S m) (S n) prf = LTESucc (idSuccPreservesLTE m n (fromLteSucc prf))


> ||| Zero is smaller than any successor
> ltZS : (m : Nat) -> LT Z (S m)
> ltZS  Z    = LTESucc LTEZero
> ltZS (S m) = idSuccPreservesLTE (S Z) (S m) (ltZS m)


> ||| Any number is smaller than its successor
> ltIdS : (m : Nat) -> LT m (S m)
> ltIdS  Z    = LTESucc LTEZero
> ltIdS (S m) = LTESucc (ltIdS m)


> ||| Any number which is not zero is greater than zero
> notZisgtZ : {n : Nat} -> Not (n = Z) -> LT Z n
> notZisgtZ {n = Z}   contra = void (contra Refl)
> notZisgtZ {n = S m} _      = ltZS m


> ||| Any number which is greater than zero is not zero
> gtZisnotZ : {n : Nat} -> LT Z n -> Not (n = Z)
> gtZisnotZ {n = Z}   p = absurd p
> gtZisnotZ {n = S m} p = absurd


> ||| No number is less than zero
> notLTzero : {n : Nat} -> Not (LT n Z)
> notLTzero = succNotLTEzero


> |||
> strengthenLT : (m : Nat) -> (n : Nat) -> LT m (S n) -> Not (m = n) -> LT m n
> strengthenLT  Z       n  _       zNEQn   = notZisgtZ (zNEQn . sym)
> strengthenLT (S m)  Z    smLTsz  _       = void (notLTzero (fromLteSucc smLTsz))
> strengthenLT (S m) (S n) smLTssn smNEQsn = LTESucc mLTn where
>   mLTsn : LT m (S n)
>   mLTsn = fromLteSucc smLTssn
>   mNEQn : Not (m = n)
>   mNEQn = predInjective m n smNEQsn
>   mLTn : LT m n
>   mLTn = strengthenLT m n mLTsn mNEQn

> monotoneNatPlusLTE : {x : Nat} -> {y : Nat} ->
>                      (z : Nat) -> LTE x y -> LTE (z + x) (z + y)
> monotoneNatPlusLTE {x} {y}  Z    xLTEy = xLTEy
> monotoneNatPlusLTE {x} {y} (S n) xLTEy = LTESucc (monotoneNatPlusLTE {x} {y} n xLTEy)



> reflexiveLTE : (n : Nat) -> LTE n n
> reflexiveLTE n = lteRefl {n}


> transitiveLTE : (m : Nat) -> (n : Nat) -> (o : Nat) ->
>                 LTE m n -> LTE n o -> LTE m o
> transitiveLTE  Z       n     o   LTEZero                 nlteo  = LTEZero
> transitiveLTE (S m) (S n) (S o) (LTESucc mlten) (LTESucc nlteo) = LTESucc (transitiveLTE m n o mlten nlteo)


> totalLTE : (m : Nat) -> (n : Nat) -> Either (LTE m n) (LTE n m)
> totalLTE  Z    n     = Left LTEZero
> totalLTE (S m) Z     = Right LTEZero
> totalLTE (S m) (S n) with (totalLTE m n)
>   | (Left  p) = Left  (LTESucc p)
>   | (Right p) = Right (LTESucc p)



> preorderNatLTE : Preorder Nat
> preorderNatLTE =
>   MkPreorder LTE reflexiveLTE transitiveLTE


> totalPreorderNatLTE : TotalPreorder Nat
> totalPreorderNatLTE =
>   MkTotalPreorder LTE reflexiveLTE transitiveLTE totalLTE


Properties of |minus|:

> ||| The difference of equal numbers is zero
> minusLemma0 : m = n -> m - n = Z
> minusLemma0 {m = Z}    {n = Z}    Refl = Refl
> minusLemma0 {m = Z}    {n = S n'} prf  = absurd prf
> minusLemma0 {m = S m'} {n = Z}    prf  = absurd prf
> minusLemma0 {m = S m'} {n = S n'} prf  = trans s1 s2 where
>   s1 : S m' - S n' = m' - n'
>   s1 = Refl
>   s2 : m' - n' = Z
>   s2 = minusLemma0 (succInjective m' n' prf)


> |||
> minusLemma1 : n - m = S l -> l = n - (S m)
> minusLemma1 {l} {m = Z}    {n = Z}    p = absurd p
> minusLemma1 {l} {m = Z}    {n = S n'} p = s5 where
>   s1 : S n' = S l
>   s1 = p
>   s2 : l = n'
>   s2 = sym (succInjective n' l s1)
>   s3 : n' = n' - Z
>   s3 = sym (minusZeroRight n')
>   s4 : n' - Z = S n' - S Z
>   s4 = Refl
>   s5 : l = S n' - S Z
>   s5 = trans s2 (trans s3 s4)
> minusLemma1 {l} {m = S m'} {n = Z}    p = absurd p
> minusLemma1 {l} {m = S m'} {n = S n'} p = s3 where
>   s1 : n' - m' = S l
>   s1 = p
>   s2 : l = n' - (S m')
>   s2 = minusLemma1 s1
>   s3 : l = S n' - S (S m')
>   s3 = trans s2 Refl


> |||
> minusLemma2 : LTE m n -> n - m = S l -> LTE (S m) n
> minusLemma2 {m = Z}    {n = Z}    p q = absurd q
> minusLemma2 {m = Z}    {n = S n'} p q = LTESucc LTEZero
> minusLemma2 {m = S m'} {n = Z}    p q = absurd p
> minusLemma2 {m = S m'} {n = S n'} (LTESucc p') q = LTESucc (minusLemma2 p' q)


> |||
> minusLemma3 : LTE m n -> Z = n - m -> m = n
> minusLemma3 {m = Z}    {n = Z}    p q = Refl
> minusLemma3 {m = Z}    {n = S n'} p q = absurd q
> minusLemma3 {m = S m'} {n = Z}    p q = absurd p
> minusLemma3 {m = S m'} {n = S n'} (LTESucc p') q =
>   eqSucc m' n' (minusLemma3 {m = m'} {n = n'} p' q') where
>     q' : Z = n' - m'
>     q' = trans q Refl


> |||
> minusLemma4 : LTE (S m) n -> S (n - S m) = n - m
> minusLemma4 {m = Z} {n = Z}    p = absurd p
> minusLemma4 {m = Z} {n = S n'} (LTESucc p') =
>     ( S (S n' - S Z) )
>   ={ Refl }=
>     ( S (n' - Z)     )
>   ={ cong (minusZeroRight n') }=              
>     ( S n'           )
>   ={ Refl }=                
>     ( S n' - Z       )
>   QED
> minusLemma4 {m = S m'} {n = Z} p = absurd p
> minusLemma4 {m = S m'} {n = S n'} (LTESucc p') =
>     ( S (S n' - S (S m')) )
>   ={ Refl }=
>     ( S (n' - S m')       )
>   ={ minusLemma4 p' }=
>     ( n' - m'             )
>   ={ Refl }=
>     ( S n' - S m'         )
>   QED


Decidability

> ||| LTE is decidable
> decLTE : (m : Nat) -> (n : Nat) -> Dec (LTE m n)
> decLTE = lte


> ||| LT is decidable
> decLT : (m : Nat) -> (n : Nat) -> Dec (LT m n)
> decLT m n = decLTE (S m) n


Uniqueness

> ||| LTE is unique
> uniqueLTE : (p1 : LTE m n) -> (p2 : LTE m n) -> p1 = p2
> uniqueLTE  LTEZero     LTEZero    = Refl
> uniqueLTE  LTEZero    (LTESucc p) impossible
> uniqueLTE (LTESucc p)  LTEZero    impossible
> uniqueLTE (LTESucc p) (LTESucc q) = cong (uniqueLTE p q)

> ||| LT is unique
> uniqueLT : (p1 : LT m n) -> (p2 : LT m n) -> p1 = p2
> uniqueLT {m} {n} = uniqueLTE {m = S m} {n = n}
