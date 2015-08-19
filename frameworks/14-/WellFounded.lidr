> module WellFounded

> %default total

goal is to define wellfounded relations, ~ induction, recursion,
the most important examples of wf relations (at least LT on Nat) and
some methods to build wf relations from others (see "Paulson - 1986 - 
Constructing Recursion Operators in Intuitionistic Type Theory" and
https://github.com/agda/agda-stdlib/blob/master/src/Induction/WellFounded.agda)

contrib/Control/WellFounded.lidr defines a type class wellFounded and
proves wf induction and recursion. No examples nor construction methods
for wf relations are given. Since I don't even know how to write
down a wellFounded-instance declaration for e.g. the inverse image of a
wf relation under some map, I'll start from the beginning without type classes.

> ||| Accessibility: some element `x` is accessible if all `y` such that
> ||| `rel y x` are themselves accessible.
> |||
> ||| @ a the type of elements
> ||| @ rel a relation on a
> ||| @ x the acessible element
> data Accessible : (rel : a -> a -> Type) -> (x : a) -> Type where
>   ||| Accessibility
>   |||
>   ||| @ x the accessible element
>   ||| @ acc' a demonstration that all smaller elements are also accessible
>   Access : (acc' : (y : a) -> rel y x -> Accessible rel y) ->
>            Accessible rel x
> 

> ||| A relation `rel` on `a` is well-founded if all elements of `a` are
> ||| acessible.
> |||
> ||| @ rel the well-founded relation
> data WF : (rel: a -> a -> Type) -> Type where
>   mkWF : {rel: a -> a -> Type} -> 
>          ((x : a) -> Accessible rel x) -> WF rel
 
> ||| A recursor over accessibility.
> |||
> ||| This allows us to recurse over the subset of some type that is
> ||| accessible according to some relation.
> |||
> ||| @ rel the well-founded relation
> ||| @ step how to take steps on reducing arguments
> ||| @ z the starting point
> accRec : {rel : a -> a -> Type} ->
>          (step : (x : a) -> ((y : a) -> rel y x -> b) -> b) ->
>          (z : a) -> Accessible rel z -> b
> accRec step z (Access f) =
>   step z $ \y, lt => accRec step y (f y lt)
> 
> ||| An induction principle for accessibility.
> |||
> ||| This allows us to recurse over the subset of some type that is
> ||| accessible according to some relation, producing a dependent type
> ||| as a result.
> |||
> ||| @ rel the well-founded relation
> ||| @ step how to take steps on reducing arguments
> ||| @ z the starting point
> accInd : {rel : a -> a -> Type} -> {P : a -> Type} ->
>          (step : (x : a) -> ((y : a) -> rel y x -> P y) -> P x) ->
>          (z : a) -> Accessible rel z -> P z
> accInd step z (Access f) =
>   step z $ \y, lt => accInd step y (f y lt)
> 
>
> ||| Use well-foundedness of a relation to write terminating operations.
> |||
> ||| @ rel a well-founded relation
> wfRec : {rel: a -> a -> Type} -> WF rel ->
>         (step : (x : a) -> ((y : a) -> rel y x -> b) -> b) ->
>         a -> b
> wfRec {rel} (mkWF wf) step x = accRec step x (wf x)
> 
> 
> ||| Use well-foundedness of a relation to write proofs
> |||
> ||| @ rel a well-founded relation
> ||| @ P the motive for the induction
> ||| @ step the induction step: take an element and its accessibility,
> |||        and give back a demonstration of P for that element,
> |||        potentially using accessibility
> wfInd : {rel: a -> a -> Type} -> {P : a -> Type} -> WF rel ->
>         (step : (x : a) -> ((y : a) -> rel y x -> P y) -> P x) ->
>         (x : a) -> P x
> wfInd {rel} (mkWF wf) step x = accInd step x (wf x)
> 

> ||| Successor relation on natural numbers
> data succRel : Nat -> Nat -> Type where
>   succZ : succRel Z (S Z)
>   succS : {m, n : Nat} -> succRel m n -> succRel (S m) (S n)

> ||| Successor relation is wellfounded
> ||| Of course we'll always use pattern matching
> ||| in place of the resp. wf recursion/induction,
> ||| so this is just for completeness...
> ||| 
> ||| can we avoid "assert_total" ?
> succRelWF : WF succRel
> succRelWF = mkWF wf where
>   stepZ : (m : Nat) -> succRel m Z -> Accessible succRel m
>   stepZ _ succZ impossible
>   stepZ _ (succS _) impossible
>   stepS : (n, m : Nat) -> succRel m (S n) -> Accessible succRel m
>   stepS _ _ succZ = Access stepZ
>   stepS _ Z     (succS _) impossible
>   stepS _ (S m) (succS _) = Access (assert_total (stepS m))
>   wf : (n : Nat) -> Accessible succRel n
>   wf Z = Access stepZ
>   wf (S n) = Access (stepS n)

> ||| LT on Nat is wellfounded
> ||| lemmata (should go somewhere else)

> lteAntisym : {m, n: Nat} -> ( m `LTE` n) -> (n `LTE` m) -> m = n
> lteAntisym LTEZero LTEZero = Refl
> lteAntisym (LTESucc mLTEn) (LTESucc nLTEm) = cong (lteAntisym mLTEn nLTEm)

> notLTEswapLT : {m, n: Nat} -> Not ( m `LTE` n) -> n `LT` m
> notLTEswapLT {m=Z}       notZLTEn = void (notZLTEn LTEZero)
> notLTEswapLT {m=(S m')} {n=Z} _   = LTESucc LTEZero 
> notLTEswapLT {m=(S m')} {n=(S n')} notSm'LTESn' = 
>     LTESucc (notLTEswapLT {m=m'} {n=n'} (notSm'LTESn' . LTESucc))

> splitLTE : {m, n : Nat} -> m `LTE` n ->
>           Either (m = n) (m `LT` n)
> splitLTE {m} {n} mLTEn with (isLTE n m)
>   | (Yes nLTEm)   = Left (lteAntisym mLTEn nLTEm)
>   | (No notnLTEm) = Right (notLTEswapLT notnLTEm)

> splitLT : {m, n : Nat} -> m `LT` n -> Either (S m = n) ((S m) `LT` n)
> splitLT = splitLTE

> ||| for any m, all n smaller m are LT-accessible 
> accLT : (m : Nat) -> (n : Nat) -> n `LT` m -> Accessible LT n
> accLT Z n LTEZero impossible
> accLT Z n (LTESucc _) impossible
> accLT (S m) n nLTSm with (splitLT nLTSm) 
>   | (Left SnIsSm) = Access acc where
>     nIsm : n = m
>     nIsm = succInjective n m SnIsSm
>     acc : (y : Nat) -> y `LT` n -> Accessible LT y
>     acc y yLTn = accLT m y (replace nIsm yLTn)
>   | (Right LTEZero) impossible
>   | (Right (LTESucc nLTm)) = accLT m n nLTm

> ||| LT is wellfounded
> ltWF : WF LT
> ltWF = mkWF wf where
>   wf : (m : Nat) -> Accessible LT m
>   wf m = Access (accLT m)


> ||| inverse image of a relation wrt some map
> ||| @ f the map
> ||| @ r the relation on the target of f
> relInvIm : (f : a -> b) -> (r : b -> b -> Type) -> (a -> a -> Type)
> relInvIm f r x y = r (f x) (f y)

> ||| if `f x` is accessible for r, x is accessible for the inverse image of r
> ||| 
> ||| @ f the map
> ||| @ r the relation
> ||| @ x the element
> relInvImAcc : {f : a -> b} -> {r : b -> b -> Type} ->
>               (x : a) -> Accessible r (f x) -> 
>               Accessible (relInvIm f r) x
> relInvImAcc {f} {r} x (Access stepfx) = 
>                   Access (\ y => \ pf => relInvImAcc y (stepfx (f y) pf)) 

> ||| inverse image of a wellfounded relation is wellfounded
> ||| 
> ||| @ f a map a -> b
> ||| @ r the wellfounded relation on b
> relInvImWF : {f : a -> b} -> {r : b -> b -> Type} ->
>              WF r -> WF (relInvIm f r)
> relInvImWF {f} {r} (mkWF wfr) = mkWF wfrInv where
>   wfrInv : (x : a) -> Accessible (relInvIm f r) x
>   wfrInv x = relInvImAcc x (wfr (f x))


> ||| Accessibility for subrelations
> |||  the idea is that each (inj x y) would be injective
> |||  but it works for any map ... in case r1 is a
> |||  (family of) mere propositions injectivity 
> |||  is automatic anyway
>
> relSubAcc : {r1, r2 : a -> a -> Type} -> 
>     (inj : {x, y : a} -> r1 x y -> r2 x y) ->
>     (z : a) -> Accessible r2 z -> Accessible r1 z
> relSubAcc inj z (Access stepr1) =
>       Access (\ w => \ pf => relSubAcc inj w (stepr1 w (inj pf)))

> ||| any subrelation of a wellfounded relation is wellfounded
> |||
> relSubWF : {r1, r2 : a -> a -> Type} ->
>     (inj : {x, y : a} -> r1 x y -> r2 x y) ->
>     WF r2 -> WF r1
> relSubWF inj (mkWF wfr2) = mkWF wfr1 where
>   wfr1 : (z : a) -> Accessible r1 z
>   wfr1 z = relSubAcc inj z (wfr2 z)


 transitive closure ??



