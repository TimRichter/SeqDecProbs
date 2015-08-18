> module WFProperties

> import WellFounded

> %default total

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

> ||| the inverse image of a wellfounded relation is wellfounded
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

> ||| the transitive closure of a relation
> relTransCl : (r : a -> a -> Type) -> (a -> a -> Type)
> relTransCl r x y = Either (r x y) (z : a ** (relTransCl r x z, r z y))

example: LT on Nat is the transitive closure of { (n, S n) | n : Nat }
first the successor relation

> data succRel : Nat -> Nat -> Type where
>   mkSuccRel : (n : Nat) -> succRel n (S n)

< ltToTransSucc : {m, n : Nat} -> m `LT` n -> relTransCl succRel m n
< ltToTransSucc {m} {n} SmLTEn with (isLTE n (S m))
<     | (Yes nLTESm) = Left (mkSuccRel m)
<     | (No  SmLTn ) = ?lala


