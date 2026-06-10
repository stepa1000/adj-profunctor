module AdjProfunctor where

import Data.Profunctor
import Data.Profunctor.Monad
import Data.Prpfunctor.Adjunction
import Data.Distributive

leftAdjunct ::
	( ProfunctorAdjunction f u
	, Profunctor p
	, Profunctor q) =>
	(f p :-> q) -> (p :-> u q) 
leftAdjunct f = promap f . unit

rightAdjunct :: 
	( ProfunctorAdjunction f u
	, Profunctor p
	, Profunctor q) =>
	(p :-> u q) -> (f p :-> q)
rightAdjunct f = counit . promap f

adjuncted :: 
	( ProfunctotAdjunction f u
	, Profunctor p, Profunctor d
	, Profunctor b, Functor g
	, Profunctor c, Profunctor s) =>
	p (d :-> u b) (g (c :-> u s)) ->
	p (f d :-> b) (g (f c :-> s))
adjuncted = bimap leftAdjunct (promap rightAdjunct)

tabulateAdjunction :: 
	( ProfunctorAdjunction f u
	, Profunctor p) =>
	(f (Forget ()) :-> p) -> u p
tabulateAdjunction f = 
	leftAdjunct f (Forget $ const ()) 

indexAdjunction :: 	
	( ProfunctorAdjunction f u
	, Profunctor p
	, Profunctor q ) =>
	u p -> f q -> p
indexAdjunction = rightAdjunct . const

zapWithAdjunction :: 
	( ProfunctorAdjunction f u
	, Profunctor a
	, Profunctor b
	, Profunctor c ) =>
	(a :-> (b :-> c)) -> u a -> f b -> c
zapWithAdjunction f ua = rightAdjunct 
	(\b-> promap (\a-> f a b) ua)

data ProMAdjointT f g m a x y = ProMAdjointT 
	{runProMAdjointT ::  
		( ProfunctorFunctor f
		, ProfunctorFunctor g
		, ProfunctorFunctor m
		, Profunctor a) =>
		g (m ( f a)) x y
		}

pmatMapG :: ( ProfunctorFunctor f
		, ProfunctorFunctor g
		, ProfunctorFunctor m
		, Profunctor a) =>
   (forall q. Profunctor q => g q x1 y1 -> g2 q x2 y2) -> 
   ProMAdjointT f g m a x1 y1 -> 
   ProMAdjointT f g2 m a x2 y2
pmatMapG t (ProMAdjointT gmfa) = ProMAdjointT $ t gmfa

pmatMapM :: ( ProfunctorFunctor f
		, ProfunctorFunctor g
		, ProfunctorFunctor m
		, Profunctor a) =>
   (forall q. Profunctor q => m q x1 y1 -> m2 q x2 y2) -> 
   ProMAdjointT f g m a x1 y1 -> 
   ProMAdjointT f g m2 a x2 y2
pmatMapM t (ProMAdjointT gmfa) = ProMAdjointT $ promap t gmfa

pmatMapF :: ( ProfunctorFunctor f
		, ProfunctorFunctor g
		, ProfunctorFunctor m
		, Profunctor a) =>
   (forall q. Profunctor q => f q x1 y1 -> f2 q x2 y2) -> 
   ProMAdjointT f g m a x1 y1 -> 
   ProMAdjointT f2 g m a x2 y2
pmatMapF t (ProMAdjointT gmfa) = ProMAdjointT $ promap (promap t) gmfa

instance ( ProfunctorFunctor f
	 , ProfunctorFunctor g
	 , ProfunctorFunctor m
	 ) => ProfunctorFunctor
	 	(ProMAdjointT f g m) where
	promap q (ProMAdjointT gmfa) =
		ProMAdjointT $ 
		promap (promap (promap q)) gmfa

--ProMAdjointT m >>>= f = ProMAdjointT $ profmap (>>= rightAdjunct (runAdjointT . f)) m

instance ( ProfunctorFunctor f
	 , ProfunctorFunctor g
	 , ProfunctorFunctor m
	 , ProfunctorMonad m 
	 , ProfunctorAdjunction f u
	 ) => ProfunctorMonad (ProMAdjointT f g m) where
  proreturn = ProMAdjointT $ leftAdjunct proreturn 
  projoint (ProMAdjointT gmfgmfa) = promap (projoint . promap (counit . promap (runProMAdjointT) )) gmfgmfa 

(>>>=) :: ( ProfunctorFunctor f
	 , ProfunctorFunctor g
	 , ProfunctorFunctor m
	 , ProfunctorMonad m
	 ) => ProMAdjointT f g m a -> (a :-> ProMAdjointT f g m b) -> ProMAdjointT f g m b 
m >>>= f = projoint $ promap f m

data ProWAdjointT f g w a x y = ProWAdjointT 
	{runProWAdjointT ::
		( ProfunctorFunctor f
		, ProfunctorFunctor g
		, ProfunctorFunctor w
		, Profunctor a) => 
		f (w (g a)) x y
	}

pwatMapG :: ( ProfunctorFunctor f
		, ProfunctorFunctor g
		, ProfunctorFunctor w
		, Profunctor a) =>
   (forall q. Profunctor q => g q x1 y1 -> g2 q x2 y2) -> 
   ProWAdjointT f g w a x1 y1 -> 
   ProWAdjointT f g2 w a x2 y2
pwatMapG t (ProMAdjointT gmfa) = ProMAdjointT $ promap (promap t) gmfa
 
pwatMapM :: ( ProfunctorFunctor f
		, ProfunctorFunctor g
		, ProfunctorFunctor w
		, Profunctor a) =>
   (forall q. Profunctor q => w q x1 y1 -> w2 q x2 y2) -> 
   ProWAdjointT f g w a x1 y1 -> 
   ProWAdjointT f g w2 a x2 y2
pwatMapM t (ProMAdjointT gmfa) = ProMAdjointT $ promap t gmfa

pwatMapF :: ( ProfunctorFunctor f
		, ProfunctorFunctor g
		, ProfunctorFunctor w
		, Profunctor a) =>
   (forall q. Profunctor q => f q x1 y1 -> f2 q x2 y2) -> 
   ProWAdjointT f g w a x1 y1 -> 
   ProWAdjointT f2 g w a x2 y2
pwatMapF t (ProMAdjointT gmfa) = ProMAdjointT $  gmfa

instance ( ProfunctorFunctor f
	 , ProfunctorFunctor g
	 , ProfunctorFunctor w
	 ) => ProfunctorFunctor
	 	(ProWAdjointT f g w) where
	promap q (ProWAdjointT gwfa) =
		ProMAdjointT $ 
		promap (promap (promap q)) gwfa

instance ( ProfunctorFunctor f
	 , ProfunctorFunctor g
	 , ProfunctorFunctor w
	 , ProfunctorComonad w
	 , ProfunctorAdjunction f u
	 ) => ProfunctorComonad (ProWAdjointT f g w) where
	proextract = rightAdjunct proextract . runProWAdjointT
	produplicate = proextend id

proextend :: (ProfunctorComonad w, Profunctor a, Profunctor b) => (w a :-> b) -> (w a :-> w b)
proextend f (ProWAdjointT m) = ProWAdjointT $ profmap (proextend $ leftAdjunct (f . ProWAdjointT)) m

spawnWAdj :: (ProfunctorComonad w, ProfunctorAdjunction f g) => w a :-> u (ProWAdjointT f g w (f a))
spawnWAdj wa = promap ProWAdjointT $ promap (promap (promap unit)) $ unit wa
--                u (f (w (u (f (a)))))          u (f (w a))

prolower :: (ProfunctorComonad w, ProfunctorAdjunction f g) => ProWAdjointT f g w a :-> w a
prolower (ProWAdjointT m) = counit $ promap ((\t-> t undefined). leftAdjunct . distribute . promap (rightAdjunct . (\g -> const g))) m

data ProIdT p a b = ProIdT (p a b)

instance Profunctor p => Profunctor (ProIdT p) where
   dimap f g (ProIdT p) = ProIdT $ dimap f g p

instance ProfunctorFunctor ProIdT where
   promap f (ProIdT p) = ProIdT $ f p

-- composeAdjW :: (ProfunctorComonad w1, ProfunctorComonad w2, ProfunctorAdjunction f u, Profunctor a, Profunctor b) => 
-- 	ProWAdjointT f g w1 a -> ProWAdjointT f g w2 b -> ProWAdjointT () () ProIdT ()

{-
composeAdjW :: (ProfunctorComonad w, ProfunctorAdjunction f u, Profunctor a, Profunctor b, ProfunctorAdjunction f2 u2) => 
	(Product 
		(ProWAdjointT f g w a) 
		(ProWAdjointT f2 g2 w b)) :-> 
	ProWAdjointT 
		(Procompose (ProWAdjointT f2 g2 w)) 
		(Rift (ProWAdjointT f2 g2 w)) 
		(ProWAdjointT f g w) 
		(Product a b)
composeAdjW (Pair pw1 pw2) = ProWAdjointT $ Procompose pw2 $ 
	promap (\a-> Rift (\npw2-> )) pw1

-}

spawnWAdjCompose ::(ProfunctorComonad w, ProfunctorAdjunction f u, Profunctor a, ProfunctorAdjunction f2 u2) => 
	(ProWAdjointT f g w a) :->
	Rift (ProWAdjointT f2 g2 w) (ProWAdjointT 
 		(Procompose (ProWAdjointT f2 g2 w)) 
		(Rift (ProWAdjointT f2 g2 w)) 
		(ProWAdjointT f g w) 
		(Procompose (ProWAdjointT f2 g2 w) a))
spawnWAdjCompose = spawnWAdj
{-
(ProWAdjointT f g w a) :->
	Rift (ProWAdjointT f2 g2 w) (ProWAdjointT 
 		(Procompose (ProWAdjointT f2 g2 w)) 
		(Rift (ProWAdjointT f2 g2 w)) 
		(ProWAdjointT f g w) 
		(Procompose (ProWAdjointT f2 g2 w) a))

(ProWAdjointT (Procompose (ProWAdjointT f2 g2 w)) = f
		(Rift (ProWAdjointT f2 g2 w)) = g
		(ProWAdjointT f g w) = w
		(Procompose (ProWAdjointT f2 g2 w) a) = a
		) :->
	Rift ((ProWAdjointT 
 		(Procompose (ProWAdjointT f g w)) 
		(Rift (ProWAdjointT f g w)) 
		(ProWAdjointT f g w) 
		(Procompose (ProWAdjointT f g w) a)) 
			(ProWAdjointT 
 			(Procompose (ProWAdjointT f g w)) 
			(Rift (ProWAdjointT f g w)) 
			(ProWAdjointT f g w) 
			(Procompose (ProWAdjointT f g w) a))


-}

{-
data CompProWAdj f g w a 
	= CPWALeaf (ProWAdjointT f g w a)
	| CPWANode (ProWAdjointT 
 		(Procompose (CompProWAdj f g w)) 
		(Rift (CompProWAdj f g w)) 
	        (CompProWAdj f g w)	
		(Procompose (CompProWAdj f g w) a))

spawnWAdjComposeRec ::(ProfunctorComonad w, ProfunctorAdjunction f u, Profunctor a) => 
	(ProWAdjointT f g w a) :->
	Rift (ProWAdjointT f g w) (ProWAdjointT 
 		(Procompose (ProWAdjointT f g w)) 
		(Rift (ProWAdjointT f g w)) 
		(ProWAdjointT f g w) 
		(Procompose (ProWAdjointT f g w) a))
spawnWAdjComposeRec = spawnWAdj
-}

liftMAdj :: (ProfunctorMonad m, ProfunctorAdjunction f u) => m a :-> ProMAdjointT f g m a 
liftMAdj ma = promap (\ mfu -> mfu >>>= (\fu-> ma >>>= (\a-> proreturn $ promap (\_->a) fu))) $ runProMAdjointT $ proreturn undefined

liftMAdjCompose :: (ProfunctorMonad m, ProfunctorAdjunction f u, ProfunctorAdjunction f2 u2) => 
	ProMAdjointT f g m a :-> ProMAdjointT (Procompose f2) (Rift g2) (ProMAdjointT f g m) a 
liftMAdjCompose = liftMAdj 
