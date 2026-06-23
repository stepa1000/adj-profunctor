module AdkProfunctor.BuildRun where

import Data.Profunctor
import Data.Profunctor.Monad
import Data.Prpfunctor.Adjunction

import Control.Category.Free
import Data.Profunctors.CompPF

buildCoPasTamSum :: 
   ( ProfunctorComonad w
   , Profunctor a
   , Profunctor b
   , Cochoice a) => 
   (a :-> b) ->
   w a :-> 
   ProWAdjointT CopastroSum CotambaraSum w b
buildCoPasTamSum f wa = ProWAdjointT $ proreturn $ promap (\a-> cotambaraSum f a) wa

buildCoPasTamSumId ::  
   ( ProfunctorComonad w
   , Profunctor a
   , Cochoice a) => 
   w a :-> 
   ProWAdjointT CopastroSum CotambaraSum w a
buildCoPasTamSumId = buildCoPasTam id

runCoPasTamSum :: ( ProfunctorMonad m
   , Profunctor a
   , Profunctor r
   , Cochoice r) => 
   (forall x y. a x y -> r x y) -> 
   ProMAdjointT CopastroSum CotambaraSum m a :-> 
   m r
runCoPasTamSum f (ProMAdjointT pma) = promap (\ (CopastroSum rcs) -> rcs f) $ proextract pma

buildPasTamSum ::  
   ( ProfunctorComonad w
   , Profunctor a
   , Profunctor b
   , Choice a) =>
   (a :-> b) ->
   w a :->
   ProWAdjointT PastroSum TambaraSum w b
buildPasTamSum f wa = ProWAdjointT $ proreturn $ promap (\a-> tambaraSum f a) wa

runPasTamSum :: ( ProfunctorMonad m
   , Profunctor a
   , Profunctor r
   , Choice r) => 
   (forall x y. a x y -> r x y) ->
   ProMAdjointT PastroSum TambaraSum m a :-> 
   m r
runPasTamSum f (ProMAdjointT pma) = promap (\ (PastroSum fy a fx) -> dimap fx fy (left' $ f a) ) $ proextract pma

buildEnvClo ::  
   ( ProfunctorComonad w
   , Profunctor a
   , Profunctor b
   , Closed a) =>
   (a :-> b) ->
   w a :->
   ProWAdjointT Environment Closure w b
buildEnvClo f wa = ProWAdjointT $ proreturn $ promap (\a-> close f a) wa

runEnvClo :: ( ProfunctorMonad m
   , Profunctor a
   , Profunctor r
   , Closed r) => 
   (forall x y. a x y -> r x y) ->
   ProMAdjointT Environment Closure m a :-> 
   m r
runEnvClo f (ProMAdjointT pma) = promap (\ (Environment fy a fx) -> dimap fx fy (closed $ f a) ) $ proextract pma

buildCoPasTam ::  
   ( ProfunctorComonad w
   , Profunctor a
   , Profunctor b
   , Costrang a) =>
   (a :-> b) ->
   w a :->
   ProWAdjointT Copastro Cotambara w b
buildCoPasTam f wa = ProWAdjointT $ proreturn $ promap (\a-> cotambara f a) wa

runCoPasTam :: ( ProfunctorMonad m
   , Profunctor a
   , Profunctor r
   , Costrong r) => 
   (forall x y. a x y -> r x y) ->
   ProMAdjointT Copastro Cotambara m a :-> 
   m r
runCoPasTam f (ProMAdjointT pma) = promap (\ (Copastro a) -> f a) $ proextract pma

buildPasTam ::  
   ( ProfunctorComonad w
   , Profunctor a
   , Profunctor b
   , Strang a) =>
   (a :-> b) ->
   w a :->
   ProWAdjointT Pastro Tambara w b
buildPasTam f wa = ProWAdjointT $ proreturn $ promap (\a-> tambara f a) wa

runPasTam :: ( ProfunctorMonad m
   , Profunctor a
   , Profunctor r
   , Strong r) => 
   (forall x y. a x y -> r x y) ->
   ProMAdjointT Pastro Tambara m a :-> 
   m r
runPasTam f (ProMAdjointT pma) = promap (\ (Pastro fy a fx) -> dimap fx fy (first' $ f a) ) $ proextract pma

buildCatRif ::  
   ( ProfunctorComonad w
   , Profunctor a
   , Category p) =>
   (p :-> a) ->
   w b :->
   ProWAdjointT (Procompose p) (Rift p) w a
buildCatRif f wa = ProWAdjointT $ proreturn $ promap (\a-> Rift f) wa

runCatRif :: ( ProfunctorMonad m
   , Profunctor a
   , Profunctor r
   , Category p) => 
   (forall x y. a x y -> p x y) ->
   ProMAdjointT (Procompose p) (Rift p) m a :-> 
   m p
runCatRif f (ProMAdjointT pma) = promap (\ (Procompose fy fx) -> (fy . f fx) ) fx) $ proextract pma

{-
data ProAdjW p w a x y
   = PAWTCPTS (ProWAdjointT CopastroSum CotambaraSum w a x y)
   | PAWTPTS (ProWAdjointT PastroSum TambaraSum w a x y)
   | PAWTEC (ProWAdjointT Environment Closure w a x y)
   | PAWTCPT (ProWAdjointT Copastro Cotambara w a x y) 
   | PAWTPT (ProWAdjointT Pastro Tambara w a x y)
   | PAWTCR (ProWAdjointT (Procompose p) (Rift p) w a x y)
   
type CatProAdjW w a x y = Queue (ProAdjW (CatProAdjW w a) w a)

data ProAdjM p m a x y
   = PAMTCPTS (ProMAdjointT CopastroSum CotambaraSum m a x y)
   | PAMTPTS (ProMAdjointT PastroSum TambaraSum m a x y)
   | PAMTEC (ProMAdjointT Environment Closure m a x y)
   | PAMTCPT (ProMAdjointT Copastro Cotambara m a x y) 
   | PAMTPT (ProMAdjointT Pastro Tambara m a x y)
   | PAMTCR (ProMAdjointT (Procompose p) (Rift p) m a x y)

type CatProAdjM m a x y = Queue (ProAdjM (CatProAdjM m a) m a)
-}
{-
data ProAdj (a :: ProAdj) -- p
   = CoPasTamSun
   | PasTamSum
   | EnvCLo
   | CoPasTam
   | PasTam
   | CatRif (Peoxy (a :: ProAdj)) -- (Proxy p) -- (Proxy (a :: ProAdj))

data ProBuild p (a :: ProAdj p) w a where
   ProCat :: 
      ProWAdjointT 
         (Procompose 
	    (ProBuild p (a :: ProAdj a2) w)) 
	 (Rift 
	    (ProBuild p (a :: ProAdj a2) w)) 
	 (ProWAdjointT 
	    (Procompose 
	       (ProBuild p (a :: ProAdj a2) w)) 
	    (Rift 
	       (ProBuild p (a :: ProAdj a2) w)) 
	    ) a -> 
	 ProBuild p (CatRif a) w a
-}


