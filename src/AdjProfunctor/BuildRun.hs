module AdkProfunctor.BuildRun where

import Data.Profunctor
import Data.Profunctor.Monad
import Data.Prpfunctor.Adjunction

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
   ProMAdjointT CopastroSum CotambaraSum m a :-> 
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




