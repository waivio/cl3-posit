{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fno-warn-type-defaults #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

{-# LANGUAGE DataKinds #-}

#if __GLASGOW_HASKELL__ == 810
-- Work around to fix GHC Issue #15304, issue popped up again in GHC 8.10, it should be fixed in GHC 8.12
-- This code is meant to reproduce MR 2608 for GHC 8.10
{-# OPTIONS_GHC -funfolding-keeness-factor=1 -funfolding-use-threshold=80 #-}
#endif

-------------------------------------------------------------------
-- |
-- Copyright   :  (c) 2017-2020 Nathan Waivio
-- License     :  BSD3
-- Maintainer  :  Nathan Waivio <nathan.waivio@gmail.com>
-- 
-- A program to test Algebra.Geometric.Cl3
-- The code runs tests on some standard test input and then
-- runs quckcheck for some trig identities.
-- 
-------------------------------------------------------------------

module Main (main) where

import Posit.Cl3

import Posit.Internal.PositC
import Control.Monad (replicateM)

import System.Random (randomRIO)
import Data.List (foldl1')

import Control.Concurrent (forkFinally,newEmptyMVar,putMVar,tryTakeMVar,MVar)
import Data.Maybe (catMaybes)

import Data.Time.Clock (getCurrentTime)

------------------------------------------------------------------
-- |
-- This program verifies the approximate equality of various trig
-- identities to the with the following limitations:
-- 
-- * The magnitude of the cliffor is limited in some cases.
--
-- * The imaginary part of the eigenvalues are unwrapped, due to the cyclical nature of some of the results, in a few cases.
--
-- * The poles of the functions are excluded.
--
-- * The poles of the derivatives of the functions are excluded when the cliffor is has a nilpotent component.
--
-- * Approximate equivalence is tested due to limitations with respect to floating point math.
--
-- 
-- The following properties are verified in this module:
--
-- * log.exp Identity
--
-- * exp.log Identity
--
-- * abs*signum law
--
-- * The definition of recip
--
-- * recip.recip Identity
--
-- * sin.asin Identity
--
-- * asin.sin Identity
--
-- * cos.acos Identity
--
-- * acos.cos Identity
--
-- * sinh.asinh Identity
--
-- * asinh.sinh Identity
--
-- * cosh.acosh Identity
--
-- * acosh.cosh Identity
--
-- * Double Sin Identity
--
-- * Double Cos Identity
--
-- * Double Tan Identity
--
-- * Double Sinh Identity
--
-- * Double Cosh Identity
--
-- * Double Tanh Identity
--
-- * Positive Sin Shift Identity
--
-- * Negative Sin Shift Identity
--
-- * sin^2+cos^2 Identity
--
-- * cosh^2-sinh^2 Identity
--
-- * Symmetry of Cosh
--
-- * Symmetry of Sinh
--
-- * Double I Sin
--
-- * Composition Algebra Tests
--
-------------------------------------------------------------------


main :: IO ()
main = do
  print "Start:"
  print =<< getCurrentTime
  inputValsCl3P256 :: [Cl3P256] <- listRandCliffs
  let inputValsCl3Posit256 = convert <$> inputValsCl3P256 :: [Cl3Posit256]
      inputValsCl3P128 = convert <$> inputValsCl3P256 :: [Cl3P128]
      inputValsCl3Posit128 = convert <$> inputValsCl3P256 :: [Cl3Posit128]
      inputValsCl3P64 = convert <$> inputValsCl3P256 :: [Cl3P64]
      inputValsCl3Posit64 = convert <$> inputValsCl3P256 :: [Cl3Posit64]
      inputValsCl3P32 = convert <$> inputValsCl3P256 :: [Cl3P32]
      inputValsCl3Posit32 = convert <$> inputValsCl3P256 :: [Cl3Posit32]
      inputValsCl3P16 = convert <$> inputValsCl3P256 :: [Cl3P16]
      inputValsCl3Posit16 = convert <$> inputValsCl3P256 :: [Cl3Posit16]
      inputValsCl3P8 = convert <$> inputValsCl3P256 :: [Cl3P8]
      inputValsCl3Posit8 = convert <$> inputValsCl3P256 :: [Cl3Posit8]
  mvar1 <- newEmptyMVar
  mvar2 <- newEmptyMVar
  mvar3 <- newEmptyMVar
  mvar4 <- newEmptyMVar
  mvar5 <- newEmptyMVar
  mvar6 <- newEmptyMVar
  mvar7 <- newEmptyMVar
  mvar8 <- newEmptyMVar
  mvar9 <- newEmptyMVar
  mvar10 <- newEmptyMVar
  mvar11 <- newEmptyMVar
  mvar12 <- newEmptyMVar
  forkFinally (p256 inputValsCl3P256) (\_ -> printDone mvar1 "Cl3P256")
  forkFinally (posit256 inputValsCl3Posit256) (\_ -> printDone mvar2 "Cl3Posit256")
  forkFinally (p128 inputValsCl3P128) (\_ -> printDone mvar3 "Cl3P128")
  forkFinally (posit128 inputValsCl3Posit128) (\_ -> printDone mvar4 "Cl3Posit128")
  forkFinally (p64 inputValsCl3P64) (\_ -> printDone mvar5 "Cl3P64")
  forkFinally (posit64 inputValsCl3Posit64) (\_ -> printDone mvar6 "Cl3Posit64")
  forkFinally (p32 inputValsCl3P32) (\_ -> printDone mvar7 "Cl3P32")
  forkFinally (posit32 inputValsCl3Posit32) (\_ -> printDone mvar8 "Cl3Posit32")
  forkFinally (p16 inputValsCl3P16) (\_ -> printDone mvar9 "Cl3P16")
  forkFinally (posit16 inputValsCl3Posit16) (\_ -> printDone mvar10 "Cl3Posit16")
  forkFinally (p8 inputValsCl3P8) (\_ -> printDone mvar11 "Cl3P8")
  forkFinally (posit8 inputValsCl3Posit8) (\_ -> printDone mvar12 "Cl3Posit8")
  checkToSeeIfDone [mvar1,mvar2,mvar3,mvar4,mvar5,mvar6,mvar7,mvar8,mvar9,mvar10,mvar11,mvar12]
--

checkToSeeIfDone :: [MVar ()] -> IO ()
checkToSeeIfDone [] = return ()
checkToSeeIfDone mvars = do
  listMaybeMVars <- mapM filtDone mvars
  checkToSeeIfDone (catMaybes listMaybeMVars)


filtDone :: MVar () -> IO (Maybe (MVar ()))
filtDone mvar = do
  r <- tryTakeMVar mvar
  case r of
    Nothing -> return $ Just mvar
    Just _ -> return $ Nothing

printDone mvar str = do
  t <- getCurrentTime
  putStrLn $ "Completed " ++ str ++ " at: " ++ show t
  putMVar mvar ()



p256 :: [Cl3P256] -> IO ()
p256 input = print $ "Max Error P256: " ++ (show $ filtMax (compute input props))

posit256 :: [Cl3Posit256] -> IO ()
posit256 input = print $ "Max Error Posit256: " ++ (show $ filtMax (compute input props))

p128 :: [Cl3P128] -> IO ()
p128 input = print $ "Max Error P128: " ++ (show $ filtMax (compute input props))

posit128 :: [Cl3Posit128] -> IO ()
posit128 input = print $ "Max Error Posit128: " ++ (show $ filtMax (compute input props))

p64 :: [Cl3P64] -> IO ()
p64 input = print $ "Max Error P64: " ++ (show $ filtMax (compute input props))

posit64 :: [Cl3Posit64] -> IO ()
posit64 input = print $ "Max Error Posit64: " ++ (show $ filtMax (compute input props))

p32 :: [Cl3P32] -> IO ()
p32 input = print $ "Max Error P32: " ++ (show $ filtMax (compute input props))

posit32 :: [Cl3Posit32] -> IO ()
posit32 input = print $ "Max Error Posit32: " ++ (show $ filtMax (compute input props))

p16 :: [Cl3P16] -> IO ()
p16 input = print $ "Max Error P16: " ++ (show $ filtMax (compute input props))

posit16 :: [Cl3Posit16] -> IO ()
posit16 input = print $ "Max Error Posit16: " ++ (show $ filtMax (compute input props))

p8 :: [Cl3P8] -> IO ()
p8 input = print $ "Max Error P8: " ++ (show $ filtMax (compute input props))

posit8 :: [Cl3Posit8] -> IO ()
posit8 input = print $ "Max Error Posit8: " ++ (show $ filtMax (compute input props))

-- Finds the maximum error, all values of NaR get naturally filtered out
filtMax :: (PositF es) => [(TestName, Cl3 es, Cl3 es)] -> (TestName, Cl3 es, Cl3 es)
filtMax xs = foldl1' maxErr xs
  where
    maxErr :: (PositF es) => (TestName, Cl3 es, Cl3 es) -> (TestName, Cl3 es, Cl3 es) -> (TestName, Cl3 es, Cl3 es)
    maxErr a@(_,_,aErr) b@(_,_,bErr) = case (compare aErr bErr) of
                                         GT -> a
                                         LT -> b
                                         EQ -> a


compute :: PositF es => [Cl3 es] -> [(TestName, Cl3 es -> Cl3 es)] -> [(TestName, Cl3 es, Cl3 es)]
compute v p = [(str,i,f i) | i <- v, (str,f) <- p]

data TestName = Test_logexp_Id
              | Test_explog_Id
              | Test_abssignum_law
              | Test_definition_recip
              | Test_reciprecip_Id
              | Test_sinasin_Id
              | Test_asinsin_Id
              | Test_cosacos_Id
              | Test_acoscos_Id
              | Test_sinhasinh_Id
              | Test_asinhsinh_Id
              | Test_coshacosh_Id
              | Test_acoshcosh_Id
              | Test_acoshcosh_Id2
              | Test_Sin2x_Id
              | Test_Cos2x_Id
              | Test_Tan2x_Id
              | Test_Sinh2x_Id
              | Test_Cosh2x_Id
              | Test_Tanh2x_Id
              | Test_Sin_phPi_shift
              | Test_Sin_nhPi_shift
              | Test_Pythagorean_Id
              | Test_HypPyth_Id
              | Test_Sym_Cosh
              | Test_Sym_Sinh
              | Test_2ixSin
            deriving (Eq,Ord,Show)

props :: PositF es => [(TestName, Cl3 es -> Cl3 es)]
props = [(Test_logexp_Id, prop_LogExp),
         (Test_explog_Id, prop_ExpLog),
         (Test_abssignum_law, prop_AbsSignum),
         (Test_definition_recip, prop_RecipDef),
         (Test_reciprecip_Id, prop_RecipID),
         (Test_sinasin_Id, prop_SinAsin),
         (Test_asinsin_Id, prop_AsinSin),
         (Test_cosacos_Id, prop_CosAcos),
         (Test_acoscos_Id, prop_AcosCos),
         (Test_sinhasinh_Id, prop_SinhAsinh),
         (Test_asinhsinh_Id, prop_AsinhSinh),
         (Test_coshacosh_Id, prop_CoshAcosh),
         (Test_acoshcosh_Id, prop_AcoshCosh),
         (Test_acoshcosh_Id2, prop_AcoshCosh2),
         (Test_Sin2x_Id, prop_DubSin),
         (Test_Cos2x_Id, prop_DubCos),
         (Test_Tan2x_Id, prop_DubTan),
         (Test_Sinh2x_Id, prop_DubSinh),
         (Test_Cosh2x_Id, prop_DubCosh),
         (Test_Tanh2x_Id, prop_DubTanh),
         (Test_Sin_phPi_shift, prop_PosSinShift),
         (Test_Sin_nhPi_shift, prop_NegSinShift),
         (Test_Pythagorean_Id, prop_SinSqCosSq),
         (Test_HypPyth_Id, prop_CoshSqmSinhSq),
         (Test_Sym_Cosh, prop_SymCosh),
         (Test_Sym_Sinh, prop_SymSinh),
         (Test_2ixSin, prop_DoubleISin)]





listRandCliffs :: PositF es => IO [Cl3 es]
listRandCliffs = do
  randCliff <-(replicateM 50).randomRIO $ (R 0, R 7)
  return (inputs ++ randCliff)

-- Standard inputs and special cases of projectors and nilpotents
inputs :: PositF es => [Cl3 es]
inputs = [R 0
         ,APS 0.1 0.2 0.3 0.4 0.5 0.6 0.7 0.8
         ,PV 0.5 0 0 0.5
         ,PV 0.5 0 0 (-0.5)
         ,BPV 0.5 0 0 0 (-0.5) 0
         ,BPV 0.5 0 0 0 0.5 0
         ,R 1
         ,R (-1)
         ,R (5/4 * pi)
         ,R pi
         ,R (3/4 * pi)
         ,R (pi/2)
         ,R (pi/4)
         ,V3 1 0 0
         ,APS 1 0.5 0 0 0 0.5 0 0
         ,APS 1 0.5 0 0 0 (-0.5) 0 0
         ,PV 1 1 0 0
         ,V3 1 0 0
         ,V3 (-1) 0 0
         ,V3 0 1 0
         ,V3 0 (-1) 0
         ,V3 0 0 1
         ,V3 0 0 (-1)
         ,V3 (5/4 * pi) 0 0
         ,V3 pi 0 0
         ,V3 (3/4 * pi) 0 0
         ,V3 (pi/2) 0 0
         ,V3 (pi/4) 0 0
         ,BV 1 0 0
         ,BV (-1) 0 0
         ,BV 0 1 0
         ,BV 0 (-1) 0
         ,BV 0 0 1
         ,BV 0 0 (-1)
         ,BV (5/4 * pi) 0 0
         ,BV pi 0 0
         ,BV (3/4 * pi) 0 0
         ,BV (pi/2) 0 0
         ,BV (pi/4) 0 0
         ,I 1
         ,I (-1)
         ,I pi
         ,I (pi/2)
         ,I (pi/4)
         ]


-------------------------------------------------------
-- | A set of properties to test
-------------------------------------------------------

prop_LogExp :: PositF es => Cl3 es -> Cl3 es
prop_LogExp (cliffor) = log (exp cliffor) ≈≈ unWrapIPartEigs cliffor
--  let cliffor' = unWrapIPartEigs cliffor  -- imaginary part of log.exp repeats
-- round off errors get large for exp larger than 5 use spectproj (log.exp) for accuracy
-- note: +/- i*pi are not really poles but cause issues due to cancelation for (BV pi 0 0), might explode here: poles [I (-pi), I (pi)] cliffor' 
--  in ((log (exp cliffor') ≈≈ cliffor'))

{- 
"Max Error P256: 
 (Test_logexp_Id,
   BPV (1.345775300002649719628531764402446353476036616196881786023653269762005820177762) (-0.219149927453103571322104319670429413933055277391296937495663428255817115942734) (-0.921765491498717492779642983249338870657522108915732731454377914010524857916025) (-3.855869753826073656510294618345036491301420231017858456688512778605467776175490) (-0.131538356517522103936904562960857848019614889829719253651330580950238493562773) (-1.620028527649688424663984579056955259721592452956397301466447820785741039024203)
   ,R (6.040219948479805050094820178826358462698325187514849997342457881959493821679264))"
"Cl3P256"
"Max Error P256: (Test_logexp_Id
  ,BPV (-0.862003150969340200811142830163853192512780944159164581917870489240658084857220) (0.132649563346343489165860542026240336160782436694235625486693473869813122536998) (-0.381628527147850949138531553641791571208707343660139431270056243114850870979206) (-1.518404525605517157222412636253555585861755822815249054121133912067845944246595) (5.421130671232055899412060837195274415507037258345642651632695032662553927301738) (-0.474534995181725339110616808175946045248929598477329497728403292211288652411335)
  ,R (5.171008891305799270501800962707290943725803921859256904658830227665452236801299))"
"Cl3P256"
 -}

-- log 0 is -Inf, Infinite vectors don't play nice
-- spectproj (exp.log) doesn't have this issue
prop_ExpLog :: PositF es => Cl3 es -> Cl3 es
prop_ExpLog (cliffor) = exp (log cliffor) ≈≈ cliffor

prop_AbsSignum :: PositF es => Cl3 es -> Cl3 es
prop_AbsSignum (cliffor) = abs cliffor * signum cliffor ≈≈ cliffor

prop_RecipDef :: PositF es => Cl3 es -> Cl3 es
prop_RecipDef (cliffor) | lsv cliffor `closeTo` 0.0 = cliffor / 0.0 -- the littleist singular value closeTo 0.0
                        | otherwise = recip cliffor * cliffor ≈≈ 1

{- -- A non-zero, zero divisor...
"Max Error P256: (Test_definition_recip,
  PV (-2.365223458902622246622776136649603663210715710855913674902154058521794029039558) (0.556091448401814401725984239606462759512286715319365251910606606595005685176563) (-4.487955154216651875320597740059658683398972680678561521542385151972650828042117e-2) (2.298484313066119361063655890059500537124262839463327307565054742133399122238169)
  ,R (5.483717055021295284487651924497137664125000000000000000000000000000000e36))"
"Cl3P256"
-}

-- singular inputs don't recip also suffers from roundoff errors at large values
prop_RecipID :: PositF es => Cl3 es -> Cl3 es
prop_RecipID (cliffor) = recip (recip cliffor) ≈≈ cliffor

prop_SinAsin :: PositF es => Cl3 es -> Cl3 es
prop_SinAsin (cliffor) = sin (asin cliffor) ≈≈ cliffor

-- if hasNilpotent cliffor
-- then poles [R 1, R (-1)] cliffor || (sin (asin cliffor) ≈≈ cliffor)
-- else sin (asin cliffor) ≈≈ cliffor

prop_AsinSin :: PositF es => Cl3 es -> Cl3 es
prop_AsinSin (cliffor) = (asin (sin cliffor) ≈≈ (I (-1) * log (0.5 * (exp (I 1 * cliffor) - exp (mIx cliffor)) + sqrt (1+0.25*(exp (mIx cliffor) - exp (I 1 * cliffor))^2))))

-- (abs cliffor > 10) || (asin (sin cliffor) ≈≈ (I (-1) * log (0.5 * (exp (I 1 * cliffor) - exp (mIx cliffor)) +
-- sqrt (1+0.25*(exp (mIx cliffor) - exp (I 1 * cliffor))^2))))

prop_CosAcos :: PositF es => Cl3 es -> Cl3 es
prop_CosAcos (cliffor) = cos (acos cliffor) ≈≈ cliffor

-- if hasNilpotent cliffor
-- then poles [R 1, R (-1)] cliffor || (cos (acos cliffor) ≈≈ cliffor)
-- else cos (acos cliffor) ≈≈ cliffor

prop_AcosCos :: PositF es => Cl3 es -> Cl3 es
prop_AcosCos (cliffor) = acos (cos cliffor) ≈≈ 0.5 * (pi - 2 * asin(cos cliffor))

-- (abs cliffor > 10) || (if hasNilpotent cliffor
-- then poles [R 0, pi, negate pi] cliffor || (acos (cos cliffor) ≈≈ 0.5 * (pi - 2 * asin(cos cliffor)))
-- else acos (cos cliffor) ≈≈ 0.5 * (pi - 2 * asin(cos cliffor)))

prop_SinhAsinh :: PositF es => Cl3 es -> Cl3 es
prop_SinhAsinh (cliffor) = sinh (asinh cliffor) ≈≈ cliffor

prop_AsinhSinh :: PositF es => Cl3 es -> Cl3 es
prop_AsinhSinh (cliffor) = (asinh (sinh cliffor) ≈≈ log (0.5*(exp cliffor - exp (negate cliffor)) + sqrt (0.25 * (exp cliffor - exp (negate cliffor))^2 + 1)))

-- (abs cliffor > 10) || (asinh (sinh cliffor) ≈≈ log (0.5*(exp cliffor - exp (negate cliffor)) +
--  sqrt (0.25 * (exp cliffor - exp (negate cliffor))^2 + 1)))

prop_CoshAcosh :: PositF es => Cl3 es -> Cl3 es
prop_CoshAcosh (cliffor) = cosh (acosh cliffor) ≈≈ cliffor

-- if hasNilpotent cliffor
-- then poles [R 1, R (-1)] cliffor || (cosh (acosh cliffor) ≈≈ cliffor)
-- else cosh (acosh cliffor) ≈≈ cliffor

prop_AcoshCosh :: PositF es => Cl3 es -> Cl3 es
prop_AcoshCosh (cliffor) = acosh (cosh cliffor) ≈≈ log (0.5*(exp cliffor + exp (negate cliffor)) +
                                                        sqrt (0.5*(exp cliffor + exp (negate cliffor)) - 1) *
                                                        sqrt (0.5*(exp cliffor + exp (negate cliffor)) + 1))

prop_AcoshCosh2 :: PositF es => Cl3 es -> Cl3 es
prop_AcoshCosh2 (cliffor) = acosh (cosh cliffor) ≈≈ log (cosh cliffor + sqrt (cosh cliffor - 1) * sqrt (cosh cliffor + 1))

prop_DubSin :: PositF es => Cl3 es -> Cl3 es
prop_DubSin (cliffor) = sin (2 * cliffor) ≈≈ 2 * sin cliffor * cos cliffor

prop_DubCos :: PositF es => Cl3 es -> Cl3 es
prop_DubCos (cliffor) = cos (2 * cliffor) ≈≈ cos cliffor ^ 2 - sin cliffor ^ 2

prop_DubTan :: PositF es => Cl3 es -> Cl3 es
prop_DubTan (cliffor) | poles [R (-5/4 * pi), R (-3/4 * pi), R (-pi/4), R (pi/4), R (3/4 * pi), R (5/4 * pi)] cliffor = cliffor / R 0.0
                      | otherwise = tan (2 * cliffor) ≈≈ (2 * tan cliffor) / (1 - tan cliffor ^ 2)

-- poles [R (-pi), R (-3*pi/4), R (-pi/2), R (-pi/4), R (pi/4), R (pi/2), R (3*pi/4), R (pi)] cliffor ||
--  (tan (2 * cliffor) ≈≈ (2 * tan cliffor) / (1 - tan cliffor ^ 2))
-- input:  V3 (0.78539816339744830961566084581987572104929234984377645524373614807695410157126) (0.00) (0.00)
-- result: R (1.036449409111714573584069473266450335772825207131701049118230053952158843e148)

prop_DubSinh :: PositF es => Cl3 es -> Cl3 es
prop_DubSinh (cliffor) = sinh (2 * cliffor) ≈≈ 2 * sinh cliffor * cosh cliffor

prop_DubCosh :: PositF es => Cl3 es -> Cl3 es
prop_DubCosh (cliffor) = cosh (2 * cliffor) ≈≈ 2 * cosh cliffor ^ 2 - 1

-- The test has poles at imaginary eigenvalues of n*pi/4 even is poles in the denominator and odd is poles in the numerator
-- The poles are a source of a loss of precision.
prop_DubTanh :: PositF es => Cl3 es -> Cl3 es
prop_DubTanh (cliffor) | poles [I (-5/4 * pi),I (-0.75 * pi),I (-pi/4), I (pi/4), I (0.75 * pi), I (5/4 * pi)] cliffor = cliffor / R 0.0
                       | otherwise = tanh (2 * cliffor) ≈≈ (2 * tanh cliffor) / (1 + tanh cliffor ^ 2)

-- poles [I (-pi), I (-3*pi/4), I (-pi/2), I (-pi/4), I (pi/4), I (pi/2), I (3*pi/4), I (pi)] cliffor ||
-- (tanh (2 * cliffor) ≈≈ (2 * tanh cliffor) / (1 + tanh cliffor ^ 2))

prop_PosSinShift :: PositF es => Cl3 es -> Cl3 es
prop_PosSinShift (cliffor) = sin (pi/2 + cliffor) ≈≈ cos cliffor

prop_NegSinShift :: PositF es => Cl3 es -> Cl3 es
prop_NegSinShift (cliffor) = sin (pi/2 - cliffor) ≈≈ cos cliffor

prop_SinSqCosSq :: PositF es => Cl3 es -> Cl3 es
prop_SinSqCosSq (cliffor) = sin cliffor ^ 2 + cos cliffor ^ 2 ≈≈ 1

-- (abs cliffor > 10) || (sin cliffor ^ 2 + cos cliffor ^ 2 ≈≈ 1)

prop_CoshSqmSinhSq :: PositF es => Cl3 es -> Cl3 es
prop_CoshSqmSinhSq (cliffor) = cosh cliffor ^ 2 - sinh cliffor ^ 2 ≈≈ 1

-- (abs cliffor > 10) || (cosh cliffor ^ 2 - sinh cliffor ^ 2 ≈≈ 1)

prop_SymCosh :: PositF es => Cl3 es -> Cl3 es
prop_SymCosh (cliffor) = cosh (negate cliffor) ≈≈ cosh cliffor

prop_SymSinh :: PositF es => Cl3 es -> Cl3 es
prop_SymSinh (cliffor) = sinh (negate cliffor) ≈≈ negate (sinh cliffor)

prop_DoubleISin :: PositF es => Cl3 es -> Cl3 es
prop_DoubleISin (cliffor) = 2 * I 1 * sin cliffor ≈≈ exp(I 1 * cliffor) - exp (mIx cliffor)

-- | Composition Sub-Algebras have a distributive norm over multiplication,
-- like this:
-- 
-- > norm $ clif * clif' = norm clif * norm clif'
--
-- Strangly the constructor combinations with the "= True" don't play nice
-- with 'abs' they are the constructors with non-zero zero-divisors.
prop_CompAlg :: PositF es => (Cl3 es, Cl3 es) -> Cl3 es
prop_CompAlg (cliffor, cliffor') = abs ( cliffor * cliffor') ≈≈ abs cliffor * abs cliffor'

{-
prop_CompAlg (PV{}, PV{}) = True
prop_CompAlg (PV{}, BPV{}) = True
prop_CompAlg (PV{}, TPV{}) = True
prop_CompAlg (PV{}, APS{}) = True
prop_CompAlg (BPV{}, PV{}) = True
prop_CompAlg (TPV{}, PV{}) = True
prop_CompAlg (APS{}, PV{}) = True
prop_CompAlg (BPV{}, BPV{}) = True
prop_CompAlg (BPV{}, TPV{}) = True
prop_CompAlg (BPV{}, APS{}) = True
prop_CompAlg (TPV{}, BPV{}) = True
prop_CompAlg (APS{}, BPV{}) = True
prop_CompAlg (TPV{}, TPV{}) = True
prop_CompAlg (TPV{}, APS{}) = True
prop_CompAlg (APS{}, TPV{}) = True
prop_CompAlg (APS{}, APS{}) = True -}

----------------------------------------------------
-- Helper functions for the properties
----------------------------------------------------

-- | '≈≈' aproximately equal, using a mean squared error like calculation
-- across the 8 dimensional vector space of APS.  The properties are 
-- equivelent symbolicly but differ due to numerical errors.
(≈≈) :: PositF es => Cl3 es -> Cl3 es -> Cl3 es
(toAPS -> (APS a0 a1 a2 a3 a23 a31 a12 a123)) ≈≈ (toAPS -> (APS b0 b1 b2 b3 b23 b31 b12 b123)) =
  let m0 = (a0 - b0)^2
      m1 = (a1 - b1)^2
      m2 = (a2 - b2)^2
      m3 = (a3 - b3)^2
      m23 = (a23 - b23)^2
      m31 = (a31 - b31)^2
      m12 = (a12 - b12)^2
      m123 = (a123 - b123)^2
  in R (sum [m0, m1, m2, m3, m23, m31, m12, m123] / 8)
_ ≈≈ _ = error "Everything passed to (≈≈) should be caught by toAPS/APS pattern match"
infix 4 ≈≈

--
-- | 'poles' a function that tests if a cliffor is one of the defined poles
poles :: PositF es => [Cl3 es] -> Cl3 es -> Bool
poles [] _ = False
poles [p] cliffor = eig1 `closeTo` p || eig2 `closeTo` p
  where (eig1,eig2) = eigvals cliffor
poles (p:ps) cliffor = (eig1 `closeTo` p || eig2 `closeTo` p) || poles ps cliffor
  where (eig1,eig2) = eigvals cliffor
--

--
-- | 'closeTo' used with poles to determine if an eigenvalue is close to a pole
-- the current threshold is 1e-3
closeTo :: PositF es => Cl3 es -> Cl3 es -> Bool
closeTo (toC -> (C a0 a123)) (toC -> (C b0 b123)) =
  let diffR = abs (a0 - b0)
      diffI = abs (a123 - b123)
      magDiff = sqrt (diffR^2 + diffI^2)
  in magDiff <= 1e-3
closeTo _ _ = error "Everything passed to 'closeTo' should be caught by toC/C pattern match"
--

-- | 'unWrapIPartEigs' a function to reduce the magnitude of the imaginary
-- portion of the Eigenvalues
unWrapIPartEigs :: PositF es => Cl3 es -> Cl3 es
unWrapIPartEigs cliffor = reduce $ spectraldcmp unWrapI id cliffor
  where unWrapI (R a0) = R a0
        unWrapI (I a123) | a123 == pi || a123 == (-pi) = I a123
                         | a123 > pi = unWrapI $ I (a123 - 2*pi)
                         | a123 < (-pi) = unWrapI $ I (a123 + 2*pi)
                         | otherwise = I a123
        unWrapI (C a0 a123) | a123 == pi || a123 == (-pi) = C a0 a123
                            | a123 > pi = unWrapI $ C a0 (a123 - 2*pi)
                            | a123 < (-pi) = unWrapI $ C a0 (a123 + 2*pi)
                            | otherwise = C a0 a123
        unWrapI _ = error "unWrapI should only be unWrapping R I and C"

-- End of File
