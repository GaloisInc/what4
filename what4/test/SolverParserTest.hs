{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}

import           Control.Monad.Catch ( SomeException, try )
import qualified Data.Text.IO as TIO
import           Numeric.Natural
import qualified System.IO.Streams as Streams

import           Test.Tasty
import           Test.Tasty.HUnit
import           Test.Tasty.Ingredients
import           Test.Tasty.Sugar

import           What4.Expr.Builder ( emptySymbolVarBimap )
import           What4.ProblemFeatures ( noFeatures )
import           What4.Protocol.SMTLib2.Response ( SMTResponse, getLimitedSolverResponse )
import qualified What4.Protocol.SMTLib2.Syntax as SMT2
import           What4.Protocol.SMTWriter


sugarCube :: CUBE
sugarCube = mkCUBE { inputDirs = [ "test/responses" ]
                   , rootName = "*.rsp"
                   , expectedSuffix = ".exp"
                   , validParams = [ ("parsing", Just ["strict", "lenient"])
                                   ]
                   }

ingredients :: [Ingredient]
ingredients = includingOptions sugarOptions :
              sugarIngredients [sugarCube] <>
              defaultIngredients


main :: IO ()
main = do testSweets <- findSugar sugarCube
          defaultMainWithIngredients ingredients .
            testGroup "solver response tests" =<<
            withSugarGroups testSweets testGroup mkTest

mkTest :: Sweets -> Natural -> Expectation -> IO [TestTree]
mkTest s n e = do
  expect <- readFile $ expectedFile e
  let strictness =
        let strictVal pmtch =
              if paramMatchVal "strict" pmtch
              then Strict
              else if paramMatchVal "lenient" pmtch
                   then Lenient
                   else error "Invalid strictness specification"
        in maybe Strict strictVal $ lookup "parsing" $ expParamsMatch e
  return
    [
      testCase (rootMatchName s <> " #" <> show n) $ do
        inpStrm <- Streams.makeInputStream $ Just <$> TIO.readFile (rootFile s)
        outStrm <- Streams.makeOutputStream $ \_ -> error "output not supported for test"
        w <- newWriterConn
             outStrm
             inpStrm
             (AckAction $ undefined)
             "test-solver"
             strictness
             noFeatures
             emptySymbolVarBimap
             ()
        actual <- try $ getLimitedSolverResponse "test resp" Just w (SMT2.Cmd "test cmd")
        expect @=? show (actual :: Either SomeException SMTResponse)
    ]
