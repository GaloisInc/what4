{-# LANGUAGE DataKinds #-}

import Data.Parameterized (knownNat)
import Prettyprinter
import Test.Tasty
import Test.Tasty.HUnit
import What4.BaseTypes (FloatPrecisionRepr (FloatingPointPrecisionRepr), NatRepr, StringInfoRepr (Char16Repr, Char8Repr, UnicodeRepr))
import What4.InterpretedFloatingPoint (FloatInfoRepr (DoubleDoubleFloatRepr, DoubleFloatRepr, HalfFloatRepr, QuadFloatRepr, SingleFloatRepr, X86_80FloatRepr))

testPrettyPrint :: (Pretty a) => String -> a -> String -> TestTree
testPrettyPrint tcName obj expected =
  testCase tcName $
    let s = show $ pretty obj
     in assertEqual "Should be equal" expected s

testPrintHalfFloatRepr :: TestTree
testPrintHalfFloatRepr = testPrettyPrint "Print half repr" HalfFloatRepr "Half"

testPrintFloatInfoRepr :: TestTree
testPrintFloatInfoRepr = testPrettyPrint "Print single repr" SingleFloatRepr "Float"

testPrintDoubleInfoRepr :: TestTree
testPrintDoubleInfoRepr = testPrettyPrint "Print double repr" DoubleFloatRepr "Double"

testPrintQuadInfoRepr :: TestTree
testPrintQuadInfoRepr = testPrettyPrint "Print quad repr" QuadFloatRepr "Quad"

testPrintX86_80InfoRepr :: TestTree
testPrintX86_80InfoRepr = testPrettyPrint "Print X86_80 repr" X86_80FloatRepr "X86_80"

testPrintDoubleDoubleInfoRepr :: TestTree
testPrintDoubleDoubleInfoRepr = testPrettyPrint "Print double double repr" DoubleDoubleFloatRepr "DoubleDouble"

five :: NatRepr 5
five = knownNat

eleven :: NatRepr 11
eleven = knownNat

main :: IO ()
main =
  defaultMain $
    testGroup "printers" $
      [ testGroup "Float printers" $
          [ testPrintFloatInfoRepr,
            testPrintHalfFloatRepr,
            testPrintDoubleInfoRepr,
            testPrintQuadInfoRepr,
            testPrintX86_80InfoRepr,
            testPrintDoubleDoubleInfoRepr
          ],
        testGroup "String repr printers" $
          [ testPrettyPrint "Print unicode repr" UnicodeRepr "Unicode",
            testPrettyPrint "Print char16 repr" Char16Repr "Char16",
            testPrettyPrint "Print char8 repr" Char8Repr "Char8"
          ],
        testGroup "Float precision repr prints" $
          [ testPrettyPrint "Print float precision repr" (FloatingPointPrecisionRepr five eleven) "(FloatingPrecision 5 11)"
          ]
      ]