import Test.Tasty
import Test.Tasty.HUnit
import What4.InterpretedFloatingPoint(FloatInfoRepr (HalfFloatRepr, SingleFloatRepr, DoubleFloatRepr, QuadFloatRepr, X86_80FloatRepr, DoubleDoubleFloatRepr))
import Prettyprinter



testPrettyPrint :: (Pretty a) => String -> a -> String -> TestTree
testPrettyPrint tcName obj expected = testCase tcName $ 
    let s = show $ pretty obj in
    assertEqual "Should be equal" expected s


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


main :: IO ()
main = defaultMain $
  testGroup "Float printers" $ 
  [testPrintFloatInfoRepr, 
  testPrintHalfFloatRepr, 
  testPrintDoubleInfoRepr, 
  testPrintQuadInfoRepr, 
  testPrintX86_80InfoRepr, 
  testPrintDoubleDoubleInfoRepr]