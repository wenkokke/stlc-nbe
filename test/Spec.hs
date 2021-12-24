import Control.Enumerable (global)
import Control.Enumerable.Count (Count (..), (!!*))
import Control.Search (ctrex)
import STLC
import Test.HUnit

depth :: Int
depth = 15

worstCase :: Int
worstCase = fromInteger $ global @Count @(Expr Z) !!* depth

reportCounts :: Integer -> Assertion
reportCounts i = do
  -- "Cases: 202696  Tried: 436  Errors: 0  Failures: 0"
  let counts = Counts worstCase (fromInteger i) 0 0
  putStrLn (showCounts counts)

reportCtrex :: Expr Z -> Assertion
reportCtrex e =
  assertFailure $ "Found counterexample: " <> show e

test_NbsPreservesTypes :: Test
test_NbsPreservesTypes =
  TestLabel "NBS preserves types" $
    TestCase $ do
      ctrex depth prop_NbsPreservesTypes >>= \case
        Left i -> reportCounts i
        Right e -> reportCtrex e

test_NbePreservesTypes :: Test
test_NbePreservesTypes =
  TestLabel "NBE preserves types" $
    TestCase $ do
      ctrex depth prop_NbePreservesTypes >>= \case
        Left i -> reportCounts i
        Right e -> reportCtrex e

test_NbsEqNbe :: Test
test_NbsEqNbe =
  TestLabel "NBS is equivalent to NBE" $
    TestCase $ do
      ctrex depth prop_NbsEqNbe >>= \case
        Left i -> reportCounts i
        Right e -> reportCtrex e

tests :: Test
tests =
  TestList
    [ test_NbsPreservesTypes,
      test_NbePreservesTypes,
      test_NbsEqNbe
    ]

main :: IO ()
main = do
  runTestTT tests
  return ()
