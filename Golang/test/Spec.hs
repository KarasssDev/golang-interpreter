import Test.Hspec
import Interpreter
import Ast


main :: IO ()
main = hspec $ do

  describe "Eval expressions:" $ do

    describe "int operation:" $ do

      describe "Simple operation test:" $ do

        it "plus" $ do
          VInt 2 + VInt 3 `shouldBe` VInt 5

        it "minus" $ do
          VInt 2 - VInt 3 `shouldBe` VInt (-1)

        it "mult" $ do
          VInt 2 * VInt 3 `shouldBe` VInt 6

        it "div" $ do 
          VInt 3 `div` VInt 2 `shouldBe` VInt 1

        it "mod" $ do 
          VInt 3 `mod` VInt 2 `shouldBe` VInt 1

        it "unary minus" $ do 
           -(VInt 2) `shouldBe` VInt (-2)

      describe "Commutative ring with identitys axioms:" $ do

        -- abelian group
        it "plus commutativity" $ do
          VInt 3 + VInt 4 `shouldBe` VInt 4 + VInt 3

        it "plus associativity" $ do
          (VInt 3 + VInt 4) + VInt 5 `shouldBe` VInt 3 + (VInt 4 + VInt 5)

        it "exist neutral" $ do
          VInt 3 + VInt 0 `shouldBe` VInt 3

        it "exist opposite" $ do
          VInt 3 + VInt (-3) `shouldBe` VInt 0

        -- monoid
        it "mult associativity" $ do
          (VInt 3 * VInt 4) * VInt 5 `shouldBe` VInt 3 * (VInt 4 * VInt 5)

        it "exist identity" $ do
          VInt 3 * VInt 1 `shouldBe` VInt 3

        -- distributive
        it "distributive" $ do
          (VInt 3 + VInt 4) * VInt 5 
            `shouldBe` VInt 3 * VInt 5 + VInt 4 * VInt 5

        -- mult commutativity
        it "mult commutativity" $ do
          VInt 3 * VInt 4 `shouldBe` VInt 4 * VInt 3

    describe "bool operation" $ do

      describe "Simple operation test:" $ do

        it "T and T = T" $ do
          VBool True `goAnd` VBool True `shouldBe` VBool True

        it "F and T = F" $ do
          VBool False `goAnd` VBool True `shouldBe` VBool False

        it "T and F = F" $ do
          VBool True `goAnd` VBool False `shouldBe` VBool False

        it "F and F = F" $ do
          VBool False `goAnd` VBool False `shouldBe` VBool False

        it "T or T = T" $ do
          VBool True `goOr` VBool True `shouldBe` VBool True

        it "F or T = T" $ do
          VBool False `goOr` VBool True `shouldBe` VBool True

        it "T or F = T" $ do
          VBool True `goOr` VBool False `shouldBe` VBool True

        it "F or F = F" $ do
          VBool False `goOr` VBool False `shouldBe` VBool False

        it "not T = F" $ do
          goNot (VBool True) `shouldBe` VBool False

        it "not F = T" $ do
          goNot (VBool False) `shouldBe` VBool True


        

        

    


