import Test.Hspec

import Type 
import Lib (someFunc) 

main :: IO ()
main = hspec $ do

  describe "GoInt" $ do

    it "can parse integers" $ do
      plus (GoInt 3) (GoInt 4) `shouldBe` (GoInt 7)

    


