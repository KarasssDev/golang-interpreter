Cram tests here. They run and compare program output to the expected output
https://dune.readthedocs.io/en/stable/tests.html#cram-tests
Use `dune promote` after you change things that should runned

  $ ./demoAO.exe
  Evaluating: ⊥
  Result:     ⊥
  ⊥
  Evaluating: 1
  Result:     1
  1
  Evaluating: ((λ m n f x -> (m (f (n (f x))))) (1 1))
  Result:     (λ n f x _x -> ((f (n (f x))) _x))
  (λ n f x _x -> ((f (n (f x))) _x))
  Evaluating: ((λ n -> ((n (λ _ _ y -> y)) ⊤)) (1 (2 (λ f x -> (f (f (f x)))))))
  Result:     ⊥
  ⊥
  Evaluating: (((λ x y z -> (x (y z))) 1) 2)
   -- ((λ y z -> (1 (y z))) 2)
   -- ((λ y z x -> ((y z) x)) 2)
   -- (λ z x -> ((2 z) x))
   -- (λ z x -> ((λ x -> (z (z x))) x))
   -- 2
  Result:     2
  2
  Evaluating: (((λ x y z -> (x (y z))) (λ f x -> (f (f (f x))))) 2)
   -- ((λ y z -> ((λ f x -> (f (f (f x)))) (y z))) 2)
   -- ((λ y z x -> ((y z) ((y z) ((y z) x)))) 2)
   -- (λ z x -> ((2 z) ((2 z) ((2 z) x))))
   -- (λ z x -> ((λ x -> (z (z x))) ((2 z) ((2 z) x))))
   -- (λ z x -> ((λ x -> (z (z x))) ((λ x -> (z (z x))) ((2 z) x))))
   -- (λ z x -> ((λ x -> (z (z x))) ((λ x -> (z (z x))) ((λ x -> (z (z x))) x))))
   -- (λ z x -> ((λ x -> (z (z x))) ((λ x -> (z (z x))) (z (z x)))))
   -- (λ z x -> ((λ x -> (z (z x))) (z (z (z (z x))))))
   -- (λ z x -> (z (z (z (z (z (z x)))))))
  Result:     (λ z x -> (z (z (z (z (z (z x)))))))
  (λ z x -> (z (z (z (z (z (z x)))))))
  $ ./demoNO.exe
  Evaluating: (((λ f -> ((λ x -> (f (x x))) (λ x -> (f (x x))))) (λ self N -> ((((λ n -> ((n (λ _ _ y -> y)) ⊤)) N) 1) (((λ x y z -> (x (y z))) (self ((λ n f x -> (((n (λ g h -> (h (g f)))) (λ _ -> x)) (λ u -> u))) N))) N)))) (((λ m n f x -> ((m f) ((n f) x))) 2) (λ f x -> (f (f (f x))))))
  Result:     (λ z x -> (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z x)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (λ z x -> (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z (z x)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
