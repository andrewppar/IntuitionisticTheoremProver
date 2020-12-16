import Test.Hspec
import Formula
import Prover

p :: Formula
p = AtomicFormula "p"

q :: Formula
q = AtomicFormula "q"


main :: IO()
main = hspec $ do
  describe "Test Suite for IntuitionisticTheoremProver" spec_prove


spec_prove :: Spec
spec_prove = do
  it (show (Or [p, Not p]) ++ " should be CounterExample") $
    prove (Or [p, Not p]) `shouldBe` CounterExample

  it  (show (Implies (Implies (Implies p q) p) p) ++ " should be CounterExample") $
    prove (Implies (Implies (Implies p q) p) p) `shouldBe` CounterExample

  it (show (Not (Not (Or [p, Not p]))) ++ " should be Proved") $
    prove (Not (Not (Or [p, Not p]))) `shouldBe` Proved

  it (show (Implies (Not (Not p)) p) ++ " should be CounterExample") $
     prove (Implies (Not (Not p)) p) `shouldBe` CounterExample

  it (show (Implies p (Not (Not p))) ++ " should be Proved") $
     prove (Implies p (Not (Not p))) `shouldBe` Proved

  it (show (Not (And [p, Not p])) ++ " should be Proved") $
     prove (Not (And [p, Not p])) `shouldBe` Proved

  it (show (And [Implies (Not p)(Not q), Or [Not (Not p), Not q]]) ++ " should be CounterExample") $
     prove (And [Implies (Not p)(Not q), Or [Not (Not p), Not q]]) `shouldBe` CounterExample

  it (show p ++ " should be CounterExample") $
     prove p `shouldBe` CounterExample

  it (show (Equivalent (Not (Not (Not p)))p) ++ " should be CounterExample") $
     prove (Equivalent (Not (Not (Not p)))p) `shouldBe` CounterExample

  it (show (Implies p (Or [p, Not p])) ++ " should be Proved") $
     prove (Implies p (Or [p, Not p])) `shouldBe` Proved

  it (show (Or [Or [p, q], Not p]) ++ " should be CounterExample") $
     prove (Or [Or [p,q], Not p]) `shouldBe` CounterExample

  it (show (Implies p p) ++ " should be Proved") $
     prove (Implies p p) `shouldBe` Proved

  it (show (Implies (And [p, Implies p q,Implies q (AtomicFormula "r")]) (AtomicFormula "r")) ++ " should be Proved") $
     prove (Implies (And [p, Implies p q,Implies q (AtomicFormula "r")]) (AtomicFormula "r")) `shouldBe` Proved

  it (show (Equivalent (Equivalent p q)(Equivalent q p)) ++ " should be Proved") $
     prove (Equivalent (Equivalent p q)(Equivalent q p)) `shouldBe` Proved

  it (show (Implies (And [Or [p, q], Implies p (Not q), Implies p q])(And [q, Not p])) ++ " should be Proved") $
     prove (Implies (And [Or [p, q], Implies p (Not q), Implies p q])(And [q, Not p])) `shouldBe` Proved

  it (show (And [Implies (Not (Or [p, q])) (And [Not p, Not q]),Implies (And [Not p, Not q]) (Not (Or [p,q]))]) ++ " should be Proved") $
     prove (And [Implies (Not (Or [p, q])) (And [Not p, Not q]),Implies (And [Not p, Not q]) (Not (Or [p,q]))]) `shouldBe` Proved

  it (show (Implies (Not (Not p)) p) ++ " should be CounterExample") $
     prove (Implies (Not (Not p)) p) `shouldBe` CounterExample

  it (show (Implies p (Not (Not p))) ++ " should be Proved") $
     prove (Implies p (Not (Not p))) `shouldBe` Proved

  it (show (Implies (Or [Not p, Not q])(Not (And [p, q]))) ++ " should be Proved") $
     prove (Implies (Or [Not p, Not q])(Not (And [p, q]))) `shouldBe` Proved

  it (show (Not (Not (Implies (Equivalent (Not p) (Not p)) (Not q)))) ++ " should be CounterExample") $
     prove (Not (Not (Implies (Equivalent (Not p) (Not p)) (Not q)))) `shouldBe` CounterExample

  it (show (Not (Not (Implies (Not (Equivalent (Not p)(Not p))) (Not q)))) ++ " should be Proved") $
     prove (Not (Not (Implies (Not (Equivalent (Not p)(Not p))) (Not q)))) `shouldBe` Proved

  it (show (Not (Not (Implies (Not (Implies p p)) (Not q)))) ++ " should be Proved") $
     prove (Not (Not (Implies (Not (Implies p p)) (Not q)))) `shouldBe` Proved

  it (show (Not (Not (Or [Not (Implies (Not p) (Not (Not p))), p]))) ++ " should be Proved") $
     prove (Not (Not (Or [Not (Implies (Not p) (Not (Not p))), p]))) `shouldBe` Proved

  it (show (Not (Not (Or [Not (Equivalent p (Not p)), Not (Not p)]))) ++ " should be Proved") $
     prove (Not (Not (Or [Not (Equivalent p (Not p)), Not (Not p)]))) `shouldBe` Proved

  it (show (Equivalent (And [AtomicFormula "a", AtomicFormula "b"]) (Not (Or [Not (AtomicFormula "a"), Not (AtomicFormula "b")]))) ++ " should be CounterExample") $
     prove (Equivalent (And [AtomicFormula "a", AtomicFormula "b"]) (Not (Or [Not (AtomicFormula "a"), Not (AtomicFormula "b")]))) `shouldBe` CounterExample

  it (show (Not (Not (Implies (Not (Implies p (Not q))) (Not (Not q))))) ++ " should be Proved") $
     prove (Not (Not (Implies (Not (Implies p (Not q))) (Not (Not q))))) `shouldBe` Proved

  it (show (Not (Not (Implies (Not (Implies p (Not q))) (Not (Not p))))) ++ " should be Proved") $
     prove (Not (Not (Implies (Not (Implies p (Not q))) (Not (Not p))))) `shouldBe` Proved

  it (show (Not (Not (Implies (Not (Implies p p)) (Not (Not (Not p)))))) ++ " should be Proved") $
     prove (Not (Not (Implies (Not (Implies p p)) (Not (Not (Not p)))))) `shouldBe` Proved

  it (show (Equivalent (And [p]) p) ++ " should be Proved") $
     prove (Equivalent (And [p]) p) `shouldBe` Proved

  it (show (Not p) ++ " should be CounterExample") $
     prove (Not p) `shouldBe` CounterExample

  it (show (Not (Not (Or [Not p, And [Not p, Not p]]))) ++ " should be CounterExample") $
     prove (Not (Not (Or [Not p, And [Not p, Not p]]))) `shouldBe` CounterExample

  it (show (Not (Not (Or [Not p, Not (And [Not p, Not p])]))) ++ " should be Proved") $
     prove (Not (Not (Or [Not p, Not (And [Not p, Not p])]))) `shouldBe` Proved

  it (show (Not (Not (Equivalent (Not p) (Not (Not (Implies p (Not p))))))) ++ " should be Proved") $
     prove (Not (Not (Equivalent (Not p) (Not (Not (Implies p (Not p))))))) `shouldBe` Proved

  it (show (Not (Not (Equivalent (Not p)(Not (Not (Not (Or [p, p]))))))) ++ " should be Proved") $
     prove (Not (Not (Equivalent (Not p)(Not (Not (Not (Or [p, p]))))))) `shouldBe` Proved

  it (show (Not (Not (Implies (Not p) (Not (Not (Not (Not (Not (Not (Not p)))))))))) ++ " should be Proved") $
     prove (Not (Not (Implies (Not p) (Not (Not (Not (Not (Not (Not (Not p)))))))))) `shouldBe` Proved

  it (show (Not (And [Implies p p,Not p])) ++ " should be CounterExample") $
     prove (Not (And [Implies p p,Not p])) `shouldBe` CounterExample

  it (show (Not (Not (Or [Not (Equivalent (Not (AtomicFormula "a")) (AtomicFormula "a")), Not (Not (AtomicFormula "b"))]))) ++ " should be Proved") $
     prove (Not (Not (Or [Not (Equivalent (Not (AtomicFormula "a")) (AtomicFormula "a")), Not (Not (AtomicFormula "b"))]))) `shouldBe` Proved

  it (show (Not (Not (Equivalent (Equivalent (Equivalent (AtomicFormula "a") (AtomicFormula "a")) (AtomicFormula "a")) (AtomicFormula "a")))) ++ " should be Proved") $
     prove (Not (Not (Equivalent (Equivalent (Equivalent (AtomicFormula "a") (AtomicFormula "a")) (AtomicFormula "a")) (AtomicFormula "a")))) `shouldBe` Proved
