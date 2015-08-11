open import Preliminaries
open import Source-lang

module Examples-Source where

----- examples

  nexp = [] |- nat

  dbl-test4 : nexp
  dbl-test4 = app dbl (suc (suc z))
  four : nexp
  four = suc (suc (suc (suc z)))
  eqs4 : evals dbl-test4 four ((0c +c 0c) +c (0c +c (1c +c (0c +c (0c +c (1c +c (0c +c (0c +c (1c +c 0c)))))))))
  eqs4 = app-evals lam-evals (s-evals (s-evals z-evals)) (rec-evals (s-evals (s-evals z-evals)) (evals-rec-s (s-evals (s-evals (force-evals delay-evals (rec-evals (s-evals z-evals) (evals-rec-s (s-evals (s-evals (force-evals delay-evals (rec-evals z-evals (evals-rec-z z-evals))))))))))))

  dbl-test0 : nexp
  dbl-test0 = app dbl z
  zero : nexp
  zero = z
  eqs0 : evals dbl-test0 zero ((0c +c 0c) +c (0c +c (1c +c 0c)))
  eqs0 = app-evals lam-evals z-evals (rec-evals z-evals (evals-rec-z z-evals))

  add-test0 : nexp
  add-test0 = app (app add z) z
  eqs01 : evals add-test0 zero ((((0c +c 0c) +c 0c) +c 0c) +c (0c +c (1c +c 0c)))
  eqs01 = app-evals (app-evals lam-evals z-evals lam-evals) z-evals (rec-evals z-evals (evals-rec-z z-evals))

  one : nexp
  one = suc z
  two : nexp
  two = suc (suc z)

  add-test1 : nexp
  add-test1 = app (app add (suc z)) z
  eqs11 : evals add-test1 one ((((0c +c 0c) +c 0c) +c 0c) +c
                                (0c +c (1c +c (0c +c (0c +c (1c +c 0c))))))
  eqs11 = app-evals (app-evals lam-evals (s-evals z-evals) lam-evals) z-evals (rec-evals (s-evals z-evals) (evals-rec-s (s-evals (force-evals delay-evals (rec-evals z-evals (evals-rec-z z-evals))))))

  add-test1' : nexp
  add-test1' = app (app add z) (suc z)
  eqs11' : evals add-test1' one ((((0c +c 0c) +c 0c) +c 0c) +c (0c +c (1c +c 0c)))
  eqs11' = app-evals (app-evals lam-evals z-evals lam-evals) (s-evals z-evals) (rec-evals z-evals (evals-rec-z (s-evals z-evals)))

  add-test2 : nexp
  add-test2 = app (app add z) four
  eqs12 : evals add-test2 four ((((0c +c 0c) +c 0c) +c 0c) +c (0c +c (1c +c 0c)))
  eqs12 = app-evals (app-evals lam-evals z-evals lam-evals) (s-evals (s-evals (s-evals (s-evals z-evals)))) (rec-evals z-evals (evals-rec-z (s-evals (s-evals (s-evals (s-evals z-evals))))))

  add-test2' : nexp
  add-test2' = app (app add four) z
  eqs12' : evals add-test2' four ((((0c +c 0c) +c 0c) +c 0c) +c
                                   (0c +c
                                    (1c +c
                                     (0c +c
                                      (0c +c
                                       (1c +c
                                        (0c +c
                                         (0c +c
                                          (1c +c (0c +c (0c +c (1c +c (0c +c (0c +c (1c +c 0c)))))))))))))))
  eqs12' = app-evals (app-evals lam-evals (s-evals (s-evals (s-evals (s-evals z-evals)))) lam-evals) z-evals (rec-evals (s-evals (s-evals (s-evals (s-evals z-evals)))) (evals-rec-s (s-evals (force-evals delay-evals (rec-evals (s-evals (s-evals (s-evals z-evals))) (evals-rec-s (s-evals (force-evals delay-evals (rec-evals (s-evals (s-evals z-evals)) (evals-rec-s (s-evals (force-evals delay-evals (rec-evals (s-evals z-evals) (evals-rec-s (s-evals (force-evals delay-evals (rec-evals z-evals (evals-rec-z z-evals))))))))))))))))))

  mult-test1 : nexp
  mult-test1 = app (app mult two) two
  eqs111 : evals mult-test1 four ((((0c +c 0c) +c 0c) +c 0c) +c
                                   (0c +c
                                    (1c +c
                                     ((((0c +c 0c) +c 0c) +c
                                       (0c +c
                                        (0c +c
                                         (1c +c
                                          ((((0c +c 0c) +c 0c) +c (0c +c (0c +c (1c +c 0c)))) +c
                                           (0c +c
                                            (1c +c (0c +c (0c +c (1c +c (0c +c (0c +c (1c +c 0c)))))))))))))
                                      +c
                                      (0c +c
                                       (1c +c (0c +c (0c +c (1c +c (0c +c (0c +c (1c +c 0c))))))))))))
  eqs111 = app-evals (app-evals lam-evals (s-evals (s-evals z-evals)) lam-evals) (s-evals (s-evals z-evals)) (rec-evals (s-evals (s-evals z-evals)) (evals-rec-s (app-evals (app-evals lam-evals (s-evals (s-evals z-evals)) lam-evals) (force-evals delay-evals (rec-evals (s-evals z-evals) (evals-rec-s (app-evals (app-evals lam-evals (s-evals (s-evals z-evals)) lam-evals) (force-evals delay-evals (rec-evals z-evals (evals-rec-z z-evals))) (rec-evals (s-evals (s-evals z-evals)) (evals-rec-s (s-evals (force-evals delay-evals (rec-evals (s-evals z-evals) (evals-rec-s (s-evals (force-evals delay-evals (rec-evals z-evals (evals-rec-z z-evals)))))))))))))) (rec-evals (s-evals (s-evals z-evals)) (evals-rec-s (s-evals (force-evals delay-evals (rec-evals (s-evals z-evals) (evals-rec-s (s-evals (force-evals delay-evals (rec-evals z-evals (evals-rec-z (s-evals (s-evals z-evals)))))))))))))))

  mult-test2 : nexp
  mult-test2 = app (app mult one) one
  eqs112 : evals mult-test2 one ((((0c +c 0c) +c 0c) +c 0c) +c
                                  (0c +c
                                   (1c +c
                                    ((((0c +c 0c) +c 0c) +c (0c +c (0c +c (1c +c 0c)))) +c
                                     (0c +c (1c +c (0c +c (0c +c (1c +c 0c)))))))))
  eqs112 = app-evals (app-evals lam-evals (s-evals z-evals) lam-evals) (s-evals z-evals) (rec-evals (s-evals z-evals) (evals-rec-s (app-evals (app-evals lam-evals (s-evals z-evals) lam-evals) (force-evals delay-evals (rec-evals z-evals (evals-rec-z z-evals))) (rec-evals (s-evals z-evals) (evals-rec-s (s-evals (force-evals delay-evals (rec-evals z-evals (evals-rec-z z-evals)))))))))

  mult-test0 : nexp
  mult-test0 = app (app mult zero) zero
  eqs00 : evals mult-test0 zero ((((0c +c 0c) +c 0c) +c 0c) +c (0c +c (1c +c 0c)))
  eqs00 = app-evals (app-evals lam-evals z-evals lam-evals) z-evals (rec-evals z-evals (evals-rec-z z-evals))

