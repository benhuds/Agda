monotone
(λ x →
   0 ,
   monotone
   (λ p₁ →
      0 ,
      monotone
      (λ p₂ →
         fst
         (lrec p₁ (1 , 1)
          (λ x₁ x₂ x₃ →
             S
             (S
              (S
               (((fst
                  (natrec
                   (1 ,
                    monotone
                    (λ p₃ →
                       S (fst (natrec (1 , 1) (λ n x₄ → 1 , 0) p₃)) ,
                       snd (natrec (1 , 1) (λ n x₄ → 1 , 0) p₃))
                    (λ a b c → ERASED))
                   (λ n x₄ →
                      1 ,
                      monotone
                      (λ p₃ →
                         fst
                         (natrec (1 , 0)
                          (λ n₁ x₅ →
                             S (S ((fst x₄ + 0) + fst (Monotone.f (snd x₄) n₁))) ,
                             snd (Monotone.f (snd x₄) n₁))
                          p₃)
                         ,
                         snd
                         (natrec (1 , 0)
                          (λ n₁ x₅ →
                             S (S ((fst x₄ + 0) + fst (Monotone.f (snd x₄) n₁))) ,
                             snd (Monotone.f (snd x₄) n₁))
                          p₃))
                      (λ a b c → ERASED))
                   p₂)
                  + 0)
                 +
                 fst
                 (Monotone.f
                  (snd
                   (natrec
                    (1 ,
                     monotone
                     (λ p₃ →
                        S (fst (natrec (1 , 1) (λ n x₄ → 1 , 0) p₃)) ,
                        snd (natrec (1 , 1) (λ n x₄ → 1 , 0) p₃))
                     (λ a b c → ERASED))
                    (λ n x₄ →
                       1 ,
                       monotone
                       (λ p₃ →
                          fst
                          (natrec (1 , 0)
                           (λ n₁ x₅ →
                              S (S ((fst x₄ + 0) + fst (Monotone.f (snd x₄) n₁))) ,
                              snd (Monotone.f (snd x₄) n₁))
                           p₃)
                          ,
                          snd
                          (natrec (1 , 0)
                           (λ n₁ x₅ →
                              S (S ((fst x₄ + 0) + fst (Monotone.f (snd x₄) n₁))) ,
                              snd (Monotone.f (snd x₄) n₁))
                           p₃))
                       (λ a b c → ERASED))
                    p₂))
                  x₁))
                +
                fst
                (natrec (S (fst x₃) , S (snd x₃)) (λ n x₄ → 1 , 0)
                 (snd
                  (Monotone.f
                   (snd
                    (natrec
                     (1 ,
                      monotone
                      (λ p₃ →
                         S (fst (natrec (1 , 1) (λ n x₄ → 1 , 0) p₃)) ,
                         snd (natrec (1 , 1) (λ n x₄ → 1 , 0) p₃))
                      (λ a b c → ERASED))
                     (λ n x₄ →
                        1 ,
                        monotone
                        (λ p₃ →
                           fst
                           (natrec (1 , 0)
                            (λ n₁ x₅ →
                               S (S ((fst x₄ + 0) + fst (Monotone.f (snd x₄) n₁))) ,
                               snd (Monotone.f (snd x₄) n₁))
                            p₃)
                           ,
                           snd
                           (natrec (1 , 0)
                            (λ n₁ x₅ →
                               S (S ((fst x₄ + 0) + fst (Monotone.f (snd x₄) n₁))) ,
                               snd (Monotone.f (snd x₄) n₁))
                            p₃))
                        (λ a b c → ERASED))
                     p₂))
                   x₁))))))
             ,
             snd
             (natrec (S (fst x₃) , S (snd x₃)) (λ n x₄ → 1 , 0)
              (snd
               (Monotone.f
                (snd
                 (natrec
                  (1 ,
                   monotone
                   (λ p₃ →
                      S (fst (natrec (1 , 1) (λ n x₄ → 1 , 0) p₃)) ,
                      snd (natrec (1 , 1) (λ n x₄ → 1 , 0) p₃))
                   (λ a b c → ERASED))
                  (λ n x₄ →
                     1 ,
                     monotone
                     (λ p₃ →
                        fst
                        (natrec (1 , 0)
                         (λ n₁ x₅ →
                            S (S ((fst x₄ + 0) + fst (Monotone.f (snd x₄) n₁))) ,
                            snd (Monotone.f (snd x₄) n₁))
                         p₃)
                        ,
                        snd
                        (natrec (1 , 0)
                         (λ n₁ x₅ →
                            S (S ((fst x₄ + 0) + fst (Monotone.f (snd x₄) n₁))) ,
                            snd (Monotone.f (snd x₄) n₁))
                         p₃))
                     (λ a b c → ERASED))
                  p₂))
                x₁)))))
         ,
         snd
         (lrec p₁ (1 , 1)
          (λ x₁ x₂ x₃ →
             S
             (S
              (S
               (((fst
                  (natrec
                   (1 ,
                    monotone
                    (λ p₃ →
                       S (fst (natrec (1 , 1) (λ n x₄ → 1 , 0) p₃)) ,
                       snd (natrec (1 , 1) (λ n x₄ → 1 , 0) p₃))
                    (λ a b c → ERASED))
                   (λ n x₄ →
                      1 ,
                      monotone
                      (λ p₃ →
                         fst
                         (natrec (1 , 0)
                          (λ n₁ x₅ →
                             S (S ((fst x₄ + 0) + fst (Monotone.f (snd x₄) n₁))) ,
                             snd (Monotone.f (snd x₄) n₁))
                          p₃)
                         ,
                         snd
                         (natrec (1 , 0)
                          (λ n₁ x₅ →
                             S (S ((fst x₄ + 0) + fst (Monotone.f (snd x₄) n₁))) ,
                             snd (Monotone.f (snd x₄) n₁))
                          p₃))
                      (λ a b c → ERASED))
                   p₂)
                  + 0)
                 +
                 fst
                 (Monotone.f
                  (snd
                   (natrec
                    (1 ,
                     monotone
                     (λ p₃ →
                        S (fst (natrec (1 , 1) (λ n x₄ → 1 , 0) p₃)) ,
                        snd (natrec (1 , 1) (λ n x₄ → 1 , 0) p₃))
                     (λ a b c → ERASED))
                    (λ n x₄ →
                       1 ,
                       monotone
                       (λ p₃ →
                          fst
                          (natrec (1 , 0)
                           (λ n₁ x₅ →
                              S (S ((fst x₄ + 0) + fst (Monotone.f (snd x₄) n₁))) ,
                              snd (Monotone.f (snd x₄) n₁))
                           p₃)
                          ,
                          snd
                          (natrec (1 , 0)
                           (λ n₁ x₅ →
                              S (S ((fst x₄ + 0) + fst (Monotone.f (snd x₄) n₁))) ,
                              snd (Monotone.f (snd x₄) n₁))
                           p₃))
                       (λ a b c → ERASED))
                    p₂))
                  x₁))
                +
                fst
                (natrec (S (fst x₃) , S (snd x₃)) (λ n x₄ → 1 , 0)
                 (snd
                  (Monotone.f
                   (snd
                    (natrec
                     (1 ,
                      monotone
                      (λ p₃ →
                         S (fst (natrec (1 , 1) (λ n x₄ → 1 , 0) p₃)) ,
                         snd (natrec (1 , 1) (λ n x₄ → 1 , 0) p₃))
                      (λ a b c → ERASED))
                     (λ n x₄ →
                        1 ,
                        monotone
                        (λ p₃ →
                           fst
                           (natrec (1 , 0)
                            (λ n₁ x₅ →
                               S (S ((fst x₄ + 0) + fst (Monotone.f (snd x₄) n₁))) ,
                               snd (Monotone.f (snd x₄) n₁))
                            p₃)
                           ,
                           snd
                           (natrec (1 , 0)
                            (λ n₁ x₅ →
                               S (S ((fst x₄ + 0) + fst (Monotone.f (snd x₄) n₁))) ,
                               snd (Monotone.f (snd x₄) n₁))
                            p₃))
                        (λ a b c → ERASED))
                     p₂))
                   x₁))))))
             ,
             snd
             (natrec (S (fst x₃) , S (snd x₃)) (λ n x₄ → 1 , 0)
              (snd
               (Monotone.f
                (snd
                 (natrec
                  (1 ,
                   monotone
                   (λ p₃ →
                      S (fst (natrec (1 , 1) (λ n x₄ → 1 , 0) p₃)) ,
                      snd (natrec (1 , 1) (λ n x₄ → 1 , 0) p₃))
                   (λ a b c → ERASED))
                  (λ n x₄ →
                     1 ,
                     monotone
                     (λ p₃ →
                        fst
                        (natrec (1 , 0)
                         (λ n₁ x₅ →
                            S (S ((fst x₄ + 0) + fst (Monotone.f (snd x₄) n₁))) ,
                            snd (Monotone.f (snd x₄) n₁))
                         p₃)
                        ,
                        snd
                        (natrec (1 , 0)
                         (λ n₁ x₅ →
                            S (S ((fst x₄ + 0) + fst (Monotone.f (snd x₄) n₁))) ,
                            snd (Monotone.f (snd x₄) n₁))
                         p₃))
                     (λ a b c → ERASED))
                  p₂))
                x₁))))))
      (λ a b c → ERASED))
   (λ a b c → ERASED))
(λ x y z₁ → ERASED)
