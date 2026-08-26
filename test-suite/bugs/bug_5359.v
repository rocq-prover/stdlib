From Stdlib Require Import Nsatz.
From Stdlib Require Import BinNat.

Goal False.

  (* the first (succeeding) goal was reached by clearing one hypothesis in the second goal which overflows 6GB of stack space *)
  let sugar := constr:( 0%Z ) in
  let nparams := constr:( (-1)%Z ) in
  let reified_goal := constr:(
  (PEsub (PEc 1%Z)
     (PEmul
        (PEmul
           (PEmul
              (PEmul (PEX Z 4) (PEX Z 2))
              (PEX Z 5)) (PEX Z 3))
        (PEX Z 6))) ) in
  let power := constr:( N.one ) in
  let reified_givens := constr:(
  (PEmul
     (PEadd (PEc 1%Z)
        (PEmul
           (PEmul
              (PEmul
                 (PEmul (PEX Z 4) (PEX Z 2))
                 (PEX Z 5)) (PEX Z 3))
           (PEX Z 6)))
     (PEsub (PEc 1%Z)
        (PEmul
           (PEmul
              (PEmul
                 (PEmul (PEX Z 4) (PEX Z 2))
                 (PEX Z 5)) (PEX Z 3))
           (PEX Z 6)))
   :: PEsub
        (PEmul
           (PEadd (PEc 1%Z)
              (PEmul
                 (PEmul
                    (PEmul
                       (PEmul (PEX Z 4)
                          (PEX Z 2)) (PEX Z 5))
                    (PEX Z 3)) (PEX Z 6)))
           (PEX Z 10)) (PEc 1%Z)
      :: PEsub
           (PEmul
              (PEsub (PEc 1%Z)
                 (PEmul
                    (PEmul
                       (PEmul
                          (PEmul (PEX Z 4)
                             (PEX Z 2)) (PEX Z 5))
                       (PEX Z 3)) (PEX Z 6)))
              (PEX Z 9)) (PEc 1%Z)
         :: PEsub
              (PEadd
                 (PEmul (PEX Z 1)
                    (PEmul (PEX Z 7)
                       (PEX Z 7)))
                 (PEmul (PEX Z 8) (PEX Z 8)))
              (PEadd (PEc 1%Z)
                 (PEmul
                    (PEmul (PEX Z 4)
                       (PEmul (PEX Z 7)
                          (PEX Z 7)))
                    (PEmul (PEX Z 8)
                       (PEX Z 8))))
            :: PEsub
                 (PEadd
                    (PEmul (PEX Z 1)
                       (PEmul (PEX Z 5)
                          (PEX Z 5)))
                    (PEmul (PEX Z 6)
                       (PEX Z 6)))
                 (PEadd (PEc 1%Z)
                    (PEmul
                       (PEmul (PEX Z 4)
                          (PEmul (PEX Z 5)
                             (PEX Z 5)))
                       (PEmul (PEX Z 6)
                          (PEX Z 6))))
               :: PEsub
                    (PEadd
                       (PEmul (PEX Z 1)
                          (PEmul (PEX Z 2)
                             (PEX Z 2)))
                       (PEmul (PEX Z 3)
                          (PEX Z 3)))
                    (PEadd (PEc 1%Z)
                       (PEmul
                          (PEmul (PEX Z 4)
                             (PEmul (PEX Z 2)
                                (PEX Z 2)))
                          (PEmul (PEX Z 3)
                             (PEX Z 3)))) :: nil)%list ) in
    NsatzTactic.nsatz_compute
          (@cons _ (@PEc _ sugar) (@cons _ (@PEc _ nparams) (@cons _ (@PEpow _ reified_goal power) reified_givens))).

  let sugar := constr:( 0%Z ) in
  let nparams := constr:( (-1)%Z ) in
  let reified_goal := constr:(
  (PEsub (PEc 1%Z)
     (PEmul
        (PEmul
           (PEmul
              (PEmul (PEX Z 4) (PEX Z 2))
              (PEX Z 5)) (PEX Z 3))
        (PEX Z 6))) ) in
  let power := constr:( N.one ) in
  let reified_givens := constr:(
  (PEmul
     (PEadd (PEc 1%Z)
        (PEmul
           (PEmul
              (PEmul
                 (PEmul (PEX Z 4) (PEX Z 2))
                 (PEX Z 5)) (PEX Z 3))
           (PEX Z 6)))
     (PEsub (PEc 1%Z)
        (PEmul
           (PEmul
              (PEmul
                 (PEmul (PEX Z 4) (PEX Z 2))
                 (PEX Z 5)) (PEX Z 3))
           (PEX Z 6)))
   :: PEadd
        (PEmul
           (PEadd (PEc 1%Z)
              (PEmul
                 (PEmul
                    (PEmul
                       (PEmul (PEX Z 4)
                          (PEX Z 2)) (PEX Z 5))
                    (PEX Z 3)) (PEX Z 6)))
           (PEsub (PEc 1%Z)
              (PEmul
                 (PEmul
                    (PEmul
                       (PEmul (PEX Z 4)
                          (PEX Z 2)) (PEX Z 5))
                    (PEX Z 3)) (PEX Z 6))))
        (PEmul
           (PEmul
              (PEmul
                 (PEmul (PEX Z 4)
                    (PEadd
                       (PEmul (PEX Z 2)
                          (PEX Z 6))
                       (PEmul (PEX Z 3)
                          (PEX Z 5)))) (PEX Z 7))
              (PEsub
                 (PEmul (PEX Z 3) (PEX Z 6))
                 (PEmul
                    (PEmul (PEX Z 1)
                       (PEX Z 2)) (PEX Z 5))))
           (PEX Z 8))
      :: PEsub
           (PEmul
              (PEadd (PEc 1%Z)
                 (PEmul
                    (PEmul
                       (PEmul
                          (PEmul (PEX Z 4)
                             (PEX Z 2)) (PEX Z 5))
                       (PEX Z 3)) (PEX Z 6)))
              (PEX Z 10)) (PEc 1%Z)
         :: PEsub
              (PEmul
                 (PEsub (PEc 1%Z)
                    (PEmul
                       (PEmul
                          (PEmul
                             (PEmul (PEX Z 4)
                                (PEX Z 2))
                             (PEX Z 5)) (PEX Z 3))
                       (PEX Z 6))) (PEX Z 9))
              (PEc 1%Z)
            :: PEsub
                 (PEadd
                    (PEmul (PEX Z 1)
                       (PEmul (PEX Z 7)
                          (PEX Z 7)))
                    (PEmul (PEX Z 8)
                       (PEX Z 8)))
                 (PEadd (PEc 1%Z)
                    (PEmul
                       (PEmul (PEX Z 4)
                          (PEmul (PEX Z 7)
                             (PEX Z 7)))
                       (PEmul (PEX Z 8)
                          (PEX Z 8))))
               :: PEsub
                    (PEadd
                       (PEmul (PEX Z 1)
                          (PEmul (PEX Z 5)
                             (PEX Z 5)))
                       (PEmul (PEX Z 6)
                          (PEX Z 6)))
                    (PEadd (PEc 1%Z)
                       (PEmul
                          (PEmul (PEX Z 4)
                             (PEmul (PEX Z 5)
                                (PEX Z 5)))
                          (PEmul (PEX Z 6)
                             (PEX Z 6))))
                  :: PEsub
                       (PEadd
                          (PEmul (PEX Z 1)
                             (PEmul (PEX Z 2)
                                (PEX Z 2)))
                          (PEmul (PEX Z 3)
                             (PEX Z 3)))
                       (PEadd (PEc 1%Z)
                          (PEmul
                             (PEmul (PEX Z 4)
                                (PEmul (PEX Z 2)
                                   (PEX Z 2)))
                             (PEmul (PEX Z 3)
                                (PEX Z 3)))) :: nil)%list ) in
    NsatzTactic.nsatz_compute
          (@cons _ (@PEc _ sugar) (@cons _ (@PEc _ nparams) (@cons _ (@PEpow _ reified_goal power) reified_givens))).
Abort.
