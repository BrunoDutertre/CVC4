; COMMAND-LINE: --no-check-proofs
(benchmark sc_init_frame_gap.induction.smt
  :source {
The Formal Verification of a Reintegration Protocol. Author: Lee Pike. Website: http://www.cs.indiana.edu/~lepike/pub_pages/emsoft.html.

This benchmark was automatically translated into SMT-LIB format from
CVC format using CVC Lite
}
  :status unsat
:category { industrial }
:difficulty { 0 }
  :logic QF_LRA
  
  :extrafuns ((x_0 Real))
  :extrapreds ((x_1))
  :extrafuns ((x_2 Real))
  :extrafuns ((x_3 Real))
  :extrapreds ((x_4))
  :extrafuns ((x_5 Real))
  :extrapreds ((x_6))
  :extrapreds ((x_7))
  :extrapreds ((x_8))
  :extrafuns ((x_9 Real))
  :extrafuns ((x_10 Real))
  :extrapreds ((x_11))
  :extrapreds ((x_12))
  :extrapreds ((x_13))
  :extrapreds ((x_14))
  :extrapreds ((x_15))
  :extrapreds ((x_16))
  :extrafuns ((x_17 Real))
  :extrafuns ((x_18 Real))
  :extrafuns ((x_19 Real))
  :extrafuns ((x_20 Real))
  :extrapreds ((x_21))
  :extrapreds ((x_22))
  :extrapreds ((x_23))
  :extrapreds ((x_24))
  :extrapreds ((x_25))
  :extrafuns ((x_26 Real))
  :extrafuns ((x_27 Real))
  :extrapreds ((x_28))
  :extrapreds ((x_29))
  :extrafuns ((x_30 Real))
  :extrafuns ((x_31 Real))
  :extrafuns ((x_32 Real))
  :extrafuns ((x_33 Real))
  :extrafuns ((x_34 Real))
  :extrafuns ((x_35 Real))
  :extrafuns ((x_36 Real))
  :extrapreds ((x_37))
  :extrapreds ((x_38))
  :extrapreds ((x_39))
  :extrapreds ((x_40))
  :extrapreds ((x_41))
  :extrapreds ((x_42))
  :extrafuns ((x_43 Real))
  :extrafuns ((x_44 Real))
  :extrafuns ((x_45 Real))
  :extrafuns ((x_46 Real))
  :extrafuns ((x_47 Real))
  :extrafuns ((x_48 Real))
  :extrafuns ((x_49 Real))
  :extrafuns ((x_50 Real))
  :extrafuns ((x_51 Real))
  :extrafuns ((x_52 Real))
  :extrapreds ((x_53))
  :extrafuns ((x_54 Real))
  :extrafuns ((x_55 Real))
  :extrafuns ((x_56 Real))
  :formula
(flet ($cvcl_4 x_6) (flet ($cvcl_6 x_7) (flet ($cvcl_7 x_8) (flet ($cvcl_0 x_14) (flet ($cvcl_1 x_15) (flet ($cvcl_2 x_16) (let (?cvcl_39 (+ x_10 x_2)) (flet ($cvcl_92 (<= x_9 x_26)) (flet ($cvcl_68 (iff x_14 x_6)) (flet ($cvcl_18 (= x_17 0)) (flet ($cvcl_24 $cvcl_18) (flet ($cvcl_25 (< x_9 x_27)) (flet ($cvcl_52 (= x_26 x_9)) (flet ($cvcl_79 $cvcl_52) (flet ($cvcl_69 (= x_17 2)) (flet ($cvcl_80 $cvcl_69) (flet ($cvcl_82 (iff x_28 x_29)) (flet ($cvcl_83 (and (iff x_21 x_11) (iff x_22 x_12))) (flet ($cvcl_66 (iff x_25 x_13)) (flet ($cvcl_67 (and (iff x_23 x_1) (iff x_24 x_4))) (flet ($cvcl_84 (= x_30 x_31)) (flet ($cvcl_85 (and (= x_32 x_33) (= x_34 x_35))) (flet ($cvcl_35 (= x_36 x_27)) (flet ($cvcl_65 (iff x_15 x_7)) (flet ($cvcl_63 (iff x_37 x_38)) (flet ($cvcl_64 (and (iff x_39 x_40) (iff x_41 x_42))) (flet ($cvcl_86 (iff x_16 x_8)) (let (?cvcl_94 (- x_18 x_10)) (flet ($cvcl_36 (= x_17 1)) (flet ($cvcl_56 $cvcl_36) (let (?cvcl_60 (+ x_2 x_10)) (flet ($cvcl_55 (<= x_43 x_26)) (flet ($cvcl_62 (iff x_28 (or x_29  (and $cvcl_55 x_38) ))) (flet ($cvcl_42 (<= x_3 ?cvcl_39)) (flet ($cvcl_44 (<= x_5 ?cvcl_39)) (flet ($cvcl_37 (<= x_3 x_2)) (flet ($cvcl_41 $cvcl_37) (flet ($cvcl_38 (<= x_5 x_2)) (flet ($cvcl_43 $cvcl_38) (flet ($cvcl_19 (not x_11)) (flet ($cvcl_47 $cvcl_19) (flet ($cvcl_71 (< x_3 x_9)) (flet ($cvcl_72 (= x_26 x_3)) (flet ($cvcl_20 (not x_12)) (flet ($cvcl_49 $cvcl_20) (flet ($cvcl_74 (< x_5 x_9)) (flet ($cvcl_75 (= x_26 x_5)) (flet ($cvcl_28 (not x_29)) (flet ($cvcl_51 $cvcl_28) (flet ($cvcl_95 (not $cvcl_92)) (flet ($cvcl_46 (not x_40)) (flet ($cvcl_48 (not x_42)) (flet ($cvcl_50 (not x_38)) (flet ($cvcl_53 (and (not $cvcl_37) (<= x_3 x_26))) (flet ($cvcl_54 (and (not $cvcl_38) (<= x_5 x_26))) (flet ($cvcl_61 (and (iff x_21 (or x_11  (and $cvcl_53 x_40) )) (iff x_22 (or x_12  (and $cvcl_54 x_42) )))) (flet ($cvcl_45 (<= x_43 ?cvcl_39)) (flet ($cvcl_77 (< x_43 x_9)) (flet ($cvcl_78 (= x_26 x_43)) (flet ($cvcl_81 (<= (ite x_13 (ite x_4 (ite x_1 3 2) x_44) (ite x_4 x_44 (ite x_1 1 0))) (* (* (ite x_29 (ite x_12 (ite x_11 0 1) x_45) (ite x_12 x_45 (ite x_11 2 3))) 1) (/ 1 2)))) (flet ($cvcl_96 $cvcl_55) (flet ($cvcl_57 (not $cvcl_42)) (flet ($cvcl_58 (not $cvcl_44)) (flet ($cvcl_11 (and (not (<= x_43 x_2)) $cvcl_55)) (flet ($cvcl_12 $cvcl_11) (flet ($cvcl_15 (and (not (<= x_46 x_2)) (<= x_46 x_26))) (flet ($cvcl_13 $cvcl_15) (flet ($cvcl_16 $cvcl_11) (flet ($cvcl_17 $cvcl_15) (flet ($cvcl_59 (not $cvcl_45)) (flet ($cvcl_34 (= x_30 0)) (flet ($cvcl_23 (= x_30 3)) (flet ($cvcl_30 (= x_32 0)) (flet ($cvcl_21 (= x_32 3)) (flet ($cvcl_32 (= x_34 0)) (flet ($cvcl_22 (= x_34 3)) (flet ($cvcl_5 (not (= x_0 2))) (flet ($cvcl_9 (< x_2 x_3)) (flet ($cvcl_10 (< x_2 x_5)) (flet ($cvcl_3 (not $cvcl_36)) (flet ($cvcl_91 (not (<= x_18 x_19))) (flet ($cvcl_93 (not (<= x_18 x_20))) (flet ($cvcl_97 (not x_23)) (flet ($cvcl_99 (not x_24)) (flet ($cvcl_40 (not x_16)) (flet ($cvcl_98 (< x_26 x_19)) (flet ($cvcl_100 (< x_26 x_20)) (flet ($cvcl_87 (= x_0 0)) (flet ($cvcl_90 (not $cvcl_87)) (flet ($cvcl_88 (= x_0 1)) (flet ($cvcl_8 (not $cvcl_88)) (flet ($cvcl_70 (not x_1)) (flet ($cvcl_73 (not x_4)) (flet ($cvcl_76 (not x_13)) (flet ($cvcl_89 (not x_8)) (flet ($cvcl_14 (and (not (<= x_49 x_2)) (<= x_49 x_26))) (flet ($cvcl_26 (= x_32 (ite $cvcl_19 (ite (and $cvcl_53 (< x_33 3)) (+ x_33 1) x_33) x_33))) (flet ($cvcl_27 (= x_34 (ite $cvcl_20 (ite (and $cvcl_54 (< x_35 3)) (+ x_35 1) x_35) x_35))) (flet ($cvcl_29 (or x_11  $cvcl_21 )) (flet ($cvcl_31 (or x_12  $cvcl_22 )) (flet ($cvcl_33 (or x_29  $cvcl_23 )) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (<= x_17 2) (>= x_17 0)) (<= x_0 2)) (>= x_0 0)) (>= x_2 0)) (>= x_3 0)) (>= x_5 0)) (>= x_9 0)) (> x_10 0)) (>= x_10 0)) (>= x_18 0)) (>= x_19 0)) (>= x_20 0)) (>= x_26 0)) (>= x_27 0)) (or (or (or $cvcl_34  (= x_30 1) )  (= x_30 2) )  $cvcl_23 )) (not (< x_30 0))) (<= x_30 3)) (or (or (or (= x_31 0)  (= x_31 1) )  (= x_31 2) )  (= x_31 3) )) (not (< x_31 0))) (<= x_31 3)) (or (or (or $cvcl_30  (= x_32 1) )  (= x_32 2) )  $cvcl_21 )) (not (< x_32 0))) (<= x_32 3)) (or (or (or (= x_33 0)  (= x_33 1) )  (= x_33 2) )  (= x_33 3) )) (not (< x_33 0))) (<= x_33 3)) (or (or (or $cvcl_32  (= x_34 1) )  (= x_34 2) )  $cvcl_22 )) (not (< x_34 0))) (<= x_34 3)) (or (or (or (= x_35 0)  (= x_35 1) )  (= x_35 2) )  (= x_35 3) )) (not (< x_35 0))) (<= x_35 3)) (>= x_36 0)) (>= x_43 0)) (>= x_46 0)) (>= x_49 0)) (not (<= x_52 (* x_10 3)))) (>= x_52 0)) (>= x_54 0)) (>= x_55 0)) (>= x_56 0)) (or $cvcl_5  (and (or x_1  $cvcl_9 ) (or x_4  $cvcl_10 )) )) (or (not $cvcl_18)  (and $cvcl_2 $cvcl_0) )) (or $cvcl_3  (and $cvcl_1 $cvcl_0) )) (or (not $cvcl_69)  (and $cvcl_1 $cvcl_2) )) $cvcl_91) $cvcl_93) (< (- x_18 x_19) x_10)) (< (- x_18 x_20) x_10)) (not x_21)) (not x_22)) (or $cvcl_3  (and (and $cvcl_97 $cvcl_99) (not x_25)) )) (or (or $cvcl_3  $cvcl_40 )  (and $cvcl_98 $cvcl_100) )) (or $cvcl_90  (and $cvcl_7 $cvcl_4) )) (or $cvcl_8  (and $cvcl_6 $cvcl_4) )) (or $cvcl_5  (and $cvcl_6 $cvcl_7) )) (not (<= x_9 x_3))) (not (<= x_9 x_5))) (< (- x_9 x_3) x_10)) (< (- x_9 x_5) x_10)) $cvcl_19) $cvcl_20) (or $cvcl_8  (and (and $cvcl_70 $cvcl_73) $cvcl_76) )) (or (or $cvcl_8  $cvcl_89 )  (and $cvcl_9 $cvcl_10) )) (= x_44 (ite x_1 2 1))) (= x_45 (ite x_11 1 2))) (= x_47 (ite $cvcl_12 2 1))) (= x_48 (ite $cvcl_16 2 1))) (= x_50 (+ (ite $cvcl_14 (ite $cvcl_13 (ite $cvcl_12 3 2) x_47) (ite $cvcl_13 x_47 (ite $cvcl_12 1 0))) x_31))) (= x_51 (+ (ite $cvcl_14 (ite $cvcl_17 (ite $cvcl_16 3 2) x_48) (ite $cvcl_17 x_48 (ite $cvcl_16 1 0))) x_31))) (or (or (and (and (and (and (and (and (or (and (and (and (and (and (and (and (and (and (and $cvcl_24 $cvcl_25) $cvcl_52) $cvcl_26) $cvcl_27) (= x_30 (ite $cvcl_28 (ite (not (< x_50 3)) 3 x_50) x_31))) (iff x_21 $cvcl_29)) (iff x_22 $cvcl_31)) (iff x_28 $cvcl_33)) $cvcl_65) $cvcl_35)  (and (and (and (and (and (and (and (and (and (and $cvcl_24 (not $cvcl_25)) x_15) (= x_26 x_27)) $cvcl_26) $cvcl_27) (= x_30 (ite $cvcl_28 (ite (not (< x_51 3)) 3 x_51) x_31))) (iff x_21 (or $cvcl_29  $cvcl_30 ))) (iff x_22 (or $cvcl_31  $cvcl_32 ))) (iff x_28 (or $cvcl_33  $cvcl_34 ))) $cvcl_35) ) $cvcl_63) $cvcl_64) $cvcl_86) $cvcl_66) $cvcl_67) $cvcl_68)  (and (and (and (and (and (and (and (or (and (and (and (and (and (and (and (and (and (and (and $cvcl_56 (or (or (and (and (and (not $cvcl_41) $cvcl_47) $cvcl_46) $cvcl_42)  (and (and (and (not $cvcl_43) $cvcl_49) $cvcl_48) $cvcl_44) )  (and (and $cvcl_51 $cvcl_50) $cvcl_45) )) $cvcl_40) (or (or (or (or $cvcl_41  $cvcl_57 )  x_40 )  x_11 )  (not (< x_26 x_3)) )) (or (or (or (or $cvcl_43  $cvcl_58 )  x_42 )  x_12 )  (not (< x_26 x_5)) )) (or (or (or $cvcl_59  x_38 )  x_29 )  (not (< x_26 x_43)) )) (or (or (or (and (and (and (and $cvcl_46 $cvcl_47) $cvcl_42) $cvcl_71) $cvcl_72)  (and (and (and (and $cvcl_48 $cvcl_49) $cvcl_44) $cvcl_74) $cvcl_75) )  (and (and (and (and $cvcl_50 $cvcl_51) $cvcl_45) $cvcl_77) $cvcl_78) )  (and (< x_9 ?cvcl_60) $cvcl_79) )) (iff x_39 (or x_40  $cvcl_53 ))) (iff x_41 (or x_42  $cvcl_54 ))) (iff x_37 (or x_38  $cvcl_55 ))) $cvcl_61) $cvcl_62)  (and (and (and (and (and (and (and (and (and $cvcl_56 (or (or (or $cvcl_41  x_40 )  x_11 )  $cvcl_57 )) (or (or (or $cvcl_43  x_42 )  x_12 )  $cvcl_58 )) (or (or x_38  x_29 )  $cvcl_59 )) x_16) (= x_26 ?cvcl_60)) $cvcl_61) $cvcl_62) $cvcl_63) $cvcl_64) ) $cvcl_84) $cvcl_85) $cvcl_35) $cvcl_65) $cvcl_66) $cvcl_67) $cvcl_68) )  (and (and (and (and (and (and (and (or (and (and (and (and (and (and (and (and (and (and (and $cvcl_80 $cvcl_81) (not x_14)) (or (or (or $cvcl_41  x_1 )  x_11 )  (<= x_26 x_3) )) (or (or (or $cvcl_43  x_4 )  x_12 )  (<= x_26 x_5) )) (or (or x_13  x_29 )  (<= x_26 x_43) )) (or (or (or (and (and (and (and $cvcl_70 $cvcl_47) $cvcl_9) $cvcl_71) $cvcl_72)  (and (and (and (and $cvcl_73 $cvcl_49) $cvcl_10) $cvcl_74) $cvcl_75) )  (and (and (and $cvcl_76 $cvcl_51) $cvcl_77) $cvcl_78) )  $cvcl_79 )) (iff x_23 (or x_1  (= x_3 x_26) ))) (iff x_24 (or x_4  (= x_5 x_26) ))) (iff x_25 (or x_13  (= x_43 x_26) ))) $cvcl_82) $cvcl_83)  (and (and (and (and (and (and (and $cvcl_80 (not $cvcl_81)) x_14) $cvcl_82) $cvcl_83) (= x_26 x_2)) $cvcl_66) $cvcl_67) ) $cvcl_84) $cvcl_85) $cvcl_35) $cvcl_65) $cvcl_63) $cvcl_64) $cvcl_86) )) (or (or (and $cvcl_87 (= x_17 (ite (not x_7) x_0 1)))  (and $cvcl_88 (= x_17 (ite $cvcl_89 x_0 2))) )  (and (and $cvcl_90 $cvcl_8) (= x_17 x_0)) )) (or (and (and $cvcl_92 $cvcl_91) (not (<= x_19 ?cvcl_94)))  (and $cvcl_95 (= x_19 x_3)) )) (or (and (and $cvcl_92 $cvcl_93) (not (<= x_20 ?cvcl_94)))  (and $cvcl_95 (= x_20 x_5)) )) (or (and (and $cvcl_92 (= x_18 (+ x_9 x_52))) x_53)  (and (and $cvcl_95 (not x_53)) (= x_18 x_9)) )) (or (and (and (and (and $cvcl_96 (not (<= x_54 x_26))) (not (<= x_55 x_26))) (< x_54 x_55)) (< x_55 x_56))  (and (and (and (not $cvcl_96) (= x_54 x_43)) (= x_55 x_46)) (= x_56 x_49)) )) $cvcl_69) (or (and $cvcl_97 (not $cvcl_98))  (and $cvcl_99 (not $cvcl_100)) )))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
)
