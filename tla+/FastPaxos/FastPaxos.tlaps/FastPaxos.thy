(* automatically generated -- do not edit manually *)
theory FastPaxos imports Constant Zenon begin
ML_command {* writeln ("*** TLAPS PARSED\n"); *}
consts
  "isReal" :: c
  "isa_slas_a" :: "[c,c] => c"
  "isa_bksl_diva" :: "[c,c] => c"
  "isa_perc_a" :: "[c,c] => c"
  "isa_peri_peri_a" :: "[c,c] => c"
  "isInfinity" :: c
  "isa_lbrk_rbrk_a" :: "[c] => c"
  "isa_less_more_a" :: "[c] => c"

lemma ob'25:
fixes Acceptors
fixes Values
fixes Quorums
fixes msgs msgs'
fixes maxBal maxBal'
fixes maxVBal maxVBal'
fixes maxVal maxVal'
(* usable definition vars suppressed *)
(* usable definition None suppressed *)
(* usable definition Init suppressed *)
(* usable definition Phase1a suppressed *)
(* usable definition Phase1b suppressed *)
(* usable definition Phase2a suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition VotedForIn suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition Chosen suppressed *)
(* usable definition Consistency suppressed *)
(* usable definition Messages suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition WontVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition MsgInv suppressed *)
(* usable definition AccInv suppressed *)
assumes v'32: "(((((TypeOK) \<and> (MsgInv))) \<and> (AccInv)))"
assumes v'33: "(Next)"
assumes v'34: "((a_hef12f5554781c2213604492856f635a :: c))"
fixes v
assumes v_in : "(v \<in> (Values))"
fixes b
assumes b_in : "(b \<in> (Nat))"
assumes v'37: "((SafeAt ((v), (b))))"
fixes a
assumes a_in : "(a \<in> (Acceptors))"
assumes v'49: "(\<exists> m \<in> (msgs) : ((((fapply ((m), (''type''))) = (''2a''))) & ((geq ((fapply ((m), (''bal''))), (fapply ((maxBal), (a)))))) & ((((a_msgshash_primea :: c)) = (((msgs) \<union> ({(((''type'' :> (''2b'')) @@ (''bal'' :> (fapply ((m), (''bal'')))) @@ (''val'' :> (fapply ((m), (''val'')))) @@ (''acc'' :> (a))))}))))) & ((((a_maxVBalhash_primea :: c)) = ([(maxVBal) EXCEPT ![(a)] = (fapply ((m), (''bal'')))]))) & ((((a_maxBalhash_primea :: c)) = ([(maxBal) EXCEPT ![(a)] = (fapply ((m), (''bal'')))]))) & ((((a_maxValhash_primea :: c)) = ([(maxVal) EXCEPT ![(a)] = (fapply ((m), (''val'')))])))))"
shows "(\<exists> m \<in> (msgs) : ((((fapply ((m), (''type''))) = (''2a''))) & ((geq ((fapply ((m), (''bal''))), (fapply ((maxBal), (a)))))) & ((((a_msgshash_primea :: c)) = (((msgs) \<union> ({(((''type'' :> (''2b'')) @@ (''bal'' :> (fapply ((m), (''bal'')))) @@ (''val'' :> (fapply ((m), (''val'')))) @@ (''acc'' :> (a))))}))))) & ((((a_maxVBalhash_primea :: c)) = ([(maxVBal) EXCEPT ![(a)] = (fapply ((m), (''bal'')))]))) & ((((a_maxBalhash_primea :: c)) = ([(maxBal) EXCEPT ![(a)] = (fapply ((m), (''bal'')))]))) & ((((a_maxValhash_primea :: c)) = ([(maxVal) EXCEPT ![(a)] = (fapply ((m), (''val'')))])))))"(is "PROP ?ob'25")
proof -
ML_command {* writeln "*** TLAPS ENTER 25"; *}
show "PROP ?ob'25"

(* BEGIN ZENON INPUT
;; file=FastPaxos.tlaps/tlapm_ce7197.znn; PATH='/home/alexis51151/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/home/alexis51151/.local/bin:/home/alexis51151/Ecole/EPaxos/toolbox:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >FastPaxos.tlaps/tlapm_ce7197.znn.out
;; obligation #25
$hyp "v'32" (/\ (/\ TypeOK MsgInv)
AccInv)
$hyp "v'33" Next
$hyp "v'34" a_hef12f5554781c2213604492856f635a
$hyp "v_in" (TLA.in v Values)
$hyp "b_in" (TLA.in b arith.N)
$hyp "v'37" (SafeAt v
b)
$hyp "a_in" (TLA.in a Acceptors)
$hyp "v'49" (TLA.bEx msgs ((m) (/\ (= (TLA.fapply m "type") "2a")
(arith.le (TLA.fapply maxBal a) (TLA.fapply m "bal")) (= a_msgshash_primea
(TLA.cup msgs
(TLA.set (TLA.record "type" "2b" "bal" (TLA.fapply m "bal") "val" (TLA.fapply m "val") "acc" a))))
(= a_maxVBalhash_primea (TLA.except maxVBal a (TLA.fapply m "bal")))
(= a_maxBalhash_primea (TLA.except maxBal a (TLA.fapply m "bal")))
(= a_maxValhash_primea
(TLA.except maxVal a (TLA.fapply m "val"))))))
$goal (TLA.bEx msgs ((m) (/\ (= (TLA.fapply m "type") "2a")
(arith.le (TLA.fapply maxBal a) (TLA.fapply m "bal")) (= a_msgshash_primea
(TLA.cup msgs
(TLA.set (TLA.record "type" "2b" "bal" (TLA.fapply m "bal") "val" (TLA.fapply m "val") "acc" a))))
(= a_maxVBalhash_primea (TLA.except maxVBal a (TLA.fapply m "bal")))
(= a_maxBalhash_primea (TLA.except maxBal a (TLA.fapply m "bal")))
(= a_maxValhash_primea
(TLA.except maxVal a (TLA.fapply m "val"))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hh:"bEx(msgs, (\<lambda>m. (((m[''type''])=''2a'')&(((maxBal[a]) <= (m[''bal'']))&((a_msgshash_primea=(msgs \\cup {(''type'' :> (''2b'') @@ ''bal'' :> ((m[''bal''])) @@ ''val'' :> ((m[''val''])) @@ ''acc'' :> (a))}))&((a_maxVBalhash_primea=except(maxVBal, a, (m[''bal''])))&((a_maxBalhash_primea=except(maxBal, a, (m[''bal''])))&(a_maxValhash_primea=except(maxVal, a, (m[''val'']))))))))))" (is "?z_hh")
 using v'49 by blast
 assume z_Hi:"(~?z_hh)"
 show FALSE
 by (rule notE [OF z_Hi z_Hh])
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 25"; *} qed
lemma ob'70:
fixes Acceptors
fixes Values
fixes Quorums
fixes msgs msgs'
fixes maxBal maxBal'
fixes maxVBal maxVBal'
fixes maxVal maxVal'
(* usable definition vars suppressed *)
(* usable definition Send suppressed *)
(* usable definition None suppressed *)
(* usable definition Init suppressed *)
(* usable definition Phase1a suppressed *)
(* usable definition Phase1b suppressed *)
(* usable definition Phase2b suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition VotedForIn suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition Chosen suppressed *)
(* usable definition Consistency suppressed *)
(* usable definition Messages suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition WontVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition MsgInv suppressed *)
(* usable definition AccInv suppressed *)
assumes v'37: "(((((TypeOK) \<and> (MsgInv))) \<and> (AccInv)))"
assumes v'38: "(Next)"
fixes b
assumes b_in : "(b \<in> (Nat))"
assumes v'50: "(((~ (\<exists> m \<in> (msgs) : (((((fapply ((m), (''type''))) = (''2a''))) \<and> (((fapply ((m), (''bal''))) = (b)))))))) & (\<exists> v \<in> (Values) : (((\<exists> Q \<in> ((Quorums ((b)))) : (\<exists> S \<in> ((SUBSET (subsetOf((msgs), %m. (((((fapply ((m), (''type''))) = (''1b''))) \<and> (((fapply ((m), (''bal''))) = (b))))))))) : ((\<forall> a \<in> (Q) : (\<exists> m \<in> (S) : (((fapply ((m), (''acc''))) = (a))))) & ((\<forall> m \<in> (S) : (((fapply ((m), (''maxVBal''))) = ((minus (((Succ[0])))))))) | (\<exists> a_ca \<in> ((isa_peri_peri_a (((0)), ((arith_add ((b), ((minus (((Succ[0]))))))))))) : ((\<forall> m \<in> (S) : ((leq ((fapply ((m), (''maxVBal''))), (a_ca))))) & (\<exists> m \<in> (S) : ((((fapply ((m), (''maxVBal''))) = (a_ca))) & (((fapply ((m), (''maxVal''))) = (v))))))))))) | (((b) = ((0))))) & ((Send ((((''type'' :> (''2a'')) @@ (''bal'' :> (b)) @@ (''val'' :> (v))))))))))"
assumes v'51: "((((a_maxBalhash_primea :: c)) = (maxBal)))"
assumes v'52: "((((a_maxVBalhash_primea :: c)) = (maxVBal)))"
assumes v'53: "((((a_maxValhash_primea :: c)) = (maxVal)))"
shows "(\<exists> v \<in> (Values) : (((Send ((((''type'' :> (''2a'')) @@ (''bal'' :> (b)) @@ (''val'' :> (v))))))) & (((((a_maxBalhash_primea :: c)) = (maxBal))) & ((((a_maxVBalhash_primea :: c)) = (maxVBal))) & ((((a_maxValhash_primea :: c)) = (maxVal))))))"(is "PROP ?ob'70")
proof -
ML_command {* writeln "*** TLAPS ENTER 70"; *}
show "PROP ?ob'70"

(* BEGIN ZENON INPUT
;; file=FastPaxos.tlaps/tlapm_62264a.znn; PATH='/home/alexis51151/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/home/alexis51151/.local/bin:/home/alexis51151/Ecole/EPaxos/toolbox:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >FastPaxos.tlaps/tlapm_62264a.znn.out
;; obligation #70
$hyp "v'37" (/\ (/\ TypeOK MsgInv)
AccInv)
$hyp "v'38" Next
$hyp "b_in" (TLA.in b arith.N)
$hyp "v'50" (/\ (-. (TLA.bEx msgs ((m) (/\ (= (TLA.fapply m "type") "2a")
(= (TLA.fapply m "bal") b)))))
(TLA.bEx Values ((v) (/\ (\/ (TLA.bEx (Quorums b) ((Q) (TLA.bEx (TLA.SUBSET (TLA.subsetOf msgs ((m) (/\ (= (TLA.fapply m "type")
"1b") (= (TLA.fapply m "bal")
b))))) ((S) (/\ (TLA.bAll Q ((a) (TLA.bEx S ((m) (= (TLA.fapply m "acc")
a))))) (\/ (TLA.bAll S ((m) (= (TLA.fapply m "maxVBal")
(arith.minus (TLA.fapply TLA.Succ 0))))) (TLA.bEx (arith.intrange 0
(arith.add b
(arith.minus (TLA.fapply TLA.Succ 0)))) ((a_ca) (/\ (TLA.bAll S ((m) (arith.le (TLA.fapply m "maxVBal")
a_ca))) (TLA.bEx S ((m) (/\ (= (TLA.fapply m "maxVBal") a_ca)
(= (TLA.fapply m "maxVal") v))))))))))))) (= b 0))
(Send (TLA.record "type" "2a" "bal" b "val" v))))))
$hyp "v'51" (= a_maxBalhash_primea maxBal)
$hyp "v'52" (= a_maxVBalhash_primea
maxVBal)
$hyp "v'53" (= a_maxValhash_primea
maxVal)
$goal (TLA.bEx Values ((v) (/\ (Send (TLA.record "type" "2a" "bal" b "val" v))
(/\ (= a_maxBalhash_primea maxBal) (= a_maxVBalhash_primea maxVBal)
(= a_maxValhash_primea
maxVal)))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_He:"(a_maxBalhash_primea=maxBal)"
 using v'51 by blast
 have z_Hf:"(a_maxVBalhash_primea=maxVBal)"
 using v'52 by blast
 have z_Hg:"(a_maxValhash_primea=maxVal)"
 using v'53 by blast
 have z_Hd:"((~bEx(msgs, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=b)))))&bEx(Values, (\<lambda>v. ((bEx(Quorums(b), (\<lambda>Q. bEx(SUBSET(subsetOf(msgs, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=b))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''acc''])=a)))))&(bAll(S, (\<lambda>m. ((m[''maxVBal''])= -.(1))))|bEx(isa'dotdot(0, (b +  -.(1))), (\<lambda>a_ca. (bAll(S, (\<lambda>m. ((m[''maxVBal'']) <= a_ca)))&bEx(S, (\<lambda>m. (((m[''maxVBal''])=a_ca)&((m[''maxVal''])=v)))))))))))))|(b=0))&Send((''type'' :> (''2a'') @@ ''bal'' :> (b) @@ ''val'' :> (v)))))))" (is "?z_ho&?z_hbc")
 using v'50 by blast
 have zenon_L1_: "(a_maxValhash_primea=maxVal) ==> (a_maxValhash_primea~=maxVal) ==> FALSE" (is "?z_hg ==> ?z_hdh ==> FALSE")
 proof -
  assume z_Hg:"?z_hg"
  assume z_Hdh:"?z_hdh"
  show FALSE
  by (rule notE [OF z_Hdh z_Hg])
 qed
 assume z_Hh:"(~bEx(Values, (\<lambda>v. (Send((''type'' :> (''2a'') @@ ''bal'' :> (b) @@ ''val'' :> (v)))&((a_maxBalhash_primea=maxBal)&((a_maxVBalhash_primea=maxVBal)&(a_maxValhash_primea=maxVal)))))))" (is "~?z_hdi")
 have z_Hbc: "?z_hbc"
 by (rule zenon_and_1 [OF z_Hd])
 have z_Hdn_z_Hbc: "(\\E x:((x \\in Values)&((bEx(Quorums(b), (\<lambda>Q. bEx(SUBSET(subsetOf(msgs, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=b))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''acc''])=a)))))&(bAll(S, (\<lambda>m. ((m[''maxVBal''])= -.(1))))|bEx(isa'dotdot(0, (b +  -.(1))), (\<lambda>a_ca. (bAll(S, (\<lambda>m. ((m[''maxVBal'']) <= a_ca)))&bEx(S, (\<lambda>m. (((m[''maxVBal''])=a_ca)&((m[''maxVal''])=x)))))))))))))|(b=0))&Send((''type'' :> (''2a'') @@ ''bal'' :> (b) @@ ''val'' :> (x)))))) == ?z_hbc" (is "?z_hdn == _")
 by (unfold bEx_def)
 have z_Hdn: "?z_hdn" (is "\\E x : ?z_hei(x)")
 by (unfold z_Hdn_z_Hbc, fact z_Hbc)
 have z_Hej: "?z_hei((CHOOSE x:((x \\in Values)&((bEx(Quorums(b), (\<lambda>Q. bEx(SUBSET(subsetOf(msgs, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=b))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''acc''])=a)))))&(bAll(S, (\<lambda>m. ((m[''maxVBal''])= -.(1))))|bEx(isa'dotdot(0, (b +  -.(1))), (\<lambda>a_ca. (bAll(S, (\<lambda>m. ((m[''maxVBal'']) <= a_ca)))&bEx(S, (\<lambda>m. (((m[''maxVBal''])=a_ca)&((m[''maxVal''])=x)))))))))))))|(b=0))&Send((''type'' :> (''2a'') @@ ''bal'' :> (b) @@ ''val'' :> (x)))))))" (is "?z_hel&?z_hem")
 by (rule zenon_ex_choose_0 [of "?z_hei", OF z_Hdn])
 have z_Hel: "?z_hel"
 by (rule zenon_and_0 [OF z_Hej])
 have z_Hem: "?z_hem" (is "?z_hen&?z_heo")
 by (rule zenon_and_1 [OF z_Hej])
 have z_Heo: "?z_heo"
 by (rule zenon_and_1 [OF z_Hem])
 have z_Hep_z_Hh: "(~(\\E x:((x \\in Values)&(Send((''type'' :> (''2a'') @@ ''bal'' :> (b) @@ ''val'' :> (x)))&((a_maxBalhash_primea=maxBal)&((a_maxVBalhash_primea=maxVBal)&(a_maxValhash_primea=maxVal))))))) == (~?z_hdi)" (is "?z_hep == ?z_hh")
 by (unfold bEx_def)
 have z_Hep: "?z_hep" (is "~(\\E x : ?z_het(x))")
 by (unfold z_Hep_z_Hh, fact z_Hh)
 have z_Heu: "~?z_het((CHOOSE x:((x \\in Values)&((bEx(Quorums(b), (\<lambda>Q. bEx(SUBSET(subsetOf(msgs, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=b))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''acc''])=a)))))&(bAll(S, (\<lambda>m. ((m[''maxVBal''])= -.(1))))|bEx(isa'dotdot(0, (b +  -.(1))), (\<lambda>a_ca. (bAll(S, (\<lambda>m. ((m[''maxVBal'']) <= a_ca)))&bEx(S, (\<lambda>m. (((m[''maxVBal''])=a_ca)&((m[''maxVal''])=x)))))))))))))|(b=0))&Send((''type'' :> (''2a'') @@ ''bal'' :> (b) @@ ''val'' :> (x)))))))" (is "~(_&?z_hev)")
 by (rule zenon_notex_0 [of "?z_het" "(CHOOSE x:((x \\in Values)&((bEx(Quorums(b), (\<lambda>Q. bEx(SUBSET(subsetOf(msgs, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=b))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''acc''])=a)))))&(bAll(S, (\<lambda>m. ((m[''maxVBal''])= -.(1))))|bEx(isa'dotdot(0, (b +  -.(1))), (\<lambda>a_ca. (bAll(S, (\<lambda>m. ((m[''maxVBal'']) <= a_ca)))&bEx(S, (\<lambda>m. (((m[''maxVBal''])=a_ca)&((m[''maxVal''])=x)))))))))))))|(b=0))&Send((''type'' :> (''2a'') @@ ''bal'' :> (b) @@ ''val'' :> (x))))))", OF z_Hep])
 show FALSE
 proof (rule zenon_notand [OF z_Heu])
  assume z_Hew:"(~?z_hel)"
  show FALSE
  by (rule notE [OF z_Hew z_Hel])
 next
  assume z_Hex:"(~?z_hev)" (is "~(_&?z_hdl)")
  show FALSE
  proof (rule zenon_notand [OF z_Hex])
   assume z_Hey:"(~?z_heo)"
   show FALSE
   by (rule notE [OF z_Hey z_Heo])
  next
   assume z_Hez:"(~?z_hdl)" (is "~(?z_he&?z_hdm)")
   show FALSE
   proof (rule zenon_notand [OF z_Hez])
    assume z_Hfa:"(a_maxBalhash_primea~=maxBal)"
    show FALSE
    by (rule notE [OF z_Hfa z_He])
   next
    assume z_Hfb:"(~?z_hdm)" (is "~(?z_hf&?z_hg)")
    show FALSE
    proof (rule zenon_notand [OF z_Hfb])
     assume z_Hfc:"(a_maxVBalhash_primea~=maxVBal)"
     show FALSE
     by (rule notE [OF z_Hfc z_Hf])
    next
     assume z_Hdh:"(a_maxValhash_primea~=maxVal)"
     show FALSE
     by (rule notE [OF z_Hdh z_Hg])
    qed
   qed
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 70"; *} qed
lemma ob'53:
fixes Acceptors
fixes Values
fixes Quorums
fixes msgs msgs'
fixes maxBal maxBal'
fixes maxVBal maxVBal'
fixes maxVal maxVal'
(* usable definition vars suppressed *)
(* usable definition Send suppressed *)
(* usable definition None suppressed *)
(* usable definition Phase1a suppressed *)
(* usable definition Phase1b suppressed *)
(* usable definition Phase2a suppressed *)
(* usable definition Phase2b suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition Chosen suppressed *)
(* usable definition Consistency suppressed *)
(* usable definition Messages suppressed *)
(* usable definition WontVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
shows "((((((msgs) = ({}))) & (((maxVBal) = ([ a \<in> (Acceptors)  \<mapsto> ((minus (((Succ[0])))))]))) & (((maxBal) = ([ a \<in> (Acceptors)  \<mapsto> ((minus (((Succ[0])))))]))) & (((maxVal) = ([ a \<in> (Acceptors)  \<mapsto> (None)])))) \<Rightarrow> ((((((((msgs) \<in> ((SUBSET (Messages))))) & (((maxVBal) \<in> ([(Acceptors) \<rightarrow> (((Nat) \<union> ({((minus (((Succ[0])))))})))]))) & (((maxBal) \<in> ([(Acceptors) \<rightarrow> (((Nat) \<union> ({((minus (((Succ[0])))))})))]))) & (((maxVal) \<in> ([(Acceptors) \<rightarrow> (((Values) \<union> ({(None)})))]))) & (\<forall> a \<in> (Acceptors) : ((geq ((fapply ((maxBal), (a))), (fapply ((maxVBal), (a)))))))) \<and> (\<forall> m \<in> (msgs) : ((((((fapply ((m), (''type''))) = (''1b''))) \<Rightarrow> (((leq ((fapply ((m), (''bal''))), (fapply ((maxBal), (fapply ((m), (''acc'')))))))) & (((((fapply ((m), (''maxVal''))) \<in> (Values))) & (((fapply ((m), (''maxVBal''))) \<in> (Nat))) & (\<exists> m_1 \<in> (msgs) : ((((fapply ((m_1), (''type''))) = (''2b''))) & (((fapply ((m_1), (''val''))) = (fapply ((m), (''maxVal''))))) & (((fapply ((m_1), (''bal''))) = (fapply ((m), (''maxVBal''))))) & (((fapply ((m_1), (''acc''))) = (fapply ((m), (''acc'')))))))) | ((((fapply ((m), (''maxVal''))) = (None))) & (((fapply ((m), (''maxVBal''))) = ((minus (((Succ[0]))))))))) & (\<forall> a_ca \<in> ((isa_peri_peri_a (((arith_add ((fapply ((m), (''maxVBal''))), ((Succ[0]))))), ((arith_add ((fapply ((m), (''bal''))), ((minus (((Succ[0]))))))))))) : ((~ (\<exists> v \<in> (Values) : (\<exists> m_1 \<in> (msgs) : ((((fapply ((m_1), (''type''))) = (''2b''))) & (((fapply ((m_1), (''val''))) = (v))) & (((fapply ((m_1), (''bal''))) = (a_ca))) & (((fapply ((m_1), (''acc''))) = (fapply ((m), (''acc'')))))))))))))) & (((((fapply ((m), (''type''))) = (''2a''))) \<Rightarrow> (((SafeAt ((fapply ((m), (''val''))), (fapply ((m), (''bal'')))))) & (\<forall> ma \<in> (msgs) : (((((((fapply ((ma), (''type''))) = (''2a''))) \<and> (((fapply ((ma), (''bal''))) = (fapply ((m), (''bal''))))))) \<Rightarrow> (((ma) = (m))))))))) & (((((fapply ((m), (''type''))) = (''2b''))) \<Rightarrow> ((\<exists> ma \<in> (msgs) : ((((fapply ((ma), (''type''))) = (''2a''))) & (((fapply ((ma), (''bal''))) = (fapply ((m), (''bal''))))) & (((fapply ((ma), (''val''))) = (fapply ((m), (''val''))))))) & ((leq ((fapply ((m), (''bal''))), (fapply ((maxVBal), (fapply ((m), (''acc''))))))))))))))) \<and> (\<forall> a \<in> (Acceptors) : ((((((fapply ((maxVal), (a))) = (None))) \<Leftrightarrow> (((fapply ((maxVBal), (a))) = ((minus (((Succ[0]))))))))) & ((leq ((fapply ((maxVBal), (a))), (fapply ((maxBal), (a)))))) & ((((geq ((fapply ((maxVBal), (a))), ((0))))) \<Rightarrow> (\<exists> m \<in> (msgs) : ((((fapply ((m), (''type''))) = (''2b''))) & (((fapply ((m), (''val''))) = (fapply ((maxVal), (a))))) & (((fapply ((m), (''bal''))) = (fapply ((maxVBal), (a))))) & (((fapply ((m), (''acc''))) = (a))))))) & (\<forall> a_ca \<in> (Nat) : ((((greater ((a_ca), (fapply ((maxVBal), (a)))))) \<Rightarrow> ((~ (\<exists> v \<in> (Values) : (\<exists> m \<in> (msgs) : ((((fapply ((m), (''type''))) = (''2b''))) & (((fapply ((m), (''val''))) = (v))) & (((fapply ((m), (''bal''))) = (a_ca))) & (((fapply ((m), (''acc''))) = (a)))))))))))))))))"(is "PROP ?ob'53")
proof -
ML_command {* writeln "*** TLAPS ENTER 53"; *}
show "PROP ?ob'53"
using assms by auto
ML_command {* writeln "*** TLAPS EXIT 53"; *} qed
lemma ob'78:
fixes Acceptors
fixes Values
fixes Quorums
fixes msgs msgs'
fixes maxBal maxBal'
fixes maxVBal maxVBal'
fixes maxVal maxVal'
(* usable definition vars suppressed *)
(* usable definition Send suppressed *)
(* usable definition None suppressed *)
(* usable definition Init suppressed *)
(* usable definition Phase1a suppressed *)
(* usable definition Phase1b suppressed *)
(* usable definition Phase2a suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition VotedForIn suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition Chosen suppressed *)
(* usable definition Consistency suppressed *)
(* usable definition Messages suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition WontVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition MsgInv suppressed *)
(* usable definition AccInv suppressed *)
assumes v'37: "(((((TypeOK) \<and> (MsgInv))) \<and> (AccInv)))"
assumes v'38: "(Next)"
fixes a
assumes a_in : "(a \<in> (Acceptors))"
assumes v'52: "(\<exists> m \<in> (msgs) : ((((fapply ((m), (''type''))) = (''2a''))) & ((geq ((fapply ((m), (''bal''))), (fapply ((maxBal), (a)))))) & ((Send ((((''type'' :> (''2b'')) @@ (''bal'' :> (fapply ((m), (''bal'')))) @@ (''val'' :> (fapply ((m), (''val'')))) @@ (''acc'' :> (a))))))) & ((((a_maxVBalhash_primea :: c)) = ([(maxVBal) EXCEPT ![(a)] = (fapply ((m), (''bal'')))]))) & ((((a_maxBalhash_primea :: c)) = ([(maxBal) EXCEPT ![(a)] = (fapply ((m), (''bal'')))]))) & ((((a_maxValhash_primea :: c)) = ([(maxVal) EXCEPT ![(a)] = (fapply ((m), (''val'')))])))))"
shows "(\<exists> m \<in> (msgs) : ((((fapply ((m), (''type''))) = (''2a''))) & ((geq ((fapply ((m), (''bal''))), (fapply ((maxBal), (a)))))) & ((Send ((((''type'' :> (''2b'')) @@ (''bal'' :> (fapply ((m), (''bal'')))) @@ (''val'' :> (fapply ((m), (''val'')))) @@ (''acc'' :> (a))))))) & ((((a_maxVBalhash_primea :: c)) = ([(maxVBal) EXCEPT ![(a)] = (fapply ((m), (''bal'')))]))) & ((((a_maxBalhash_primea :: c)) = ([(maxBal) EXCEPT ![(a)] = (fapply ((m), (''bal'')))]))) & ((((a_maxValhash_primea :: c)) = ([(maxVal) EXCEPT ![(a)] = (fapply ((m), (''val'')))])))))"(is "PROP ?ob'78")
proof -
ML_command {* writeln "*** TLAPS ENTER 78"; *}
show "PROP ?ob'78"

(* BEGIN ZENON INPUT
;; file=FastPaxos.tlaps/tlapm_1039ce.znn; PATH='/home/alexis51151/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/home/alexis51151/.local/bin:/home/alexis51151/Ecole/EPaxos/toolbox:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >FastPaxos.tlaps/tlapm_1039ce.znn.out
;; obligation #78
$hyp "v'37" (/\ (/\ TypeOK MsgInv)
AccInv)
$hyp "v'38" Next
$hyp "a_in" (TLA.in a Acceptors)
$hyp "v'52" (TLA.bEx msgs ((m) (/\ (= (TLA.fapply m "type") "2a")
(arith.le (TLA.fapply maxBal a) (TLA.fapply m "bal"))
(Send (TLA.record "type" "2b" "bal" (TLA.fapply m "bal") "val" (TLA.fapply m "val") "acc" a))
(= a_maxVBalhash_primea (TLA.except maxVBal a (TLA.fapply m "bal")))
(= a_maxBalhash_primea (TLA.except maxBal a (TLA.fapply m "bal")))
(= a_maxValhash_primea
(TLA.except maxVal a (TLA.fapply m "val"))))))
$goal (TLA.bEx msgs ((m) (/\ (= (TLA.fapply m "type") "2a")
(arith.le (TLA.fapply maxBal a) (TLA.fapply m "bal"))
(Send (TLA.record "type" "2b" "bal" (TLA.fapply m "bal") "val" (TLA.fapply m "val") "acc" a))
(= a_maxVBalhash_primea (TLA.except maxVBal a (TLA.fapply m "bal")))
(= a_maxBalhash_primea (TLA.except maxBal a (TLA.fapply m "bal")))
(= a_maxValhash_primea
(TLA.except maxVal a (TLA.fapply m "val"))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hd:"bEx(msgs, (\<lambda>m. (((m[''type''])=''2a'')&(((maxBal[a]) <= (m[''bal'']))&(Send((''type'' :> (''2b'') @@ ''bal'' :> ((m[''bal''])) @@ ''val'' :> ((m[''val''])) @@ ''acc'' :> (a)))&((a_maxVBalhash_primea=except(maxVBal, a, (m[''bal''])))&((a_maxBalhash_primea=except(maxBal, a, (m[''bal''])))&(a_maxValhash_primea=except(maxVal, a, (m[''val'']))))))))))" (is "?z_hd")
 using v'52 by blast
 assume z_He:"(~?z_hd)"
 show FALSE
 by (rule notE [OF z_He z_Hd])
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 78"; *} qed
lemma ob'74:
fixes Acceptors
fixes Values
fixes Quorums
fixes msgs msgs'
fixes maxBal maxBal'
fixes maxVBal maxVBal'
fixes maxVal maxVal'
(* usable definition vars suppressed *)
(* usable definition Send suppressed *)
(* usable definition None suppressed *)
(* usable definition Init suppressed *)
(* usable definition Phase1a suppressed *)
(* usable definition Phase2a suppressed *)
(* usable definition Phase2b suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition VotedForIn suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition Chosen suppressed *)
(* usable definition Consistency suppressed *)
(* usable definition Messages suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition WontVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition MsgInv suppressed *)
(* usable definition AccInv suppressed *)
assumes v'37: "(((((TypeOK) \<and> (MsgInv))) \<and> (AccInv)))"
assumes v'38: "(Next)"
fixes a
assumes a_in : "(a \<in> (Acceptors))"
assumes v'51: "(\<exists> m \<in> (msgs) : ((((fapply ((m), (''type''))) = (''1a''))) & ((greater ((fapply ((m), (''bal''))), (fapply ((maxBal), (a)))))) & ((Send ((((''type'' :> (''1b'')) @@ (''bal'' :> (fapply ((m), (''bal'')))) @@ (''maxVBal'' :> (fapply ((maxVBal), (a)))) @@ (''maxVal'' :> (fapply ((maxVal), (a)))) @@ (''acc'' :> (a))))))) & ((((a_maxBalhash_primea :: c)) = ([(maxBal) EXCEPT ![(a)] = (fapply ((m), (''bal'')))]))) & (((((a_maxVBalhash_primea :: c)) = (maxVBal))) & ((((a_maxValhash_primea :: c)) = (maxVal))))))"
shows "(\<exists> m \<in> (msgs) : ((((fapply ((m), (''type''))) = (''1a''))) & ((greater ((fapply ((m), (''bal''))), (fapply ((maxBal), (a)))))) & ((Send ((((''type'' :> (''1b'')) @@ (''bal'' :> (fapply ((m), (''bal'')))) @@ (''maxVBal'' :> (fapply ((maxVBal), (a)))) @@ (''maxVal'' :> (fapply ((maxVal), (a)))) @@ (''acc'' :> (a))))))) & ((((a_maxBalhash_primea :: c)) = ([(maxBal) EXCEPT ![(a)] = (fapply ((m), (''bal'')))]))) & (((((a_maxVBalhash_primea :: c)) = (maxVBal))) & ((((a_maxValhash_primea :: c)) = (maxVal))))))"(is "PROP ?ob'74")
proof -
ML_command {* writeln "*** TLAPS ENTER 74"; *}
show "PROP ?ob'74"

(* BEGIN ZENON INPUT
;; file=FastPaxos.tlaps/tlapm_6d965b.znn; PATH='/home/alexis51151/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/home/alexis51151/.local/bin:/home/alexis51151/Ecole/EPaxos/toolbox:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >FastPaxos.tlaps/tlapm_6d965b.znn.out
;; obligation #74
$hyp "v'37" (/\ (/\ TypeOK MsgInv)
AccInv)
$hyp "v'38" Next
$hyp "a_in" (TLA.in a Acceptors)
$hyp "v'51" (TLA.bEx msgs ((m) (/\ (= (TLA.fapply m "type") "1a")
(arith.lt (TLA.fapply maxBal a) (TLA.fapply m "bal"))
(Send (TLA.record "type" "1b" "bal" (TLA.fapply m "bal") "maxVBal" (TLA.fapply maxVBal a) "maxVal" (TLA.fapply maxVal a) "acc" a))
(= a_maxBalhash_primea (TLA.except maxBal a (TLA.fapply m "bal")))
(/\ (= a_maxVBalhash_primea maxVBal) (= a_maxValhash_primea
maxVal)))))
$goal (TLA.bEx msgs ((m) (/\ (= (TLA.fapply m "type") "1a")
(arith.lt (TLA.fapply maxBal a) (TLA.fapply m "bal"))
(Send (TLA.record "type" "1b" "bal" (TLA.fapply m "bal") "maxVBal" (TLA.fapply maxVBal a) "maxVal" (TLA.fapply maxVal a) "acc" a))
(= a_maxBalhash_primea (TLA.except maxBal a (TLA.fapply m "bal")))
(/\ (= a_maxVBalhash_primea maxVBal) (= a_maxValhash_primea
maxVal)))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hd:"bEx(msgs, (\<lambda>m. (((m[''type''])=''1a'')&(((maxBal[a]) < (m[''bal'']))&(Send((''type'' :> (''1b'') @@ ''bal'' :> ((m[''bal''])) @@ ''maxVBal'' :> ((maxVBal[a])) @@ ''maxVal'' :> ((maxVal[a])) @@ ''acc'' :> (a)))&((a_maxBalhash_primea=except(maxBal, a, (m[''bal''])))&((a_maxVBalhash_primea=maxVBal)&(a_maxValhash_primea=maxVal))))))))" (is "?z_hd")
 using v'51 by blast
 assume z_He:"(~?z_hd)"
 show FALSE
 by (rule notE [OF z_He z_Hd])
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 74"; *} qed
lemma ob'155:
fixes Acceptors
fixes Values
fixes Quorums
fixes msgs msgs'
fixes maxBal maxBal'
fixes maxVBal maxVBal'
fixes maxVal maxVal'
(* usable definition vars suppressed *)
(* usable definition Send suppressed *)
(* usable definition None suppressed *)
(* usable definition Init suppressed *)
(* usable definition Phase1a suppressed *)
(* usable definition Phase1b suppressed *)
(* usable definition Phase2b suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition VotedForIn suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition Chosen suppressed *)
(* usable definition Consistency suppressed *)
(* usable definition Messages suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition WontVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition MsgInv suppressed *)
(* usable definition AccInv suppressed *)
assumes v'37: "(((((TypeOK) \<and> (MsgInv))) \<and> (AccInv)))"
assumes v'38: "(Next)"
fixes b
assumes b_in : "(b \<in> (Nat))"
assumes v'53: "(((~ (\<exists> m \<in> (msgs) : (((((fapply ((m), (''type''))) = (''2a''))) \<and> (((fapply ((m), (''bal''))) = (b)))))))) & (\<exists> v \<in> (Values) : (((\<exists> Q \<in> ((Quorums ((b)))) : (\<exists> S \<in> ((SUBSET (subsetOf((msgs), %m. (((((fapply ((m), (''type''))) = (''1b''))) \<and> (((fapply ((m), (''bal''))) = (b))))))))) : ((\<forall> a \<in> (Q) : (\<exists> m \<in> (S) : (((fapply ((m), (''acc''))) = (a))))) & ((\<forall> m \<in> (S) : (((fapply ((m), (''maxVBal''))) = ((minus (((Succ[0])))))))) | (\<exists> a_ca \<in> ((isa_peri_peri_a (((0)), ((arith_add ((b), ((minus (((Succ[0]))))))))))) : ((\<forall> m \<in> (S) : ((leq ((fapply ((m), (''maxVBal''))), (a_ca))))) & (\<exists> m \<in> (S) : ((((fapply ((m), (''maxVBal''))) = (a_ca))) & (((fapply ((m), (''maxVal''))) = (v))))))))))) | (((b) = ((0))))) & ((Send ((((''type'' :> (''2a'')) @@ (''bal'' :> (b)) @@ (''val'' :> (v))))))))))"
assumes v'54: "((((a_maxBalhash_primea :: c)) = (maxBal)))"
assumes v'55: "((((a_maxVBalhash_primea :: c)) = (maxVBal)))"
assumes v'56: "((((a_maxValhash_primea :: c)) = (maxVal)))"
shows "((~ (\<exists> m \<in> (msgs) : (((((fapply ((m), (''type''))) = (''2a''))) \<and> (((fapply ((m), (''bal''))) = (b))))))))"(is "PROP ?ob'155")
proof -
ML_command {* writeln "*** TLAPS ENTER 155"; *}
show "PROP ?ob'155"

(* BEGIN ZENON INPUT
;; file=FastPaxos.tlaps/tlapm_9ff4b8.znn; PATH='/home/alexis51151/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/home/alexis51151/.local/bin:/home/alexis51151/Ecole/EPaxos/toolbox:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >FastPaxos.tlaps/tlapm_9ff4b8.znn.out
;; obligation #155
$hyp "v'37" (/\ (/\ TypeOK MsgInv)
AccInv)
$hyp "v'38" Next
$hyp "b_in" (TLA.in b arith.N)
$hyp "v'53" (/\ (-. (TLA.bEx msgs ((m) (/\ (= (TLA.fapply m "type") "2a")
(= (TLA.fapply m "bal") b)))))
(TLA.bEx Values ((v) (/\ (\/ (TLA.bEx (Quorums b) ((Q) (TLA.bEx (TLA.SUBSET (TLA.subsetOf msgs ((m) (/\ (= (TLA.fapply m "type")
"1b") (= (TLA.fapply m "bal")
b))))) ((S) (/\ (TLA.bAll Q ((a) (TLA.bEx S ((m) (= (TLA.fapply m "acc")
a))))) (\/ (TLA.bAll S ((m) (= (TLA.fapply m "maxVBal")
(arith.minus (TLA.fapply TLA.Succ 0))))) (TLA.bEx (arith.intrange 0
(arith.add b
(arith.minus (TLA.fapply TLA.Succ 0)))) ((a_ca) (/\ (TLA.bAll S ((m) (arith.le (TLA.fapply m "maxVBal")
a_ca))) (TLA.bEx S ((m) (/\ (= (TLA.fapply m "maxVBal") a_ca)
(= (TLA.fapply m "maxVal") v))))))))))))) (= b 0))
(Send (TLA.record "type" "2a" "bal" b "val" v))))))
$hyp "v'54" (= a_maxBalhash_primea maxBal)
$hyp "v'55" (= a_maxVBalhash_primea
maxVBal)
$hyp "v'56" (= a_maxValhash_primea
maxVal)
$goal (-. (TLA.bEx msgs ((m) (/\ (= (TLA.fapply m "type") "2a")
(= (TLA.fapply m "bal")
b)))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hd:"((~bEx(msgs, (\<lambda>m. (((m[''type''])=''2a'')&((m[''bal''])=b)))))&bEx(Values, (\<lambda>v. ((bEx(Quorums(b), (\<lambda>Q. bEx(SUBSET(subsetOf(msgs, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=b))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''acc''])=a)))))&(bAll(S, (\<lambda>m. ((m[''maxVBal''])= -.(1))))|bEx(isa'dotdot(0, (b +  -.(1))), (\<lambda>a_ca. (bAll(S, (\<lambda>m. ((m[''maxVBal'']) <= a_ca)))&bEx(S, (\<lambda>m. (((m[''maxVBal''])=a_ca)&((m[''maxVal''])=v)))))))))))))|(b=0))&Send((''type'' :> (''2a'') @@ ''bal'' :> (b) @@ ''val'' :> (v)))))))" (is "?z_hi&?z_hw")
 using v'53 by blast
 assume z_Hh:"(~?z_hi)" (is "~~?z_hj")
 have z_Hi: "?z_hi"
 by (rule zenon_and_0 [OF z_Hd])
 show FALSE
 by (rule notE [OF z_Hh z_Hi])
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 155"; *} qed
lemma ob'181:
fixes Acceptors
fixes Values
fixes Quorums
fixes msgs msgs'
fixes maxBal maxBal'
fixes maxVBal maxVBal'
fixes maxVal maxVal'
(* usable definition vars suppressed *)
(* usable definition Send suppressed *)
(* usable definition None suppressed *)
(* usable definition Init suppressed *)
(* usable definition Phase1a suppressed *)
(* usable definition Phase1b suppressed *)
(* usable definition Phase2a suppressed *)
(* usable definition Phase2b suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition VotedForIn suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition Chosen suppressed *)
(* usable definition Consistency suppressed *)
(* usable definition Messages suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition WontVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition MsgInv suppressed *)
(* usable definition AccInv suppressed *)
assumes v'38: "(((((TypeOK) \<and> (MsgInv))) \<and> (AccInv)))"
assumes v'39: "(Next)"
fixes b
assumes b_in : "(b \<in> (Nat))"
fixes v
assumes v_in : "(v \<in> (Values))"
assumes v'70: "(((b) \<noteq> ((0))))"
assumes v'71: "(((\<exists> Q \<in> ((Quorums ((b)))) : (\<exists> S \<in> ((SUBSET (subsetOf((msgs), %m. (((((fapply ((m), (''type''))) = (''1b''))) \<and> (((fapply ((m), (''bal''))) = (b))))))))) : ((\<forall> a \<in> (Q) : (\<exists> m \<in> (S) : (((fapply ((m), (''acc''))) = (a))))) & ((\<forall> m \<in> (S) : (((fapply ((m), (''maxVBal''))) = ((minus (((Succ[0])))))))) | (\<exists> a_ca \<in> ((isa_peri_peri_a (((0)), ((arith_add ((b), ((minus (((Succ[0]))))))))))) : ((\<forall> m \<in> (S) : ((leq ((fapply ((m), (''maxVBal''))), (a_ca))))) & (\<exists> m \<in> (S) : ((((fapply ((m), (''maxVBal''))) = (a_ca))) & (((fapply ((m), (''maxVal''))) = (v))))))))))) | (((b) = ((0))))) & ((Send ((((''type'' :> (''2a'')) @@ (''bal'' :> (b)) @@ (''val'' :> (v))))))))"
shows "(\<exists> Q \<in> ((Quorums ((b)))) : (\<exists> S \<in> ((SUBSET (subsetOf((msgs), %m. (((((fapply ((m), (''type''))) = (''1b''))) \<and> (((fapply ((m), (''bal''))) = (b))))))))) : ((\<forall> a \<in> (Q) : (\<exists> m \<in> (S) : (((fapply ((m), (''acc''))) = (a))))) & ((\<forall> m \<in> (S) : (((fapply ((m), (''maxVBal''))) = ((minus (((Succ[0])))))))) | (\<exists> a_ca \<in> ((isa_peri_peri_a (((0)), ((arith_add ((b), ((minus (((Succ[0]))))))))))) : ((\<forall> m \<in> (S) : ((leq ((fapply ((m), (''maxVBal''))), (a_ca))))) & (\<exists> m \<in> (S) : ((((fapply ((m), (''maxVBal''))) = (a_ca))) & (((fapply ((m), (''maxVal''))) = (v)))))))))))"(is "PROP ?ob'181")
proof -
ML_command {* writeln "*** TLAPS ENTER 181"; *}
show "PROP ?ob'181"

(* BEGIN ZENON INPUT
;; file=FastPaxos.tlaps/tlapm_9d2e32.znn; PATH='/home/alexis51151/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/home/alexis51151/.local/bin:/home/alexis51151/Ecole/EPaxos/toolbox:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >FastPaxos.tlaps/tlapm_9d2e32.znn.out
;; obligation #181
$hyp "v'38" (/\ (/\ TypeOK MsgInv)
AccInv)
$hyp "v'39" Next
$hyp "b_in" (TLA.in b arith.N)
$hyp "v_in" (TLA.in v Values)
$hyp "v'70" (-. (= b
0))
$hyp "v'71" (/\ (\/ (TLA.bEx (Quorums b) ((Q) (TLA.bEx (TLA.SUBSET (TLA.subsetOf msgs ((m) (/\ (= (TLA.fapply m "type")
"1b") (= (TLA.fapply m "bal")
b))))) ((S) (/\ (TLA.bAll Q ((a) (TLA.bEx S ((m) (= (TLA.fapply m "acc")
a))))) (\/ (TLA.bAll S ((m) (= (TLA.fapply m "maxVBal")
(arith.minus (TLA.fapply TLA.Succ 0))))) (TLA.bEx (arith.intrange 0
(arith.add b
(arith.minus (TLA.fapply TLA.Succ 0)))) ((a_ca) (/\ (TLA.bAll S ((m) (arith.le (TLA.fapply m "maxVBal")
a_ca))) (TLA.bEx S ((m) (/\ (= (TLA.fapply m "maxVBal") a_ca)
(= (TLA.fapply m "maxVal") v))))))))))))) (= b 0))
(Send (TLA.record "type" "2a" "bal" b "val" v)))
$goal (TLA.bEx (Quorums b) ((Q) (TLA.bEx (TLA.SUBSET (TLA.subsetOf msgs ((m) (/\ (= (TLA.fapply m "type")
"1b") (= (TLA.fapply m "bal")
b))))) ((S) (/\ (TLA.bAll Q ((a) (TLA.bEx S ((m) (= (TLA.fapply m "acc")
a))))) (\/ (TLA.bAll S ((m) (= (TLA.fapply m "maxVBal")
(arith.minus (TLA.fapply TLA.Succ 0))))) (TLA.bEx (arith.intrange 0
(arith.add b
(arith.minus (TLA.fapply TLA.Succ 0)))) ((a_ca) (/\ (TLA.bAll S ((m) (arith.le (TLA.fapply m "maxVBal")
a_ca))) (TLA.bEx S ((m) (/\ (= (TLA.fapply m "maxVBal") a_ca)
(= (TLA.fapply m "maxVal")
v)))))))))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hf:"((bEx(Quorums(b), (\<lambda>Q. bEx(SUBSET(subsetOf(msgs, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=b))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''acc''])=a)))))&(bAll(S, (\<lambda>m. ((m[''maxVBal''])= -.(1))))|bEx(isa'dotdot(0, (b +  -.(1))), (\<lambda>a_ca. (bAll(S, (\<lambda>m. ((m[''maxVBal'']) <= a_ca)))&bEx(S, (\<lambda>m. (((m[''maxVBal''])=a_ca)&((m[''maxVal''])=v)))))))))))))|(b=0))&Send((''type'' :> (''2a'') @@ ''bal'' :> (b) @@ ''val'' :> (v))))" (is "?z_hh&?z_hcn")
 using v'71 by blast
 have z_He:"(b~=0)"
 using v'70 by blast
 assume z_Hg:"(~bEx(Quorums(b), (\<lambda>Q. bEx(SUBSET(subsetOf(msgs, (\<lambda>m. (((m[''type''])=''1b'')&((m[''bal''])=b))))), (\<lambda>S. (bAll(Q, (\<lambda>a. bEx(S, (\<lambda>m. ((m[''acc''])=a)))))&(bAll(S, (\<lambda>m. ((m[''maxVBal''])= -.(1))))|bEx(isa'dotdot(0, (b +  -.(1))), (\<lambda>a_ca. (bAll(S, (\<lambda>m. ((m[''maxVBal'']) <= a_ca)))&bEx(S, (\<lambda>m. (((m[''maxVBal''])=a_ca)&((m[''maxVal''])=v))))))))))))))" (is "~?z_hi")
 have z_Hh: "?z_hh" (is "_|?z_hcm")
 by (rule zenon_and_0 [OF z_Hf])
 show FALSE
 proof (rule zenon_or [OF z_Hh])
  assume z_Hi:"?z_hi"
  show FALSE
  by (rule notE [OF z_Hg z_Hi])
 next
  assume z_Hcm:"?z_hcm"
  show FALSE
  by (rule notE [OF z_He z_Hcm])
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 181"; *} qed
lemma ob'192:
fixes Acceptors
fixes Values
fixes Quorums
fixes msgs msgs'
fixes maxBal maxBal'
fixes maxVBal maxVBal'
fixes maxVal maxVal'
(* usable definition vars suppressed *)
(* usable definition Send suppressed *)
(* usable definition None suppressed *)
(* usable definition Init suppressed *)
(* usable definition Phase1a suppressed *)
(* usable definition Phase1b suppressed *)
(* usable definition Phase2a suppressed *)
(* usable definition Phase2b suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition VotedForIn suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition Chosen suppressed *)
(* usable definition Consistency suppressed *)
(* usable definition Messages suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition WontVoteIn suppressed *)
(* usable definition MsgInv suppressed *)
(* usable definition AccInv suppressed *)
assumes v'37: "(((((TypeOK) \<and> (MsgInv))) \<and> (AccInv)))"
assumes v'38: "(Next)"
fixes b
assumes b_in : "(b \<in> (Nat))"
fixes v
assumes v_in : "(v \<in> (Values))"
fixes Q
assumes Q_in : "(Q \<in> ((Quorums ((b)))))"
fixes S
assumes S_in : "(S \<in> ((SUBSET (subsetOf((msgs), %m. (((((fapply ((m), (''type''))) = (''1b''))) \<and> (((fapply ((m), (''bal''))) = (b))))))))))"
fixes a_ca
assumes a_ca_in : "(a_ca \<in> ((isa_peri_peri_a (((0)), ((arith_add ((b), ((minus (((Succ[0]))))))))))))"
fixes ma
assumes ma_in : "(ma \<in> (S))"
assumes v'81: "((\<And> d :: c. d \<in> ((isa_peri_peri_a (((0)), ((arith_add ((b), ((minus (((Succ[0]))))))))))) \<Longrightarrow> (\<exists> QQ \<in> ((Quorums ((d)))) : (\<forall> q \<in> (QQ) : ((((VotedForIn ((q), (v), (d)))) \<or> ((WontVoteIn ((q), (d))))))))))"
shows "(\<forall> a_ca_1 \<in> ((isa_peri_peri_a (((0)), ((arith_add ((b), ((minus (((Succ[0]))))))))))) : (\<exists> Q_1 \<in> ((Quorums ((a_ca_1)))) : (\<forall> a \<in> (Q_1) : ((((VotedForIn ((a), (v), (a_ca_1)))) \<or> ((WontVoteIn ((a), (a_ca_1)))))))))"(is "PROP ?ob'192")
proof -
ML_command {* writeln "*** TLAPS ENTER 192"; *}
show "PROP ?ob'192"

(* BEGIN ZENON INPUT
;; file=FastPaxos.tlaps/tlapm_a8b819.znn; PATH='/home/alexis51151/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/home/alexis51151/.local/bin:/home/alexis51151/Ecole/EPaxos/toolbox:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >FastPaxos.tlaps/tlapm_a8b819.znn.out
;; obligation #192
$hyp "v'37" (/\ (/\ TypeOK MsgInv)
AccInv)
$hyp "v'38" Next
$hyp "b_in" (TLA.in b arith.N)
$hyp "v_in" (TLA.in v Values)
$hyp "Q_in" (TLA.in Q (Quorums b))
$hyp "S_in" (TLA.in S (TLA.SUBSET (TLA.subsetOf msgs ((m) (/\ (= (TLA.fapply m "type")
"1b") (= (TLA.fapply m "bal")
b))))))
$hyp "a_ca_in" (TLA.in a_ca (arith.intrange 0 (arith.add b
(arith.minus (TLA.fapply TLA.Succ 0)))))
$hyp "ma_in" (TLA.in ma S)
$hyp "v'81" (TLA.bAll (arith.intrange 0 (arith.add b
(arith.minus (TLA.fapply TLA.Succ 0)))) ((d) (TLA.bEx (Quorums d) ((QQ) (TLA.bAll QQ ((q) (\/ (VotedForIn q
v d) (WontVoteIn q d))))))))
$goal (TLA.bAll (arith.intrange 0 (arith.add b
(arith.minus (TLA.fapply TLA.Succ 0)))) ((a_ca_1) (TLA.bEx (Quorums a_ca_1) ((Q_1) (TLA.bAll Q_1 ((a) (\/ (VotedForIn a
v a_ca_1) (WontVoteIn a
a_ca_1))))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Hi:"bAll(isa'dotdot(0, (b +  -.(1))), (\<lambda>d. bEx(Quorums(d), (\<lambda>QQ. bAll(QQ, (\<lambda>q. (VotedForIn(q, v, d)|WontVoteIn(q, d))))))))" (is "?z_hi")
 using v'81 by blast
 assume z_Hj:"(~?z_hi)"
 show FALSE
 by (rule notE [OF z_Hj z_Hi])
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 192"; *} qed
lemma ob'146:
fixes Acceptors
fixes Values
fixes Quorums
fixes msgs msgs'
fixes maxBal maxBal'
fixes maxVBal maxVBal'
fixes maxVal maxVal'
(* usable definition vars suppressed *)
(* usable definition Send suppressed *)
(* usable definition None suppressed *)
(* usable definition Init suppressed *)
(* usable definition Phase1a suppressed *)
(* usable definition Phase1b suppressed *)
(* usable definition Phase2a suppressed *)
(* usable definition Phase2b suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition VotedForIn suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition Chosen suppressed *)
(* usable definition Consistency suppressed *)
(* usable definition WontVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition AccInv suppressed *)
assumes v'35: "((((((((msgs) \<in> ((SUBSET ((((((([''type'' : ({(''1a'')}), ''bal'' : (Nat)]) \<union> ([''type'' : ({(''1b'')}), ''bal'' : (Nat), ''maxVBal'' : (((Nat) \<union> ({((minus (((Succ[0])))))}))), ''maxVal'' : (((Values) \<union> ({(None)}))), ''acc'' : (Acceptors)]))) \<union> ([''type'' : ({(''2a'')}), ''bal'' : (Nat), ''val'' : (Values)]))) \<union> ([''type'' : ({(''2b'')}), ''bal'' : (Nat), ''val'' : (Values), ''acc'' : (Acceptors)]))))))) & (((maxVBal) \<in> ([(Acceptors) \<rightarrow> (((Nat) \<union> ({((minus (((Succ[0])))))})))]))) & (((maxBal) \<in> ([(Acceptors) \<rightarrow> (((Nat) \<union> ({((minus (((Succ[0])))))})))]))) & (((maxVal) \<in> ([(Acceptors) \<rightarrow> (((Values) \<union> ({(None)})))]))) & (\<forall> a \<in> (Acceptors) : ((geq ((fapply ((maxBal), (a))), (fapply ((maxVBal), (a)))))))) \<and> (\<forall> m \<in> (msgs) : ((((((fapply ((m), (''type''))) = (''1b''))) \<Rightarrow> (((leq ((fapply ((m), (''bal''))), (fapply ((maxBal), (fapply ((m), (''acc'')))))))) & (((((fapply ((m), (''maxVal''))) \<in> (Values))) & (((fapply ((m), (''maxVBal''))) \<in> (Nat))) & ((VotedForIn ((fapply ((m), (''acc''))), (fapply ((m), (''maxVal''))), (fapply ((m), (''maxVBal''))))))) | ((((fapply ((m), (''maxVal''))) = (None))) & (((fapply ((m), (''maxVBal''))) = ((minus (((Succ[0]))))))))) & (\<forall> a_ca \<in> ((isa_peri_peri_a (((arith_add ((fapply ((m), (''maxVBal''))), ((Succ[0]))))), ((arith_add ((fapply ((m), (''bal''))), ((minus (((Succ[0]))))))))))) : ((~ (\<exists> v \<in> (Values) : ((VotedForIn ((fapply ((m), (''acc''))), (v), (a_ca))))))))))) & (((((fapply ((m), (''type''))) = (''2a''))) \<Rightarrow> (((SafeAt ((fapply ((m), (''val''))), (fapply ((m), (''bal'')))))) & (\<forall> ma \<in> (msgs) : (((((((fapply ((ma), (''type''))) = (''2a''))) \<and> (((fapply ((ma), (''bal''))) = (fapply ((m), (''bal''))))))) \<Rightarrow> (((ma) = (m))))))))) & (((((fapply ((m), (''type''))) = (''2b''))) \<Rightarrow> ((\<exists> ma \<in> (msgs) : ((((fapply ((ma), (''type''))) = (''2a''))) & (((fapply ((ma), (''bal''))) = (fapply ((m), (''bal''))))) & (((fapply ((ma), (''val''))) = (fapply ((m), (''val''))))))) & ((leq ((fapply ((m), (''bal''))), (fapply ((maxVBal), (fapply ((m), (''acc''))))))))))))))) \<and> (AccInv)))"
assumes v'36: "(Next)"
fixes b
assumes b_in : "(b \<in> (Nat))"
fixes v
assumes v_in : "(v \<in> (Values))"
assumes v'61: "(((((a_msgshash_primea :: c)) \<in> ((SUBSET ((((((([''type'' : ({(''1a'')}), ''bal'' : (Nat)]) \<union> ([''type'' : ({(''1b'')}), ''bal'' : (Nat), ''maxVBal'' : (((Nat) \<union> ({((minus (((Succ[0])))))}))), ''maxVal'' : (((Values) \<union> ({(None)}))), ''acc'' : (Acceptors)]))) \<union> ([''type'' : ({(''2a'')}), ''bal'' : (Nat), ''val'' : (Values)]))) \<union> ([''type'' : ({(''2b'')}), ''bal'' : (Nat), ''val'' : (Values), ''acc'' : (Acceptors)]))))))) & ((((a_maxVBalhash_primea :: c)) \<in> ([(Acceptors) \<rightarrow> (((Nat) \<union> ({((minus (((Succ[0])))))})))]))) & ((((a_maxBalhash_primea :: c)) \<in> ([(Acceptors) \<rightarrow> (((Nat) \<union> ({((minus (((Succ[0])))))})))]))) & ((((a_maxValhash_primea :: c)) \<in> ([(Acceptors) \<rightarrow> (((Values) \<union> ({(None)})))]))) & (\<forall> a \<in> (Acceptors) : ((geq ((fapply (((a_maxBalhash_primea :: c)), (a))), (fapply (((a_maxVBalhash_primea :: c)), (a))))))))"
assumes v'62: "((((a_maxBalhash_primea :: c)) = (maxBal)))"
assumes v'63: "((((a_maxVBalhash_primea :: c)) = (maxVBal)))"
assumes v'64: "((((a_maxValhash_primea :: c)) = (maxVal)))"
assumes v'65: "((((a_msgshash_primea :: c)) = (((msgs) \<union> ({(((''type'' :> (''2a'')) @@ (''bal'' :> (b)) @@ (''val'' :> (v))))})))))"
assumes v'66: "(\<forall>aa : (\<forall>vv : (\<forall>bb : ((((a_h03062837f0f10c4714e0f53023b1a7a ((aa), (vv), (bb)) :: c)) \<Leftrightarrow> ((VotedForIn ((aa), (vv), (bb)))))))))"
assumes v'67: "(\<forall> m \<in> ((a_msgshash_primea :: c)) : (\<forall> ma \<in> ((a_msgshash_primea :: c)) : (((((((((fapply ((m), (''type''))) = (''2a''))) \<and> (((fapply ((ma), (''type''))) = (''2a''))))) \<and> (((fapply ((ma), (''bal''))) = (fapply ((m), (''bal''))))))) \<Rightarrow> (((ma) = (m)))))))"
assumes v'68: "((a_hd4a7fa801d94bc2a9c69d39a405ea2a ((fapply ((((''type'' :> (''2a'')) @@ (''bal'' :> (b)) @@ (''val'' :> (v)))), (''val''))), (fapply ((((''type'' :> (''2a'')) @@ (''bal'' :> (b)) @@ (''val'' :> (v)))), (''bal'')))) :: c))"
assumes v'69: "((((((((((((((msgs) \<in> ((SUBSET ((((((([''type'' : ({(''1a'')}), ''bal'' : (Nat)]) \<union> ([''type'' : ({(''1b'')}), ''bal'' : (Nat), ''maxVBal'' : (((Nat) \<union> ({((minus (((Succ[0])))))}))), ''maxVal'' : (((Values) \<union> ({(None)}))), ''acc'' : (Acceptors)]))) \<union> ([''type'' : ({(''2a'')}), ''bal'' : (Nat), ''val'' : (Values)]))) \<union> ([''type'' : ({(''2b'')}), ''bal'' : (Nat), ''val'' : (Values), ''acc'' : (Acceptors)]))))))) & (((maxVBal) \<in> ([(Acceptors) \<rightarrow> (((Nat) \<union> ({((minus (((Succ[0])))))})))]))) & (((maxBal) \<in> ([(Acceptors) \<rightarrow> (((Nat) \<union> ({((minus (((Succ[0])))))})))]))) & (((maxVal) \<in> ([(Acceptors) \<rightarrow> (((Values) \<union> ({(None)})))]))) & (\<forall> a \<in> (Acceptors) : ((geq ((fapply ((maxBal), (a))), (fapply ((maxVBal), (a)))))))) \<and> (\<forall> m \<in> (msgs) : ((((((fapply ((m), (''type''))) = (''1b''))) \<Rightarrow> (((leq ((fapply ((m), (''bal''))), (fapply ((maxBal), (fapply ((m), (''acc'')))))))) & (((((fapply ((m), (''maxVal''))) \<in> (Values))) & (((fapply ((m), (''maxVBal''))) \<in> (Nat))) & ((VotedForIn ((fapply ((m), (''acc''))), (fapply ((m), (''maxVal''))), (fapply ((m), (''maxVBal''))))))) | ((((fapply ((m), (''maxVal''))) = (None))) & (((fapply ((m), (''maxVBal''))) = ((minus (((Succ[0]))))))))) & (\<forall> a_ca \<in> ((isa_peri_peri_a (((arith_add ((fapply ((m), (''maxVBal''))), ((Succ[0]))))), ((arith_add ((fapply ((m), (''bal''))), ((minus (((Succ[0]))))))))))) : ((~ (\<exists> v_1 \<in> (Values) : ((VotedForIn ((fapply ((m), (''acc''))), (v_1), (a_ca))))))))))) & (((((fapply ((m), (''type''))) = (''2a''))) \<Rightarrow> (((SafeAt ((fapply ((m), (''val''))), (fapply ((m), (''bal'')))))) & (\<forall> ma \<in> (msgs) : (((((((fapply ((ma), (''type''))) = (''2a''))) \<and> (((fapply ((ma), (''bal''))) = (fapply ((m), (''bal''))))))) \<Rightarrow> (((ma) = (m))))))))) & (((((fapply ((m), (''type''))) = (''2b''))) \<Rightarrow> ((\<exists> ma \<in> (msgs) : ((((fapply ((ma), (''type''))) = (''2a''))) & (((fapply ((ma), (''bal''))) = (fapply ((m), (''bal''))))) & (((fapply ((ma), (''val''))) = (fapply ((m), (''val''))))))) & ((leq ((fapply ((m), (''bal''))), (fapply ((maxVBal), (fapply ((m), (''acc''))))))))))))))) \<and> (AccInv))) \<and> (Next))) \<and> (((((a_msgshash_primea :: c)) \<in> ((SUBSET ((((((([''type'' : ({(''1a'')}), ''bal'' : (Nat)]) \<union> ([''type'' : ({(''1b'')}), ''bal'' : (Nat), ''maxVBal'' : (((Nat) \<union> ({((minus (((Succ[0])))))}))), ''maxVal'' : (((Values) \<union> ({(None)}))), ''acc'' : (Acceptors)]))) \<union> ([''type'' : ({(''2a'')}), ''bal'' : (Nat), ''val'' : (Values)]))) \<union> ([''type'' : ({(''2b'')}), ''bal'' : (Nat), ''val'' : (Values), ''acc'' : (Acceptors)]))))))) & ((((a_maxVBalhash_primea :: c)) \<in> ([(Acceptors) \<rightarrow> (((Nat) \<union> ({((minus (((Succ[0])))))})))]))) & ((((a_maxBalhash_primea :: c)) \<in> ([(Acceptors) \<rightarrow> (((Nat) \<union> ({((minus (((Succ[0])))))})))]))) & ((((a_maxValhash_primea :: c)) \<in> ([(Acceptors) \<rightarrow> (((Values) \<union> ({(None)})))]))) & (\<forall> a \<in> (Acceptors) : ((geq ((fapply (((a_maxBalhash_primea :: c)), (a))), (fapply (((a_maxVBalhash_primea :: c)), (a)))))))))) \<Rightarrow> (\<forall> v_1 \<in> (Values) : (\<forall> b_1 \<in> (Nat) : ((((SafeAt ((v_1), (b_1)))) \<Rightarrow> ((a_hd4a7fa801d94bc2a9c69d39a405ea2a ((v_1), (b_1)) :: c))))))))"
shows "(\<forall> m \<in> ((a_msgshash_primea :: c)) : ((((((fapply ((m), (''type''))) = (''1b''))) \<Rightarrow> (((leq ((fapply ((m), (''bal''))), (fapply (((a_maxBalhash_primea :: c)), (fapply ((m), (''acc'')))))))) & (((((fapply ((m), (''maxVal''))) \<in> (Values))) & (((fapply ((m), (''maxVBal''))) \<in> (Nat))) & ((a_h03062837f0f10c4714e0f53023b1a7a ((fapply ((m), (''acc''))), (fapply ((m), (''maxVal''))), (fapply ((m), (''maxVBal'')))) :: c))) | ((((fapply ((m), (''maxVal''))) = (None))) & (((fapply ((m), (''maxVBal''))) = ((minus (((Succ[0]))))))))) & (\<forall> a_ca \<in> ((isa_peri_peri_a (((arith_add ((fapply ((m), (''maxVBal''))), ((Succ[0]))))), ((arith_add ((fapply ((m), (''bal''))), ((minus (((Succ[0]))))))))))) : ((~ (\<exists> v_1 \<in> (Values) : ((a_h03062837f0f10c4714e0f53023b1a7a ((fapply ((m), (''acc''))), (v_1), (a_ca)) :: c))))))))) & (((((fapply ((m), (''type''))) = (''2a''))) \<Rightarrow> (((a_hd4a7fa801d94bc2a9c69d39a405ea2a ((fapply ((m), (''val''))), (fapply ((m), (''bal'')))) :: c)) & (\<forall> ma \<in> ((a_msgshash_primea :: c)) : (((((((fapply ((ma), (''type''))) = (''2a''))) \<and> (((fapply ((ma), (''bal''))) = (fapply ((m), (''bal''))))))) \<Rightarrow> (((ma) = (m))))))))) & (((((fapply ((m), (''type''))) = (''2b''))) \<Rightarrow> ((\<exists> ma \<in> ((a_msgshash_primea :: c)) : ((((fapply ((ma), (''type''))) = (''2a''))) & (((fapply ((ma), (''bal''))) = (fapply ((m), (''bal''))))) & (((fapply ((ma), (''val''))) = (fapply ((m), (''val''))))))) & ((leq ((fapply ((m), (''bal''))), (fapply (((a_maxVBalhash_primea :: c)), (fapply ((m), (''acc'')))))))))))))"(is "PROP ?ob'146")
proof -
ML_command {* writeln "*** TLAPS ENTER 146"; *}
show "PROP ?ob'146"

(* BEGIN ZENON INPUT
;; file=FastPaxos.tlaps/tlapm_49cc5f.znn; PATH='/home/alexis51151/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/home/alexis51151/.local/bin:/home/alexis51151/Ecole/EPaxos/toolbox:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >FastPaxos.tlaps/tlapm_49cc5f.znn.out
;; obligation #146
$hyp "v'35" (/\ (/\ (/\ (TLA.in msgs
(TLA.SUBSET (TLA.cup (TLA.cup (TLA.cup (TLA.recordset "type" (TLA.set "1a") "bal" arith.N)
(TLA.recordset "type" (TLA.set "1b") "bal" arith.N "maxVBal" (TLA.cup arith.N
(TLA.set (arith.minus (TLA.fapply TLA.Succ 0)))) "maxVal" (TLA.cup Values
(TLA.set None)) "acc" Acceptors))
(TLA.recordset "type" (TLA.set "2a") "bal" arith.N "val" Values))
(TLA.recordset "type" (TLA.set "2b") "bal" arith.N "val" Values "acc" Acceptors))))
(TLA.in maxVBal (TLA.FuncSet Acceptors (TLA.cup arith.N
(TLA.set (arith.minus (TLA.fapply TLA.Succ 0)))))) (TLA.in maxBal
(TLA.FuncSet Acceptors (TLA.cup arith.N
(TLA.set (arith.minus (TLA.fapply TLA.Succ 0)))))) (TLA.in maxVal
(TLA.FuncSet Acceptors (TLA.cup Values (TLA.set None))))
(TLA.bAll Acceptors ((a) (arith.le (TLA.fapply maxVBal a)
(TLA.fapply maxBal a)))))
(TLA.bAll msgs ((m) (/\ (=> (= (TLA.fapply m "type") "1b")
(/\ (arith.le (TLA.fapply m "bal") (TLA.fapply maxBal (TLA.fapply m "acc")))
(\/ (/\ (TLA.in (TLA.fapply m "maxVal") Values)
(TLA.in (TLA.fapply m "maxVBal") arith.N) (VotedForIn (TLA.fapply m "acc")
(TLA.fapply m "maxVal") (TLA.fapply m "maxVBal")))
(/\ (= (TLA.fapply m "maxVal") None) (= (TLA.fapply m "maxVBal")
(arith.minus (TLA.fapply TLA.Succ 0)))))
(TLA.bAll (arith.intrange (arith.add (TLA.fapply m "maxVBal")
(TLA.fapply TLA.Succ 0)) (arith.add (TLA.fapply m "bal")
(arith.minus (TLA.fapply TLA.Succ 0)))) ((a_ca) (-. (TLA.bEx Values ((v) (VotedForIn (TLA.fapply m "acc")
v a_ca)))))))) (=> (= (TLA.fapply m "type") "2a")
(/\ (SafeAt (TLA.fapply m "val") (TLA.fapply m "bal"))
(TLA.bAll msgs ((ma) (=> (/\ (= (TLA.fapply ma "type") "2a")
(= (TLA.fapply ma "bal") (TLA.fapply m "bal"))) (= ma m))))))
(=> (= (TLA.fapply m "type") "2b")
(/\ (TLA.bEx msgs ((ma) (/\ (= (TLA.fapply ma "type") "2a")
(= (TLA.fapply ma "bal") (TLA.fapply m "bal")) (= (TLA.fapply ma "val")
(TLA.fapply m "val"))))) (arith.le (TLA.fapply m "bal")
(TLA.fapply maxVBal (TLA.fapply m "acc")))))))))
AccInv)
$hyp "v'36" Next
$hyp "b_in" (TLA.in b arith.N)
$hyp "v_in" (TLA.in v Values)
$hyp "v'61" (/\ (TLA.in a_msgshash_primea
(TLA.SUBSET (TLA.cup (TLA.cup (TLA.cup (TLA.recordset "type" (TLA.set "1a") "bal" arith.N)
(TLA.recordset "type" (TLA.set "1b") "bal" arith.N "maxVBal" (TLA.cup arith.N
(TLA.set (arith.minus (TLA.fapply TLA.Succ 0)))) "maxVal" (TLA.cup Values
(TLA.set None)) "acc" Acceptors))
(TLA.recordset "type" (TLA.set "2a") "bal" arith.N "val" Values))
(TLA.recordset "type" (TLA.set "2b") "bal" arith.N "val" Values "acc" Acceptors))))
(TLA.in a_maxVBalhash_primea (TLA.FuncSet Acceptors (TLA.cup arith.N
(TLA.set (arith.minus (TLA.fapply TLA.Succ 0))))))
(TLA.in a_maxBalhash_primea (TLA.FuncSet Acceptors (TLA.cup arith.N
(TLA.set (arith.minus (TLA.fapply TLA.Succ 0))))))
(TLA.in a_maxValhash_primea (TLA.FuncSet Acceptors (TLA.cup Values
(TLA.set None))))
(TLA.bAll Acceptors ((a) (arith.le (TLA.fapply a_maxVBalhash_primea a)
(TLA.fapply a_maxBalhash_primea a)))))
$hyp "v'62" (= a_maxBalhash_primea maxBal)
$hyp "v'63" (= a_maxVBalhash_primea
maxVBal)
$hyp "v'64" (= a_maxValhash_primea maxVal)
$hyp "v'65" (= a_msgshash_primea (TLA.cup msgs
(TLA.set (TLA.record "type" "2a" "bal" b "val" v))))
$hyp "v'66" (A. ((aa) (A. ((vv) (A. ((bb) (<=> (a_h03062837f0f10c4714e0f53023b1a7a aa
vv bb) (VotedForIn aa vv
bb))))))))
$hyp "v'67" (TLA.bAll a_msgshash_primea ((m) (TLA.bAll a_msgshash_primea ((ma) (=> (/\ (/\ (= (TLA.fapply m "type")
"2a") (= (TLA.fapply ma "type") "2a")) (= (TLA.fapply ma "bal")
(TLA.fapply m "bal"))) (= ma
m))))))
$hyp "v'68" (a_hd4a7fa801d94bc2a9c69d39a405ea2a (TLA.fapply (TLA.record "type" "2a" "bal" b "val" v) "val")
(TLA.fapply (TLA.record "type" "2a" "bal" b "val" v) "bal"))
$hyp "v'69" (=> (/\ (/\ (/\ (/\ (/\ (TLA.in msgs
(TLA.SUBSET (TLA.cup (TLA.cup (TLA.cup (TLA.recordset "type" (TLA.set "1a") "bal" arith.N)
(TLA.recordset "type" (TLA.set "1b") "bal" arith.N "maxVBal" (TLA.cup arith.N
(TLA.set (arith.minus (TLA.fapply TLA.Succ 0)))) "maxVal" (TLA.cup Values
(TLA.set None)) "acc" Acceptors))
(TLA.recordset "type" (TLA.set "2a") "bal" arith.N "val" Values))
(TLA.recordset "type" (TLA.set "2b") "bal" arith.N "val" Values "acc" Acceptors))))
(TLA.in maxVBal (TLA.FuncSet Acceptors (TLA.cup arith.N
(TLA.set (arith.minus (TLA.fapply TLA.Succ 0)))))) (TLA.in maxBal
(TLA.FuncSet Acceptors (TLA.cup arith.N
(TLA.set (arith.minus (TLA.fapply TLA.Succ 0)))))) (TLA.in maxVal
(TLA.FuncSet Acceptors (TLA.cup Values (TLA.set None))))
(TLA.bAll Acceptors ((a) (arith.le (TLA.fapply maxVBal a)
(TLA.fapply maxBal a)))))
(TLA.bAll msgs ((m) (/\ (=> (= (TLA.fapply m "type") "1b")
(/\ (arith.le (TLA.fapply m "bal") (TLA.fapply maxBal (TLA.fapply m "acc")))
(\/ (/\ (TLA.in (TLA.fapply m "maxVal") Values)
(TLA.in (TLA.fapply m "maxVBal") arith.N) (VotedForIn (TLA.fapply m "acc")
(TLA.fapply m "maxVal") (TLA.fapply m "maxVBal")))
(/\ (= (TLA.fapply m "maxVal") None) (= (TLA.fapply m "maxVBal")
(arith.minus (TLA.fapply TLA.Succ 0)))))
(TLA.bAll (arith.intrange (arith.add (TLA.fapply m "maxVBal")
(TLA.fapply TLA.Succ 0)) (arith.add (TLA.fapply m "bal")
(arith.minus (TLA.fapply TLA.Succ 0)))) ((a_ca) (-. (TLA.bEx Values ((v_1) (VotedForIn (TLA.fapply m "acc")
v_1 a_ca)))))))) (=> (= (TLA.fapply m "type") "2a")
(/\ (SafeAt (TLA.fapply m "val") (TLA.fapply m "bal"))
(TLA.bAll msgs ((ma) (=> (/\ (= (TLA.fapply ma "type") "2a")
(= (TLA.fapply ma "bal") (TLA.fapply m "bal"))) (= ma m))))))
(=> (= (TLA.fapply m "type") "2b")
(/\ (TLA.bEx msgs ((ma) (/\ (= (TLA.fapply ma "type") "2a")
(= (TLA.fapply ma "bal") (TLA.fapply m "bal")) (= (TLA.fapply ma "val")
(TLA.fapply m "val"))))) (arith.le (TLA.fapply m "bal")
(TLA.fapply maxVBal (TLA.fapply m "acc"))))))))) AccInv) Next)
(/\ (TLA.in a_msgshash_primea
(TLA.SUBSET (TLA.cup (TLA.cup (TLA.cup (TLA.recordset "type" (TLA.set "1a") "bal" arith.N)
(TLA.recordset "type" (TLA.set "1b") "bal" arith.N "maxVBal" (TLA.cup arith.N
(TLA.set (arith.minus (TLA.fapply TLA.Succ 0)))) "maxVal" (TLA.cup Values
(TLA.set None)) "acc" Acceptors))
(TLA.recordset "type" (TLA.set "2a") "bal" arith.N "val" Values))
(TLA.recordset "type" (TLA.set "2b") "bal" arith.N "val" Values "acc" Acceptors))))
(TLA.in a_maxVBalhash_primea (TLA.FuncSet Acceptors (TLA.cup arith.N
(TLA.set (arith.minus (TLA.fapply TLA.Succ 0))))))
(TLA.in a_maxBalhash_primea (TLA.FuncSet Acceptors (TLA.cup arith.N
(TLA.set (arith.minus (TLA.fapply TLA.Succ 0))))))
(TLA.in a_maxValhash_primea (TLA.FuncSet Acceptors (TLA.cup Values
(TLA.set None))))
(TLA.bAll Acceptors ((a) (arith.le (TLA.fapply a_maxVBalhash_primea a)
(TLA.fapply a_maxBalhash_primea a))))))
(TLA.bAll Values ((v_1) (TLA.bAll arith.N ((b_1) (=> (SafeAt v_1 b_1)
(a_hd4a7fa801d94bc2a9c69d39a405ea2a v_1
b_1)))))))
$goal (TLA.bAll a_msgshash_primea ((m) (/\ (=> (= (TLA.fapply m "type") "1b")
(/\ (arith.le (TLA.fapply m "bal")
(TLA.fapply a_maxBalhash_primea (TLA.fapply m "acc")))
(\/ (/\ (TLA.in (TLA.fapply m "maxVal") Values)
(TLA.in (TLA.fapply m "maxVBal") arith.N)
(a_h03062837f0f10c4714e0f53023b1a7a (TLA.fapply m "acc")
(TLA.fapply m "maxVal") (TLA.fapply m "maxVBal")))
(/\ (= (TLA.fapply m "maxVal") None) (= (TLA.fapply m "maxVBal")
(arith.minus (TLA.fapply TLA.Succ 0)))))
(TLA.bAll (arith.intrange (arith.add (TLA.fapply m "maxVBal")
(TLA.fapply TLA.Succ 0)) (arith.add (TLA.fapply m "bal")
(arith.minus (TLA.fapply TLA.Succ 0)))) ((a_ca) (-. (TLA.bEx Values ((v_1) (a_h03062837f0f10c4714e0f53023b1a7a (TLA.fapply m "acc")
v_1 a_ca)))))))) (=> (= (TLA.fapply m "type") "2a")
(/\ (a_hd4a7fa801d94bc2a9c69d39a405ea2a (TLA.fapply m "val")
(TLA.fapply m "bal"))
(TLA.bAll a_msgshash_primea ((ma) (=> (/\ (= (TLA.fapply ma "type") "2a")
(= (TLA.fapply ma "bal") (TLA.fapply m "bal"))) (= ma m))))))
(=> (= (TLA.fapply m "type") "2b")
(/\ (TLA.bEx a_msgshash_primea ((ma) (/\ (= (TLA.fapply ma "type") "2a")
(= (TLA.fapply ma "bal") (TLA.fapply m "bal")) (= (TLA.fapply ma "val")
(TLA.fapply m "val"))))) (arith.le (TLA.fapply m "bal")
(TLA.fapply a_maxVBalhash_primea (TLA.fapply m "acc"))))))))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Ha:"((((msgs \\in SUBSET(((([''type'' : ({''1a''}), ''bal'' : (Nat)] \\cup [''type'' : ({''1b''}), ''bal'' : (Nat), ''maxVBal'' : ((Nat \\cup { -.(1)})), ''maxVal'' : ((Values \\cup {None})), ''acc'' : (Acceptors)]) \\cup [''type'' : ({''2a''}), ''bal'' : (Nat), ''val'' : (Values)]) \\cup [''type'' : ({''2b''}), ''bal'' : (Nat), ''val'' : (Values), ''acc'' : (Acceptors)])))&((maxVBal \\in FuncSet(Acceptors, (Nat \\cup { -.(1)})))&((maxBal \\in FuncSet(Acceptors, (Nat \\cup { -.(1)})))&((maxVal \\in FuncSet(Acceptors, (Values \\cup {None})))&bAll(Acceptors, (\<lambda>a. ((maxVBal[a]) <= (maxBal[a]))))))))&bAll(msgs, (\<lambda>m. ((((m[''type''])=''1b'')=>(((m[''bal'']) <= (maxBal[(m[''acc''])]))&(((((m[''maxVal'']) \\in Values)&(((m[''maxVBal'']) \\in Nat)&VotedForIn((m[''acc'']), (m[''maxVal'']), (m[''maxVBal'']))))|(((m[''maxVal''])=None)&((m[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((m[''maxVBal'']) + 1), ((m[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v. VotedForIn((m[''acc'']), v, a_ca)))))))))&((((m[''type''])=''2a'')=>(SafeAt((m[''val'']), (m[''bal'']))&bAll(msgs, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(m[''bal''])))=>(ma=m))))))&(((m[''type''])=''2b'')=>(bEx(msgs, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(m[''bal'']))&((ma[''val''])=(m[''val'']))))))&((m[''bal'']) <= (maxVBal[(m[''acc''])])))))))))&AccInv)" (is "?z_ho&_")
 using v'35 by blast
 have z_Hf:"(a_maxBalhash_primea=maxBal)"
 using v'62 by blast
 have z_Hj:"(\\A aa:(\\A vv:(\\A bb:(a_h03062837f0f10c4714e0f53023b1a7a(aa, vv, bb)<=>VotedForIn(aa, vv, bb)))))" (is "\\A x : ?z_hfj(x)")
 using v'66 by blast
 have z_Hg:"(a_maxVBalhash_primea=maxVBal)"
 using v'63 by blast
 have z_Hi:"(a_msgshash_primea=(msgs \\cup {(''type'' :> (''2a'') @@ ''bal'' :> (b) @@ ''val'' :> (v))}))" (is "_=?z_hfm")
 using v'65 by blast
 have z_Hk:"bAll(a_msgshash_primea, (\<lambda>m. bAll(a_msgshash_primea, (\<lambda>ma. (((((m[''type''])=''2a'')&((ma[''type''])=''2a''))&((ma[''bal''])=(m[''bal''])))=>(ma=m))))))" (is "?z_hk")
 using v'67 by blast
 have z_Hb:"Next"
 using v'36 by blast
 have z_Hl:"a_hd4a7fa801d94bc2a9c69d39a405ea2a(((''type'' :> (''2a'') @@ ''bal'' :> (b) @@ ''val'' :> (v))[''val'']), ((''type'' :> (''2a'') @@ ''bal'' :> (b) @@ ''val'' :> (v))[''bal'']))" (is "?z_hl")
 using v'68 by blast
 have z_Hm:"((((?z_ho&AccInv)&Next)&((a_msgshash_primea \\in SUBSET(((([''type'' : ({''1a''}), ''bal'' : (Nat)] \\cup [''type'' : ({''1b''}), ''bal'' : (Nat), ''maxVBal'' : ((Nat \\cup { -.(1)})), ''maxVal'' : ((Values \\cup {None})), ''acc'' : (Acceptors)]) \\cup [''type'' : ({''2a''}), ''bal'' : (Nat), ''val'' : (Values)]) \\cup [''type'' : ({''2b''}), ''bal'' : (Nat), ''val'' : (Values), ''acc'' : (Acceptors)])))&((a_maxVBalhash_primea \\in FuncSet(Acceptors, (Nat \\cup { -.(1)})))&((a_maxBalhash_primea \\in FuncSet(Acceptors, (Nat \\cup { -.(1)})))&((a_maxValhash_primea \\in FuncSet(Acceptors, (Values \\cup {None})))&bAll(Acceptors, (\<lambda>a. ((a_maxVBalhash_primea[a]) <= (a_maxBalhash_primea[a])))))))))=>bAll(Values, (\<lambda>v_1. bAll(Nat, (\<lambda>b_1. (SafeAt(v_1, b_1)=>a_hd4a7fa801d94bc2a9c69d39a405ea2a(v_1, b_1)))))))" (is "?z_hfy=>?z_hgn")
 using v'69 by blast
 have z_He:"((a_msgshash_primea \\in SUBSET(((([''type'' : ({''1a''}), ''bal'' : (Nat)] \\cup [''type'' : ({''1b''}), ''bal'' : (Nat), ''maxVBal'' : ((Nat \\cup { -.(1)})), ''maxVal'' : ((Values \\cup {None})), ''acc'' : (Acceptors)]) \\cup [''type'' : ({''2a''}), ''bal'' : (Nat), ''val'' : (Values)]) \\cup [''type'' : ({''2b''}), ''bal'' : (Nat), ''val'' : (Values), ''acc'' : (Acceptors)])))&((a_maxVBalhash_primea \\in FuncSet(Acceptors, (Nat \\cup { -.(1)})))&((a_maxBalhash_primea \\in FuncSet(Acceptors, (Nat \\cup { -.(1)})))&((a_maxValhash_primea \\in FuncSet(Acceptors, (Values \\cup {None})))&bAll(Acceptors, (\<lambda>a. ((a_maxVBalhash_primea[a]) <= (a_maxBalhash_primea[a]))))))))" (is "?z_hga&?z_hgb")
 using v'61 by blast
 have zenon_L1_: "(~((''type'' :> (''2a'') @@ ''bal'' :> (b) @@ ''val'' :> (v)) \\in {(''type'' :> (''2a'') @@ ''bal'' :> (b) @@ ''val'' :> (v))})) ==> FALSE" (is "?z_hgw ==> FALSE")
 proof -
  assume z_Hgw:"?z_hgw" (is "~?z_hgx")
  have z_Hgy: "((''type'' :> (''2a'') @@ ''bal'' :> (b) @@ ''val'' :> (v))~=(''type'' :> (''2a'') @@ ''bal'' :> (b) @@ ''val'' :> (v)))" (is "?z_hfo~=_")
  by (rule zenon_notin_addElt_0 [of "?z_hfo" "?z_hfo" "{}", OF z_Hgw])
  show FALSE
  by (rule zenon_noteq [OF z_Hgy])
 qed
 have zenon_L2_: "(((''type'' :> (''2a'') @@ ''bal'' :> (b) @@ ''val'' :> (v))[''type''])~=((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''type''])) ==> ((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))=(''type'' :> (''2a'') @@ ''bal'' :> (b) @@ ''val'' :> (v))) ==> FALSE" (is "?z_hha ==> ?z_hji ==> FALSE")
 proof -
  assume z_Hha:"?z_hha" (is "?z_hhb~=?z_hhc")
  assume z_Hji:"?z_hji" (is "?z_hhd=?z_hfo")
  show FALSE
  proof (rule zenon_noteq [of "?z_hhc"])
   have z_Hjj: "(?z_hfo=?z_hhd)"
   by (rule sym [OF z_Hji])
   have z_Hjk: "(?z_hhc~=?z_hhc)"
   by (rule subst [where P="(\<lambda>zenon_Vhwh. ((zenon_Vhwh[''type''])~=?z_hhc))", OF z_Hjj], fact z_Hha)
   thus "(?z_hhc~=?z_hhc)" .
  qed
 qed
 have zenon_L3_: "((''type'' :> (''2a'') @@ ''bal'' :> (b) @@ ''val'' :> (v)) \\in [''type'' : ({''2b''}), ''bal'' : (Nat), ''val'' : (Values), ''acc'' : (Acceptors)]) ==> FALSE" (is "?z_hjp ==> FALSE")
 proof -
  assume z_Hjp:"?z_hjp"
  let ?z_hfo = "(''type'' :> (''2a'') @@ ''bal'' :> (b) @@ ''val'' :> (v))"
  let ?z_hjq = "<<''type'', ''bal'', ''val'', ''acc''>>"
  let ?z_hjr = "<<{''2b''}, Nat, Values, Acceptors>>"
  have z_Hjs: "(1 \\in DOMAIN(?z_hjq))" by auto
  have z_Hju: "((?z_hfo[(?z_hjq[1])]) \\in (?z_hjr[1]))" (is "?z_hju")
  by (rule zenon_in_recordset_field [OF z_Hjp z_Hjs])
  have z_Hjy: "((?z_hfo[''type'']) \\in {''2b''})" (is "?z_hjy")
  using z_Hju by auto
  show FALSE
  proof (rule zenon_in_addElt [of "(?z_hfo[''type''])" "''2b''" "{}", OF z_Hjy])
   assume z_Hjz:"((?z_hfo[''type''])=''2b'')" (is "?z_hhb=?z_hbx")
   have z_Hka: "((''type'' \\in DOMAIN(?z_hfo))&(?z_hhb=''2a''))" (is "?z_hkb&?z_hkd")
   by ((rule zenon_recfield_1)+, rule zenon_recfield_2b)
   have z_Hkd: "?z_hkd" (is "_=?z_hbt")
   by (rule conjD2 [OF z_Hka])
   have z_Hke: "(?z_hbt=?z_hbx)"
   by (rule subst [where P="(\<lambda>zenon_Vib. (zenon_Vib=?z_hbx))", OF z_Hkd z_Hjz])
   have z_Hki: "(?z_hbt~=?z_hbx)"
   by (simp only: zenon_sa_1 zenon_sa_2,
       ((rule zenon_sa_diff_2)+)?,
       (rule zenon_sa_diff_3, auto)?,
       (rule zenon_sa_diff_1, auto)?,
       (rule zenon_sa_diff_0a)?, (rule zenon_sa_diff_0b)?)
   show FALSE
   by (rule notE [OF z_Hki z_Hke])
  next
   assume z_Hkj:"((?z_hfo[''type'']) \\in {})" (is "?z_hkj")
   show FALSE
   by (rule zenon_in_emptyset [of "(?z_hfo[''type''])", OF z_Hkj])
  qed
 qed
 have zenon_L4_: "(a_msgshash_primea=?z_hfm) ==> ((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])]))))))))) \\in {(''type'' :> (''2a'') @@ ''bal'' :> (b) @@ ''val'' :> (v))}) ==> (((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''type''])=''1b'') ==> (a_msgshash_primea \\subseteq ((([''type'' : ({''1a''}), ''bal'' : (Nat)] \\cup [''type'' : ({''1b''}), ''bal'' : (Nat), ''maxVBal'' : ((Nat \\cup { -.(1)})), ''maxVal'' : ((Values \\cup {None})), ''acc'' : (Acceptors)]) \\cup [''type'' : ({''2a''}), ''bal'' : (Nat), ''val'' : (Values)]) \\cup [''type'' : ({''2b''}), ''bal'' : (Nat), ''val'' : (Values), ''acc'' : (Acceptors)])) ==> FALSE" (is "?z_hi ==> ?z_hkk ==> ?z_hkl ==> ?z_hkm ==> FALSE")
 proof -
  assume z_Hi:"?z_hi"
  assume z_Hkk:"?z_hkk"
  assume z_Hkl:"?z_hkl" (is "?z_hhc=?z_hbe")
  assume z_Hkm:"?z_hkm"
  show FALSE
  proof (rule zenon_in_addElt [of "(CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))" "(''type'' :> (''2a'') @@ ''bal'' :> (b) @@ ''val'' :> (v))" "{}", OF z_Hkk])
   assume z_Hji:"((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))=(''type'' :> (''2a'') @@ ''bal'' :> (b) @@ ''val'' :> (v)))" (is "?z_hhd=?z_hfo")
   have z_Hkn: "(?z_hfm \\subseteq ((([''type'' : ({''1a''}), ''bal'' : (Nat)] \\cup [''type'' : ({?z_hbe}), ''bal'' : (Nat), ''maxVBal'' : ((Nat \\cup { -.(1)})), ''maxVal'' : ((Values \\cup {None})), ''acc'' : (Acceptors)]) \\cup [''type'' : ({''2a''}), ''bal'' : (Nat), ''val'' : (Values)]) \\cup [''type'' : ({''2b''}), ''bal'' : (Nat), ''val'' : (Values), ''acc'' : (Acceptors)]))" (is "?z_hkn")
   by (rule subst [where P="(\<lambda>zenon_Vgvh. (zenon_Vgvh \\subseteq ((([''type'' : ({''1a''}), ''bal'' : (Nat)] \\cup [''type'' : ({?z_hbe}), ''bal'' : (Nat), ''maxVBal'' : ((Nat \\cup { -.(1)})), ''maxVal'' : ((Values \\cup {None})), ''acc'' : (Acceptors)]) \\cup [''type'' : ({''2a''}), ''bal'' : (Nat), ''val'' : (Values)]) \\cup [''type'' : ({''2b''}), ''bal'' : (Nat), ''val'' : (Values), ''acc'' : (Acceptors)])))", OF z_Hi z_Hkm])
   have z_Hkr: "({?z_hfo} \\subseteq ((([''type'' : ({''1a''}), ''bal'' : (Nat)] \\cup [''type'' : ({?z_hbe}), ''bal'' : (Nat), ''maxVBal'' : ((Nat \\cup { -.(1)})), ''maxVal'' : ((Values \\cup {None})), ''acc'' : (Acceptors)]) \\cup [''type'' : ({''2a''}), ''bal'' : (Nat), ''val'' : (Values)]) \\cup [''type'' : ({''2b''}), ''bal'' : (Nat), ''val'' : (Values), ''acc'' : (Acceptors)]))" (is "?z_hkr")
   by (rule zenon_cup_subseteq_1 [of , OF z_Hkn])
   have z_Hks_z_Hkr: "bAll({?z_hfo}, (\<lambda>x. (x \\in ((([''type'' : ({''1a''}), ''bal'' : (Nat)] \\cup [''type'' : ({?z_hbe}), ''bal'' : (Nat), ''maxVBal'' : ((Nat \\cup { -.(1)})), ''maxVal'' : ((Values \\cup {None})), ''acc'' : (Acceptors)]) \\cup [''type'' : ({''2a''}), ''bal'' : (Nat), ''val'' : (Values)]) \\cup [''type'' : ({''2b''}), ''bal'' : (Nat), ''val'' : (Values), ''acc'' : (Acceptors)])))) == ?z_hkr" (is "?z_hks == _")
   by (unfold subset_def)
   have z_Hks: "?z_hks"
   by (unfold z_Hks_z_Hkr, fact z_Hkr)
   have z_Hkv_z_Hks: "(\\A x:((x \\in {?z_hfo})=>(x \\in ((([''type'' : ({''1a''}), ''bal'' : (Nat)] \\cup [''type'' : ({?z_hbe}), ''bal'' : (Nat), ''maxVBal'' : ((Nat \\cup { -.(1)})), ''maxVal'' : ((Values \\cup {None})), ''acc'' : (Acceptors)]) \\cup [''type'' : ({''2a''}), ''bal'' : (Nat), ''val'' : (Values)]) \\cup [''type'' : ({''2b''}), ''bal'' : (Nat), ''val'' : (Values), ''acc'' : (Acceptors)])))) == ?z_hks" (is "?z_hkv == _")
   by (unfold bAll_def)
   have z_Hkv: "?z_hkv" (is "\\A x : ?z_hky(x)")
   by (unfold z_Hkv_z_Hks, fact z_Hks)
   have z_Hkz: "?z_hky(?z_hfo)" (is "?z_hgx=>?z_hla")
   by (rule zenon_all_0 [of "?z_hky" "?z_hfo", OF z_Hkv])
   show FALSE
   proof (rule zenon_imply [OF z_Hkz])
    assume z_Hgw:"(~?z_hgx)"
    show FALSE
    by (rule zenon_L1_ [OF z_Hgw])
   next
    assume z_Hla:"?z_hla"
    show FALSE
    proof (rule zenon_in_cup [of "?z_hfo" "(([''type'' : ({''1a''}), ''bal'' : (Nat)] \\cup [''type'' : ({?z_hbe}), ''bal'' : (Nat), ''maxVBal'' : ((Nat \\cup { -.(1)})), ''maxVal'' : ((Values \\cup {None})), ''acc'' : (Acceptors)]) \\cup [''type'' : ({''2a''}), ''bal'' : (Nat), ''val'' : (Values)])" "[''type'' : ({''2b''}), ''bal'' : (Nat), ''val'' : (Values), ''acc'' : (Acceptors)]", OF z_Hla])
     assume z_Hlb:"(?z_hfo \\in (([''type'' : ({''1a''}), ''bal'' : (Nat)] \\cup [''type'' : ({?z_hbe}), ''bal'' : (Nat), ''maxVBal'' : ((Nat \\cup { -.(1)})), ''maxVal'' : ((Values \\cup {None})), ''acc'' : (Acceptors)]) \\cup [''type'' : ({''2a''}), ''bal'' : (Nat), ''val'' : (Values)]))" (is "?z_hlb")
     show FALSE
     proof (rule zenon_in_cup [of "?z_hfo" "([''type'' : ({''1a''}), ''bal'' : (Nat)] \\cup [''type'' : ({?z_hbe}), ''bal'' : (Nat), ''maxVBal'' : ((Nat \\cup { -.(1)})), ''maxVal'' : ((Values \\cup {None})), ''acc'' : (Acceptors)])" "[''type'' : ({''2a''}), ''bal'' : (Nat), ''val'' : (Values)]", OF z_Hlb])
      assume z_Hlc:"(?z_hfo \\in ([''type'' : ({''1a''}), ''bal'' : (Nat)] \\cup [''type'' : ({?z_hbe}), ''bal'' : (Nat), ''maxVBal'' : ((Nat \\cup { -.(1)})), ''maxVal'' : ((Values \\cup {None})), ''acc'' : (Acceptors)]))" (is "?z_hlc")
      show FALSE
      proof (rule zenon_in_cup [of "?z_hfo" "[''type'' : ({''1a''}), ''bal'' : (Nat)]" "[''type'' : ({?z_hbe}), ''bal'' : (Nat), ''maxVBal'' : ((Nat \\cup { -.(1)})), ''maxVal'' : ((Values \\cup {None})), ''acc'' : (Acceptors)]", OF z_Hlc])
       assume z_Hld:"(?z_hfo \\in [''type'' : ({''1a''}), ''bal'' : (Nat)])" (is "?z_hld")
       let ?z_hle = "<<''type'', ''bal''>>"
       let ?z_hlf = "<<{''1a''}, Nat>>"
       have z_Hlg: "(1 \\in DOMAIN(?z_hle))" by auto
       have z_Hli: "((?z_hfo[(?z_hle[1])]) \\in (?z_hlf[1]))" (is "?z_hli")
       by (rule zenon_in_recordset_field [OF z_Hld z_Hlg])
       have z_Hlm: "((?z_hfo[''type'']) \\in {''1a''})" (is "?z_hlm")
       using z_Hli by auto
       show FALSE
       proof (rule zenon_in_addElt [of "(?z_hfo[''type''])" "''1a''" "{}", OF z_Hlm])
        assume z_Hln:"((?z_hfo[''type''])=''1a'')" (is "?z_hhb=?z_hz")
        have z_Hlo: "(?z_hz~=?z_hbe)"
        by auto
        have z_Hha: "(?z_hhb~=?z_hhc)"
        by (rule zenon_stringdiffll [OF z_Hlo z_Hln z_Hkl])
         show FALSE
         by (rule zenon_L2_ [OF z_Hha z_Hji])
       next
        assume z_Hkj:"((?z_hfo[''type'']) \\in {})" (is "?z_hkj")
        show FALSE
        by (rule zenon_in_emptyset [of "(?z_hfo[''type''])", OF z_Hkj])
       qed
      next
       assume z_Hlp:"(?z_hfo \\in [''type'' : ({?z_hbe}), ''bal'' : (Nat), ''maxVBal'' : ((Nat \\cup { -.(1)})), ''maxVal'' : ((Values \\cup {None})), ''acc'' : (Acceptors)])" (is "?z_hlp")
       let ?z_hlq = "<<''type'', ''bal'', ''maxVBal'', ''maxVal'', ''acc''>>"
       let ?z_hlr = "<<{?z_hbe}, Nat, (Nat \\cup { -.(1)}), (Values \\cup {None}), Acceptors>>"
       have z_Hls: "(1 \\in DOMAIN(?z_hlq))" by auto
       have z_Hlu: "((?z_hfo[(?z_hlq[1])]) \\in (?z_hlr[1]))" (is "?z_hlu")
       by (rule zenon_in_recordset_field [OF z_Hlp z_Hls])
       have z_Hly: "((?z_hfo[''type'']) \\in {?z_hbe})" (is "?z_hly")
       using z_Hlu by auto
       show FALSE
       proof (rule zenon_in_addElt [of "(?z_hfo[''type''])" "?z_hbe" "{}", OF z_Hly])
        assume z_Hlz:"((?z_hfo[''type''])=?z_hbe)" (is "?z_hhb=_")
        have z_Hka: "((''type'' \\in DOMAIN(?z_hfo))&(?z_hhb=''2a''))" (is "?z_hkb&?z_hkd")
        by ((rule zenon_recfield_1)+, rule zenon_recfield_2b)
        have z_Hkd: "?z_hkd" (is "_=?z_hbt")
        by (rule conjD2 [OF z_Hka])
        have z_Hma: "(?z_hbt=?z_hbe)"
        by (rule subst [where P="(\<lambda>zenon_Vgyf. (zenon_Vgyf=?z_hbe))", OF z_Hkd z_Hlz])
        have z_Hme: "(?z_hbt~=?z_hbe)"
        by (simp only: zenon_sa_1 zenon_sa_2,
            ((rule zenon_sa_diff_2)+)?,
            (rule zenon_sa_diff_3, auto)?,
            (rule zenon_sa_diff_1, auto)?,
            (rule zenon_sa_diff_0a)?, (rule zenon_sa_diff_0b)?)
        show FALSE
        by (rule notE [OF z_Hme z_Hma])
       next
        assume z_Hkj:"((?z_hfo[''type'']) \\in {})" (is "?z_hkj")
        show FALSE
        by (rule zenon_in_emptyset [of "(?z_hfo[''type''])", OF z_Hkj])
       qed
      qed
     next
      assume z_Hmf:"(?z_hfo \\in [''type'' : ({''2a''}), ''bal'' : (Nat), ''val'' : (Values)])" (is "?z_hmf")
      let ?z_hmg = "<<''type'', ''bal'', ''val''>>"
      let ?z_hmh = "<<{''2a''}, Nat, Values>>"
      have z_Hmi: "(1 \\in DOMAIN(?z_hmg))" by auto
      have z_Hmk: "((?z_hfo[(?z_hmg[1])]) \\in (?z_hmh[1]))" (is "?z_hmk")
      by (rule zenon_in_recordset_field [OF z_Hmf z_Hmi])
      have z_Hmo: "((?z_hfo[''type'']) \\in {''2a''})" (is "?z_hmo")
      using z_Hmk by auto
      show FALSE
      proof (rule zenon_in_addElt [of "(?z_hfo[''type''])" "''2a''" "{}", OF z_Hmo])
       assume z_Hkd:"((?z_hfo[''type''])=''2a'')" (is "?z_hhb=?z_hbt")
       have z_Hme: "(?z_hbt~=?z_hbe)"
       by auto
       have z_Hha: "(?z_hhb~=?z_hhc)"
       by (rule zenon_stringdiffll [OF z_Hme z_Hkd z_Hkl])
        show FALSE
        by (rule zenon_L2_ [OF z_Hha z_Hji])
      next
       assume z_Hkj:"((?z_hfo[''type'']) \\in {})" (is "?z_hkj")
       show FALSE
       by (rule zenon_in_emptyset [of "(?z_hfo[''type''])", OF z_Hkj])
      qed
     qed
    next
     assume z_Hjp:"(?z_hfo \\in [''type'' : ({''2b''}), ''bal'' : (Nat), ''val'' : (Values), ''acc'' : (Acceptors)])" (is "?z_hjp")
     show FALSE
     by (rule zenon_L3_ [OF z_Hjp])
    qed
   qed
  next
   assume z_Hmp:"((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])]))))))))) \\in {})" (is "?z_hmp")
   show FALSE
   by (rule zenon_in_emptyset [of "(CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))", OF z_Hmp])
  qed
 qed
 have zenon_L5_: "((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])]))))))))) \\in ([''type'' : ({''1a''}), ''bal'' : (Nat)] \\cup [''type'' : ({''1b''}), ''bal'' : (Nat), ''maxVBal'' : ((Nat \\cup { -.(1)})), ''maxVal'' : ((Values \\cup {None})), ''acc'' : (Acceptors)])) ==> (((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''type''])=''2a'') ==> FALSE" (is "?z_hmq ==> ?z_hmr ==> FALSE")
 proof -
  assume z_Hmq:"?z_hmq"
  assume z_Hmr:"?z_hmr" (is "?z_hhc=?z_hbt")
  show FALSE
  proof (rule zenon_in_cup [of "(CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=?z_hbt)=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=?z_hbt)&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=?z_hbt)&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))" "[''type'' : ({''1a''}), ''bal'' : (Nat)]" "[''type'' : ({''1b''}), ''bal'' : (Nat), ''maxVBal'' : ((Nat \\cup { -.(1)})), ''maxVal'' : ((Values \\cup {None})), ''acc'' : (Acceptors)]", OF z_Hmq])
   assume z_Hms:"((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=?z_hbt)=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=?z_hbt)&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=?z_hbt)&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])]))))))))) \\in [''type'' : ({''1a''}), ''bal'' : (Nat)])" (is "?z_hms")
   let ?z_hhd = "(CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=?z_hbt)=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=?z_hbt)&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=?z_hbt)&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))"
   let ?z_hle = "<<''type'', ''bal''>>"
   let ?z_hlf = "<<{''1a''}, Nat>>"
   have z_Hlg: "(1 \\in DOMAIN(?z_hle))" by auto
   have z_Hmt: "((?z_hhd[(?z_hle[1])]) \\in (?z_hlf[1]))" (is "?z_hmt")
   by (rule zenon_in_recordset_field [OF z_Hms z_Hlg])
   have z_Hmv: "(?z_hhc \\in {''1a''})" (is "?z_hmv")
   using z_Hmt by auto
   show FALSE
   proof (rule zenon_in_addElt [of "?z_hhc" "''1a''" "{}", OF z_Hmv])
    assume z_Hmw:"(?z_hhc=''1a'')" (is "_=?z_hz")
    have z_Hmx: "(?z_hz~=?z_hbt)"
    by auto
    have z_Hjk: "(?z_hhc~=?z_hhc)"
    by (rule zenon_stringdiffll [OF z_Hmx z_Hmw z_Hmr])
     show FALSE
     by (rule zenon_noteq [OF z_Hjk])
   next
    assume z_Hmy:"(?z_hhc \\in {})" (is "?z_hmy")
    show FALSE
    by (rule zenon_in_emptyset [of "?z_hhc", OF z_Hmy])
   qed
  next
   assume z_Hmz:"((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=?z_hbt)=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=?z_hbt)&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=?z_hbt)&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])]))))))))) \\in [''type'' : ({''1b''}), ''bal'' : (Nat), ''maxVBal'' : ((Nat \\cup { -.(1)})), ''maxVal'' : ((Values \\cup {None})), ''acc'' : (Acceptors)])" (is "?z_hmz")
   let ?z_hhd = "(CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=?z_hbt)=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=?z_hbt)&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=?z_hbt)&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))"
   let ?z_hlq = "<<''type'', ''bal'', ''maxVBal'', ''maxVal'', ''acc''>>"
   let ?z_hlr = "<<{''1b''}, Nat, (Nat \\cup { -.(1)}), (Values \\cup {None}), Acceptors>>"
   have z_Hls: "(1 \\in DOMAIN(?z_hlq))" by auto
   have z_Hna: "((?z_hhd[(?z_hlq[1])]) \\in (?z_hlr[1]))" (is "?z_hna")
   by (rule zenon_in_recordset_field [OF z_Hmz z_Hls])
   have z_Hnc: "(?z_hhc \\in {''1b''})" (is "?z_hnc")
   using z_Hna by auto
   show FALSE
   proof (rule zenon_in_addElt [of "?z_hhc" "''1b''" "{}", OF z_Hnc])
    assume z_Hkl:"(?z_hhc=''1b'')" (is "_=?z_hbe")
    have z_Hnd: "(?z_hbe~=?z_hbt)"
    by auto
    have z_Hjk: "(?z_hhc~=?z_hhc)"
    by (rule zenon_stringdiffll [OF z_Hnd z_Hkl z_Hmr])
     show FALSE
     by (rule zenon_noteq [OF z_Hjk])
   next
    assume z_Hmy:"(?z_hhc \\in {})" (is "?z_hmy")
    show FALSE
    by (rule zenon_in_emptyset [of "?z_hhc", OF z_Hmy])
   qed
  qed
 qed
 have zenon_L6_: "((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])]))))))))) \\in [''type'' : ({''2b''}), ''bal'' : (Nat), ''val'' : (Values), ''acc'' : (Acceptors)]) ==> (((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''type''])=''2a'') ==> FALSE" (is "?z_hne ==> ?z_hmr ==> FALSE")
 proof -
  assume z_Hne:"?z_hne"
  assume z_Hmr:"?z_hmr" (is "?z_hhc=?z_hbt")
  let ?z_hhd = "(CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=?z_hbt)=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=?z_hbt)&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=?z_hbt)&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))"
  let ?z_hjq = "<<''type'', ''bal'', ''val'', ''acc''>>"
  let ?z_hjr = "<<{''2b''}, Nat, Values, Acceptors>>"
  have z_Hjs: "(1 \\in DOMAIN(?z_hjq))" by auto
  have z_Hnf: "((?z_hhd[(?z_hjq[1])]) \\in (?z_hjr[1]))" (is "?z_hnf")
  by (rule zenon_in_recordset_field [OF z_Hne z_Hjs])
  have z_Hnh: "(?z_hhc \\in {''2b''})" (is "?z_hnh")
  using z_Hnf by auto
  show FALSE
  proof (rule zenon_in_addElt [of "?z_hhc" "''2b''" "{}", OF z_Hnh])
   assume z_Hni:"(?z_hhc=''2b'')" (is "_=?z_hbx")
   have z_Hnj: "(?z_hbx~=?z_hbt)"
   by auto
   have z_Hjk: "(?z_hhc~=?z_hhc)"
   by (rule zenon_stringdiffll [OF z_Hnj z_Hni z_Hmr])
    show FALSE
    by (rule zenon_noteq [OF z_Hjk])
  next
   assume z_Hmy:"(?z_hhc \\in {})" (is "?z_hmy")
   show FALSE
   by (rule zenon_in_emptyset [of "?z_hhc", OF z_Hmy])
  qed
 qed
 have zenon_L7_: "(a_msgshash_primea=?z_hfm) ==> ((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])]))))))))) \\in {(''type'' :> (''2a'') @@ ''bal'' :> (b) @@ ''val'' :> (v))}) ==> (((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''type''])=''2b'') ==> (a_msgshash_primea \\subseteq ((([''type'' : ({''1a''}), ''bal'' : (Nat)] \\cup [''type'' : ({''1b''}), ''bal'' : (Nat), ''maxVBal'' : ((Nat \\cup { -.(1)})), ''maxVal'' : ((Values \\cup {None})), ''acc'' : (Acceptors)]) \\cup [''type'' : ({''2a''}), ''bal'' : (Nat), ''val'' : (Values)]) \\cup [''type'' : ({''2b''}), ''bal'' : (Nat), ''val'' : (Values), ''acc'' : (Acceptors)])) ==> FALSE" (is "?z_hi ==> ?z_hkk ==> ?z_hni ==> ?z_hkm ==> FALSE")
 proof -
  assume z_Hi:"?z_hi"
  assume z_Hkk:"?z_hkk"
  assume z_Hni:"?z_hni" (is "?z_hhc=?z_hbx")
  assume z_Hkm:"?z_hkm"
  show FALSE
  proof (rule zenon_in_addElt [of "(CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=?z_hbx)=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))" "(''type'' :> (''2a'') @@ ''bal'' :> (b) @@ ''val'' :> (v))" "{}", OF z_Hkk])
   assume z_Hji:"((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=?z_hbx)=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))=(''type'' :> (''2a'') @@ ''bal'' :> (b) @@ ''val'' :> (v)))" (is "?z_hhd=?z_hfo")
   have z_Hkn: "(?z_hfm \\subseteq ((([''type'' : ({''1a''}), ''bal'' : (Nat)] \\cup [''type'' : ({''1b''}), ''bal'' : (Nat), ''maxVBal'' : ((Nat \\cup { -.(1)})), ''maxVal'' : ((Values \\cup {None})), ''acc'' : (Acceptors)]) \\cup [''type'' : ({''2a''}), ''bal'' : (Nat), ''val'' : (Values)]) \\cup [''type'' : ({?z_hbx}), ''bal'' : (Nat), ''val'' : (Values), ''acc'' : (Acceptors)]))" (is "?z_hkn")
   by (rule subst [where P="(\<lambda>zenon_Vgvh. (zenon_Vgvh \\subseteq ((([''type'' : ({''1a''}), ''bal'' : (Nat)] \\cup [''type'' : ({''1b''}), ''bal'' : (Nat), ''maxVBal'' : ((Nat \\cup { -.(1)})), ''maxVal'' : ((Values \\cup {None})), ''acc'' : (Acceptors)]) \\cup [''type'' : ({''2a''}), ''bal'' : (Nat), ''val'' : (Values)]) \\cup [''type'' : ({?z_hbx}), ''bal'' : (Nat), ''val'' : (Values), ''acc'' : (Acceptors)])))", OF z_Hi z_Hkm])
   have z_Hkr: "({?z_hfo} \\subseteq ((([''type'' : ({''1a''}), ''bal'' : (Nat)] \\cup [''type'' : ({''1b''}), ''bal'' : (Nat), ''maxVBal'' : ((Nat \\cup { -.(1)})), ''maxVal'' : ((Values \\cup {None})), ''acc'' : (Acceptors)]) \\cup [''type'' : ({''2a''}), ''bal'' : (Nat), ''val'' : (Values)]) \\cup [''type'' : ({?z_hbx}), ''bal'' : (Nat), ''val'' : (Values), ''acc'' : (Acceptors)]))" (is "?z_hkr")
   by (rule zenon_cup_subseteq_1 [of , OF z_Hkn])
   have z_Hks_z_Hkr: "bAll({?z_hfo}, (\<lambda>x. (x \\in ((([''type'' : ({''1a''}), ''bal'' : (Nat)] \\cup [''type'' : ({''1b''}), ''bal'' : (Nat), ''maxVBal'' : ((Nat \\cup { -.(1)})), ''maxVal'' : ((Values \\cup {None})), ''acc'' : (Acceptors)]) \\cup [''type'' : ({''2a''}), ''bal'' : (Nat), ''val'' : (Values)]) \\cup [''type'' : ({?z_hbx}), ''bal'' : (Nat), ''val'' : (Values), ''acc'' : (Acceptors)])))) == ?z_hkr" (is "?z_hks == _")
   by (unfold subset_def)
   have z_Hks: "?z_hks"
   by (unfold z_Hks_z_Hkr, fact z_Hkr)
   have z_Hkv_z_Hks: "(\\A x:((x \\in {?z_hfo})=>(x \\in ((([''type'' : ({''1a''}), ''bal'' : (Nat)] \\cup [''type'' : ({''1b''}), ''bal'' : (Nat), ''maxVBal'' : ((Nat \\cup { -.(1)})), ''maxVal'' : ((Values \\cup {None})), ''acc'' : (Acceptors)]) \\cup [''type'' : ({''2a''}), ''bal'' : (Nat), ''val'' : (Values)]) \\cup [''type'' : ({?z_hbx}), ''bal'' : (Nat), ''val'' : (Values), ''acc'' : (Acceptors)])))) == ?z_hks" (is "?z_hkv == _")
   by (unfold bAll_def)
   have z_Hkv: "?z_hkv" (is "\\A x : ?z_hky(x)")
   by (unfold z_Hkv_z_Hks, fact z_Hks)
   have z_Hkz: "?z_hky(?z_hfo)" (is "?z_hgx=>?z_hla")
   by (rule zenon_all_0 [of "?z_hky" "?z_hfo", OF z_Hkv])
   show FALSE
   proof (rule zenon_imply [OF z_Hkz])
    assume z_Hgw:"(~?z_hgx)"
    show FALSE
    by (rule zenon_L1_ [OF z_Hgw])
   next
    assume z_Hla:"?z_hla"
    show FALSE
    proof (rule zenon_in_cup [of "?z_hfo" "(([''type'' : ({''1a''}), ''bal'' : (Nat)] \\cup [''type'' : ({''1b''}), ''bal'' : (Nat), ''maxVBal'' : ((Nat \\cup { -.(1)})), ''maxVal'' : ((Values \\cup {None})), ''acc'' : (Acceptors)]) \\cup [''type'' : ({''2a''}), ''bal'' : (Nat), ''val'' : (Values)])" "[''type'' : ({?z_hbx}), ''bal'' : (Nat), ''val'' : (Values), ''acc'' : (Acceptors)]", OF z_Hla])
     assume z_Hlb:"(?z_hfo \\in (([''type'' : ({''1a''}), ''bal'' : (Nat)] \\cup [''type'' : ({''1b''}), ''bal'' : (Nat), ''maxVBal'' : ((Nat \\cup { -.(1)})), ''maxVal'' : ((Values \\cup {None})), ''acc'' : (Acceptors)]) \\cup [''type'' : ({''2a''}), ''bal'' : (Nat), ''val'' : (Values)]))" (is "?z_hlb")
     show FALSE
     proof (rule zenon_in_cup [of "?z_hfo" "([''type'' : ({''1a''}), ''bal'' : (Nat)] \\cup [''type'' : ({''1b''}), ''bal'' : (Nat), ''maxVBal'' : ((Nat \\cup { -.(1)})), ''maxVal'' : ((Values \\cup {None})), ''acc'' : (Acceptors)])" "[''type'' : ({''2a''}), ''bal'' : (Nat), ''val'' : (Values)]", OF z_Hlb])
      assume z_Hlc:"(?z_hfo \\in ([''type'' : ({''1a''}), ''bal'' : (Nat)] \\cup [''type'' : ({''1b''}), ''bal'' : (Nat), ''maxVBal'' : ((Nat \\cup { -.(1)})), ''maxVal'' : ((Values \\cup {None})), ''acc'' : (Acceptors)]))" (is "?z_hlc")
      show FALSE
      proof (rule zenon_in_cup [of "?z_hfo" "[''type'' : ({''1a''}), ''bal'' : (Nat)]" "[''type'' : ({''1b''}), ''bal'' : (Nat), ''maxVBal'' : ((Nat \\cup { -.(1)})), ''maxVal'' : ((Values \\cup {None})), ''acc'' : (Acceptors)]", OF z_Hlc])
       assume z_Hld:"(?z_hfo \\in [''type'' : ({''1a''}), ''bal'' : (Nat)])" (is "?z_hld")
       let ?z_hle = "<<''type'', ''bal''>>"
       let ?z_hlf = "<<{''1a''}, Nat>>"
       have z_Hlg: "(1 \\in DOMAIN(?z_hle))" by auto
       have z_Hli: "((?z_hfo[(?z_hle[1])]) \\in (?z_hlf[1]))" (is "?z_hli")
       by (rule zenon_in_recordset_field [OF z_Hld z_Hlg])
       have z_Hlm: "((?z_hfo[''type'']) \\in {''1a''})" (is "?z_hlm")
       using z_Hli by auto
       show FALSE
       proof (rule zenon_in_addElt [of "(?z_hfo[''type''])" "''1a''" "{}", OF z_Hlm])
        assume z_Hln:"((?z_hfo[''type''])=''1a'')" (is "?z_hhb=?z_hz")
        have z_Hnk: "(?z_hz~=?z_hbx)"
        by auto
        have z_Hha: "(?z_hhb~=?z_hhc)"
        by (rule zenon_stringdiffll [OF z_Hnk z_Hln z_Hni])
         show FALSE
         by (rule zenon_L2_ [OF z_Hha z_Hji])
       next
        assume z_Hkj:"((?z_hfo[''type'']) \\in {})" (is "?z_hkj")
        show FALSE
        by (rule zenon_in_emptyset [of "(?z_hfo[''type''])", OF z_Hkj])
       qed
      next
       assume z_Hlp:"(?z_hfo \\in [''type'' : ({''1b''}), ''bal'' : (Nat), ''maxVBal'' : ((Nat \\cup { -.(1)})), ''maxVal'' : ((Values \\cup {None})), ''acc'' : (Acceptors)])" (is "?z_hlp")
       let ?z_hlq = "<<''type'', ''bal'', ''maxVBal'', ''maxVal'', ''acc''>>"
       let ?z_hlr = "<<{''1b''}, Nat, (Nat \\cup { -.(1)}), (Values \\cup {None}), Acceptors>>"
       have z_Hls: "(1 \\in DOMAIN(?z_hlq))" by auto
       have z_Hlu: "((?z_hfo[(?z_hlq[1])]) \\in (?z_hlr[1]))" (is "?z_hlu")
       by (rule zenon_in_recordset_field [OF z_Hlp z_Hls])
       have z_Hly: "((?z_hfo[''type'']) \\in {''1b''})" (is "?z_hly")
       using z_Hlu by auto
       show FALSE
       proof (rule zenon_in_addElt [of "(?z_hfo[''type''])" "''1b''" "{}", OF z_Hly])
        assume z_Hlz:"((?z_hfo[''type''])=''1b'')" (is "?z_hhb=?z_hbe")
        have z_Hnl: "(?z_hbe~=?z_hbx)"
        by auto
        have z_Hha: "(?z_hhb~=?z_hhc)"
        by (rule zenon_stringdiffll [OF z_Hnl z_Hlz z_Hni])
         show FALSE
         by (rule zenon_L2_ [OF z_Hha z_Hji])
       next
        assume z_Hkj:"((?z_hfo[''type'']) \\in {})" (is "?z_hkj")
        show FALSE
        by (rule zenon_in_emptyset [of "(?z_hfo[''type''])", OF z_Hkj])
       qed
      qed
     next
      assume z_Hmf:"(?z_hfo \\in [''type'' : ({''2a''}), ''bal'' : (Nat), ''val'' : (Values)])" (is "?z_hmf")
      let ?z_hmg = "<<''type'', ''bal'', ''val''>>"
      let ?z_hmh = "<<{''2a''}, Nat, Values>>"
      have z_Hmi: "(1 \\in DOMAIN(?z_hmg))" by auto
      have z_Hmk: "((?z_hfo[(?z_hmg[1])]) \\in (?z_hmh[1]))" (is "?z_hmk")
      by (rule zenon_in_recordset_field [OF z_Hmf z_Hmi])
      have z_Hmo: "((?z_hfo[''type'']) \\in {''2a''})" (is "?z_hmo")
      using z_Hmk by auto
      show FALSE
      proof (rule zenon_in_addElt [of "(?z_hfo[''type''])" "''2a''" "{}", OF z_Hmo])
       assume z_Hkd:"((?z_hfo[''type''])=''2a'')" (is "?z_hhb=?z_hbt")
       have z_Hki: "(?z_hbt~=?z_hbx)"
       by auto
       have z_Hha: "(?z_hhb~=?z_hhc)"
       by (rule zenon_stringdiffll [OF z_Hki z_Hkd z_Hni])
        show FALSE
        by (rule zenon_L2_ [OF z_Hha z_Hji])
      next
       assume z_Hkj:"((?z_hfo[''type'']) \\in {})" (is "?z_hkj")
       show FALSE
       by (rule zenon_in_emptyset [of "(?z_hfo[''type''])", OF z_Hkj])
      qed
     qed
    next
     assume z_Hjp:"(?z_hfo \\in [''type'' : ({?z_hbx}), ''bal'' : (Nat), ''val'' : (Values), ''acc'' : (Acceptors)])" (is "?z_hjp")
     show FALSE
     by (rule zenon_L3_ [OF z_Hjp])
    qed
   qed
  next
   assume z_Hmp:"((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=?z_hbx)=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])]))))))))) \\in {})" (is "?z_hmp")
   show FALSE
   by (rule zenon_in_emptyset [of "(CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=?z_hbx)=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))", OF z_Hmp])
  qed
 qed
 assume z_Hn:"(~bAll(a_msgshash_primea, (\<lambda>m. ((((m[''type''])=''1b'')=>(((m[''bal'']) <= (a_maxBalhash_primea[(m[''acc''])]))&(((((m[''maxVal'']) \\in Values)&(((m[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((m[''acc'']), (m[''maxVal'']), (m[''maxVBal'']))))|(((m[''maxVal''])=None)&((m[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((m[''maxVBal'']) + 1), ((m[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((m[''acc'']), v_1, a_ca)))))))))&((((m[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((m[''val'']), (m[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(m[''bal''])))=>(ma=m))))))&(((m[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(m[''bal'']))&((ma[''val''])=(m[''val'']))))))&((m[''bal'']) <= (a_maxVBalhash_primea[(m[''acc''])])))))))))" (is "~?z_hnm")
 have z_Ho: "?z_ho" (is "?z_hp&?z_hcp")
 by (rule zenon_and_0 [OF z_Ha])
 have z_Hez: "AccInv"
 by (rule zenon_and_1 [OF z_Ha])
 have z_Hp: "?z_hp" (is "?z_hq&?z_hby")
 by (rule zenon_and_0 [OF z_Ho])
 have z_Hcp: "?z_hcp"
 by (rule zenon_and_1 [OF z_Ho])
 have z_Hq: "?z_hq"
 by (rule zenon_and_0 [OF z_Hp])
 have z_Hby: "?z_hby" (is "?z_hbz&?z_hcc")
 by (rule zenon_and_1 [OF z_Hp])
 have z_Hbz: "?z_hbz"
 by (rule zenon_and_0 [OF z_Hby])
 have z_Hcc: "?z_hcc" (is "?z_hcd&?z_hcf")
 by (rule zenon_and_1 [OF z_Hby])
 have z_Hcd: "?z_hcd"
 by (rule zenon_and_0 [OF z_Hcc])
 have z_Hcf: "?z_hcf" (is "?z_hcg&?z_hcj")
 by (rule zenon_and_1 [OF z_Hcc])
 have z_Hcg: "?z_hcg"
 by (rule zenon_and_0 [OF z_Hcf])
 have z_Hcj: "?z_hcj"
 by (rule zenon_and_1 [OF z_Hcf])
 have z_Hoo_z_Hcp: "(\\A x:((x \\in msgs)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (maxBal[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&VotedForIn((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v. VotedForIn((x[''acc'']), v, a_ca)))))))))&((((x[''type''])=''2a'')=>(SafeAt((x[''val'']), (x[''bal'']))&bAll(msgs, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(msgs, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (maxVBal[(x[''acc''])])))))))) == ?z_hcp" (is "?z_hoo == _")
 by (unfold bAll_def)
 have z_Hoo: "?z_hoo" (is "\\A x : ?z_hpr(x)")
 by (unfold z_Hoo_z_Hcp, fact z_Hcp)
 have z_Hga: "?z_hga"
 by (rule zenon_and_0 [OF z_He])
 have z_Hgb: "?z_hgb" (is "?z_hgc&?z_hgd")
 by (rule zenon_and_1 [OF z_He])
 have z_Hgc: "?z_hgc"
 by (rule zenon_and_0 [OF z_Hgb])
 have z_Hgd: "?z_hgd" (is "?z_hge&?z_hgf")
 by (rule zenon_and_1 [OF z_Hgb])
 have z_Hge: "?z_hge"
 by (rule zenon_and_0 [OF z_Hgd])
 have z_Hgf: "?z_hgf" (is "?z_hgg&?z_hgi")
 by (rule zenon_and_1 [OF z_Hgd])
 have z_Hgg: "?z_hgg"
 by (rule zenon_and_0 [OF z_Hgf])
 have z_Hgi: "?z_hgi"
 by (rule zenon_and_1 [OF z_Hgf])
 have z_Hkm: "(a_msgshash_primea \\subseteq ((([''type'' : ({''1a''}), ''bal'' : (Nat)] \\cup [''type'' : ({''1b''}), ''bal'' : (Nat), ''maxVBal'' : ((Nat \\cup { -.(1)})), ''maxVal'' : ((Values \\cup {None})), ''acc'' : (Acceptors)]) \\cup [''type'' : ({''2a''}), ''bal'' : (Nat), ''val'' : (Values)]) \\cup [''type'' : ({''2b''}), ''bal'' : (Nat), ''val'' : (Values), ''acc'' : (Acceptors)]))" (is "?z_hkm")
 by (rule zenon_in_SUBSET_0 [of "a_msgshash_primea" "((([''type'' : ({''1a''}), ''bal'' : (Nat)] \\cup [''type'' : ({''1b''}), ''bal'' : (Nat), ''maxVBal'' : ((Nat \\cup { -.(1)})), ''maxVal'' : ((Values \\cup {None})), ''acc'' : (Acceptors)]) \\cup [''type'' : ({''2a''}), ''bal'' : (Nat), ''val'' : (Values)]) \\cup [''type'' : ({''2b''}), ''bal'' : (Nat), ''val'' : (Values), ''acc'' : (Acceptors)])", OF z_Hga])
 have z_Hps_z_Hkm: "bAll(a_msgshash_primea, (\<lambda>x. (x \\in ((([''type'' : ({''1a''}), ''bal'' : (Nat)] \\cup [''type'' : ({''1b''}), ''bal'' : (Nat), ''maxVBal'' : ((Nat \\cup { -.(1)})), ''maxVal'' : ((Values \\cup {None})), ''acc'' : (Acceptors)]) \\cup [''type'' : ({''2a''}), ''bal'' : (Nat), ''val'' : (Values)]) \\cup [''type'' : ({''2b''}), ''bal'' : (Nat), ''val'' : (Values), ''acc'' : (Acceptors)])))) == ?z_hkm" (is "?z_hps == _")
 by (unfold subset_def)
 have z_Hps: "?z_hps"
 by (unfold z_Hps_z_Hkm, fact z_Hkm)
 have z_Hpt_z_Hk: "(\\A x:((x \\in a_msgshash_primea)=>bAll(a_msgshash_primea, (\<lambda>ma. (((((x[''type''])=''2a'')&((ma[''type''])=''2a''))&((ma[''bal''])=(x[''bal''])))=>(ma=x)))))) == ?z_hk" (is "?z_hpt == _")
 by (unfold bAll_def)
 have z_Hpt: "?z_hpt" (is "\\A x : ?z_hqa(x)")
 by (unfold z_Hpt_z_Hk, fact z_Hk)
 have z_Hqb_z_Hn: "(~(\\A x:((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])]))))))))) == (~?z_hnm)" (is "?z_hqb == ?z_hn")
 by (unfold bAll_def)
 have z_Hqb: "?z_hqb" (is "~(\\A x : ?z_hqd(x))")
 by (unfold z_Hqb_z_Hn, fact z_Hn)
 have z_Hqe: "(\\E x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))" (is "\\E x : ?z_hqf(x)")
 by (rule zenon_notallex_0 [of "?z_hqd", OF z_Hqb])
 have z_Hqg: "?z_hqf((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])]))))))))))" (is "~(?z_hqh=>?z_hqi)")
 by (rule zenon_ex_choose_0 [of "?z_hqf", OF z_Hqe])
 have z_Hqh: "?z_hqh"
 by (rule zenon_notimply_0 [OF z_Hqg])
 have z_Hqj: "(~?z_hqi)" (is "~(?z_hqk&?z_hql)")
 by (rule zenon_notimply_1 [OF z_Hqg])
 show FALSE
 proof (rule zenon_notand [OF z_Hqj])
  assume z_Hqm:"(~?z_hqk)" (is "~(?z_hkl=>?z_hqn)")
  have z_Hkl: "?z_hkl" (is "?z_hhc=?z_hbe")
  by (rule zenon_notimply_0 [OF z_Hqm])
  have z_Hqo: "(~?z_hqn)" (is "~(?z_hqp&?z_hqq)")
  by (rule zenon_notimply_1 [OF z_Hqm])
  show FALSE
  proof (rule zenon_notand [OF z_Hqo])
   assume z_Hqr:"(~?z_hqp)"
   have z_Hqs: "(~(((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''bal'']) <= (maxBal[((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''acc''])])))" (is "~?z_hqt")
   by (rule subst [where P="(\<lambda>zenon_Vcvh. (~(((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''bal'']) <= (zenon_Vcvh[((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''acc''])]))))", OF z_Hf z_Hqr])
   have z_Hrc: "((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])]))))))))) \\in ?z_hfm)" (is "?z_hrc")
   by (rule subst [where P="(\<lambda>zenon_Vevh. ((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])]))))))))) \\in zenon_Vevh))", OF z_Hi z_Hqh])
   show FALSE
   proof (rule zenon_in_cup [of "(CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))" "msgs" "{(''type'' :> (''2a'') @@ ''bal'' :> (b) @@ ''val'' :> (v))}", OF z_Hrc])
    assume z_Hrg:"((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])]))))))))) \\in msgs)" (is "?z_hrg")
    have z_Hrh: "?z_hpr((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])]))))))))))" (is "_=>?z_hri")
    by (rule zenon_all_0 [of "?z_hpr" "(CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))", OF z_Hoo])
    show FALSE
    proof (rule zenon_imply [OF z_Hrh])
     assume z_Hrj:"(~?z_hrg)"
     show FALSE
     by (rule notE [OF z_Hrj z_Hrg])
    next
     assume z_Hri:"?z_hri" (is "?z_hrk&?z_hrl")
     have z_Hrk: "?z_hrk" (is "_=>?z_hrm")
     by (rule zenon_and_0 [OF z_Hri])
     show FALSE
     proof (rule zenon_imply [OF z_Hrk])
      assume z_Hrn:"(?z_hhc~=?z_hbe)"
      show FALSE
      by (rule notE [OF z_Hrn z_Hkl])
     next
      assume z_Hrm:"?z_hrm" (is "_&?z_hro")
      have z_Hqt: "?z_hqt"
      by (rule zenon_and_0 [OF z_Hrm])
      show FALSE
      by (rule notE [OF z_Hqs z_Hqt])
     qed
    qed
   next
    assume z_Hkk:"((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])]))))))))) \\in {(''type'' :> (''2a'') @@ ''bal'' :> (b) @@ ''val'' :> (v))})" (is "?z_hkk")
    show FALSE
    by (rule zenon_L4_ [OF z_Hi z_Hkk z_Hkl z_Hkm])
   qed
  next
   assume z_Hrp:"(~?z_hqq)" (is "~(?z_hrq&?z_hrr)")
   show FALSE
   proof (rule zenon_notand [OF z_Hrp])
    assume z_Hrs:"(~?z_hrq)" (is "~(?z_hrt|?z_hru)")
    have z_Hrv: "(~?z_hrt)" (is "~(?z_hrw&?z_hrx)")
    by (rule zenon_notor_0 [OF z_Hrs])
    have z_Hry: "(~?z_hru)" (is "~(?z_hrz&?z_hsa)")
    by (rule zenon_notor_1 [OF z_Hrs])
    show FALSE
    proof (rule zenon_notand [OF z_Hrv])
     assume z_Hsb:"(~?z_hrw)"
     have z_Hrc: "((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])]))))))))) \\in ?z_hfm)" (is "?z_hrc")
     by (rule subst [where P="(\<lambda>zenon_Vevh. ((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])]))))))))) \\in zenon_Vevh))", OF z_Hi z_Hqh])
     show FALSE
     proof (rule zenon_in_cup [of "(CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))" "msgs" "{(''type'' :> (''2a'') @@ ''bal'' :> (b) @@ ''val'' :> (v))}", OF z_Hrc])
      assume z_Hrg:"((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])]))))))))) \\in msgs)" (is "?z_hrg")
      have z_Hrh: "?z_hpr((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])]))))))))))" (is "_=>?z_hri")
      by (rule zenon_all_0 [of "?z_hpr" "(CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))", OF z_Hoo])
      show FALSE
      proof (rule zenon_imply [OF z_Hrh])
       assume z_Hrj:"(~?z_hrg)"
       show FALSE
       by (rule notE [OF z_Hrj z_Hrg])
      next
       assume z_Hri:"?z_hri" (is "?z_hrk&?z_hrl")
       have z_Hrk: "?z_hrk" (is "_=>?z_hrm")
       by (rule zenon_and_0 [OF z_Hri])
       show FALSE
       proof (rule zenon_imply [OF z_Hrk])
        assume z_Hrn:"(?z_hhc~=?z_hbe)"
        show FALSE
        by (rule notE [OF z_Hrn z_Hkl])
       next
        assume z_Hrm:"?z_hrm" (is "?z_hqt&?z_hro")
        have z_Hro: "?z_hro" (is "?z_hsc&?z_hsd")
        by (rule zenon_and_1 [OF z_Hrm])
        have z_Hsc: "?z_hsc" (is "?z_hse|_")
        by (rule zenon_and_0 [OF z_Hro])
        show FALSE
        proof (rule zenon_or [OF z_Hsc])
         assume z_Hse:"?z_hse" (is "_&?z_hsf")
         have z_Hrw: "?z_hrw"
         by (rule zenon_and_0 [OF z_Hse])
         show FALSE
         by (rule notE [OF z_Hsb z_Hrw])
        next
         assume z_Hru:"?z_hru"
         show FALSE
         by (rule notE [OF z_Hry z_Hru])
        qed
       qed
      qed
     next
      assume z_Hkk:"((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])]))))))))) \\in {(''type'' :> (''2a'') @@ ''bal'' :> (b) @@ ''val'' :> (v))})" (is "?z_hkk")
      show FALSE
      by (rule zenon_L4_ [OF z_Hi z_Hkk z_Hkl z_Hkm])
     qed
    next
     assume z_Hsg:"(~?z_hrx)" (is "~(?z_hsh&?z_hsi)")
     show FALSE
     proof (rule zenon_notand [OF z_Hsg])
      assume z_Hsj:"(~?z_hsh)"
      have z_Hrc: "((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])]))))))))) \\in ?z_hfm)" (is "?z_hrc")
      by (rule subst [where P="(\<lambda>zenon_Vevh. ((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])]))))))))) \\in zenon_Vevh))", OF z_Hi z_Hqh])
      show FALSE
      proof (rule zenon_in_cup [of "(CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))" "msgs" "{(''type'' :> (''2a'') @@ ''bal'' :> (b) @@ ''val'' :> (v))}", OF z_Hrc])
       assume z_Hrg:"((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])]))))))))) \\in msgs)" (is "?z_hrg")
       have z_Hrh: "?z_hpr((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])]))))))))))" (is "_=>?z_hri")
       by (rule zenon_all_0 [of "?z_hpr" "(CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))", OF z_Hoo])
       show FALSE
       proof (rule zenon_imply [OF z_Hrh])
        assume z_Hrj:"(~?z_hrg)"
        show FALSE
        by (rule notE [OF z_Hrj z_Hrg])
       next
        assume z_Hri:"?z_hri" (is "?z_hrk&?z_hrl")
        have z_Hrk: "?z_hrk" (is "_=>?z_hrm")
        by (rule zenon_and_0 [OF z_Hri])
        show FALSE
        proof (rule zenon_imply [OF z_Hrk])
         assume z_Hrn:"(?z_hhc~=?z_hbe)"
         show FALSE
         by (rule notE [OF z_Hrn z_Hkl])
        next
         assume z_Hrm:"?z_hrm" (is "?z_hqt&?z_hro")
         have z_Hro: "?z_hro" (is "?z_hsc&?z_hsd")
         by (rule zenon_and_1 [OF z_Hrm])
         have z_Hsc: "?z_hsc" (is "?z_hse|_")
         by (rule zenon_and_0 [OF z_Hro])
         show FALSE
         proof (rule zenon_or [OF z_Hsc])
          assume z_Hse:"?z_hse" (is "_&?z_hsf")
          have z_Hsf: "?z_hsf" (is "_&?z_hsk")
          by (rule zenon_and_1 [OF z_Hse])
          have z_Hsh: "?z_hsh"
          by (rule zenon_and_0 [OF z_Hsf])
          show FALSE
          by (rule notE [OF z_Hsj z_Hsh])
         next
          assume z_Hru:"?z_hru"
          show FALSE
          by (rule notE [OF z_Hry z_Hru])
         qed
        qed
       qed
      next
       assume z_Hkk:"((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])]))))))))) \\in {(''type'' :> (''2a'') @@ ''bal'' :> (b) @@ ''val'' :> (v))})" (is "?z_hkk")
       show FALSE
       by (rule zenon_L4_ [OF z_Hi z_Hkk z_Hkl z_Hkm])
      qed
     next
      assume z_Hsl:"(~?z_hsi)"
      have z_Hsm: "?z_hfj(((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''acc'']))" (is "\\A x : ?z_hsn(x)")
      by (rule zenon_all_0 [of "?z_hfj" "((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''acc''])", OF z_Hj])
      have z_Hso: "?z_hsn(((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''maxVal'']))" (is "\\A x : ?z_hsq(x)")
      by (rule zenon_all_0 [of "?z_hsn" "((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''maxVal''])", OF z_Hsm])
      have z_Hsr: "?z_hsq(((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''maxVBal'']))" (is "_<=>?z_hsk")
      by (rule zenon_all_0 [of "?z_hsq" "((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''maxVBal''])", OF z_Hso])
      show FALSE
      proof (rule zenon_equiv [OF z_Hsr])
       assume z_Hsl:"(~?z_hsi)"
       assume z_Hst:"(~?z_hsk)"
       have z_Hrc: "((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])]))))))))) \\in ?z_hfm)" (is "?z_hrc")
       by (rule subst [where P="(\<lambda>zenon_Vevh. ((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])]))))))))) \\in zenon_Vevh))", OF z_Hi z_Hqh])
       show FALSE
       proof (rule zenon_in_cup [of "(CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))" "msgs" "{(''type'' :> (''2a'') @@ ''bal'' :> (b) @@ ''val'' :> (v))}", OF z_Hrc])
        assume z_Hrg:"((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])]))))))))) \\in msgs)" (is "?z_hrg")
        have z_Hrh: "?z_hpr((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])]))))))))))" (is "_=>?z_hri")
        by (rule zenon_all_0 [of "?z_hpr" "(CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))", OF z_Hoo])
        show FALSE
        proof (rule zenon_imply [OF z_Hrh])
         assume z_Hrj:"(~?z_hrg)"
         show FALSE
         by (rule notE [OF z_Hrj z_Hrg])
        next
         assume z_Hri:"?z_hri" (is "?z_hrk&?z_hrl")
         have z_Hrk: "?z_hrk" (is "_=>?z_hrm")
         by (rule zenon_and_0 [OF z_Hri])
         show FALSE
         proof (rule zenon_imply [OF z_Hrk])
          assume z_Hrn:"(?z_hhc~=?z_hbe)"
          show FALSE
          by (rule notE [OF z_Hrn z_Hkl])
         next
          assume z_Hrm:"?z_hrm" (is "?z_hqt&?z_hro")
          have z_Hro: "?z_hro" (is "?z_hsc&?z_hsd")
          by (rule zenon_and_1 [OF z_Hrm])
          have z_Hsc: "?z_hsc" (is "?z_hse|_")
          by (rule zenon_and_0 [OF z_Hro])
          show FALSE
          proof (rule zenon_or [OF z_Hsc])
           assume z_Hse:"?z_hse" (is "_&?z_hsf")
           have z_Hsf: "?z_hsf"
           by (rule zenon_and_1 [OF z_Hse])
           have z_Hsk: "?z_hsk"
           by (rule zenon_and_1 [OF z_Hsf])
           show FALSE
           by (rule notE [OF z_Hst z_Hsk])
          next
           assume z_Hru:"?z_hru"
           show FALSE
           by (rule notE [OF z_Hry z_Hru])
          qed
         qed
        qed
       next
        assume z_Hkk:"((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])]))))))))) \\in {(''type'' :> (''2a'') @@ ''bal'' :> (b) @@ ''val'' :> (v))})" (is "?z_hkk")
        show FALSE
        by (rule zenon_L4_ [OF z_Hi z_Hkk z_Hkl z_Hkm])
       qed
      next
       assume z_Hsi:"?z_hsi"
       assume z_Hsk:"?z_hsk"
       show FALSE
       by (rule notE [OF z_Hsl z_Hsi])
      qed
     qed
    qed
   next
    assume z_Hsu:"(~?z_hrr)"
    have z_Hsv_z_Hsu: "(~(\\A x:((x \\in isa'dotdot((((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''maxVBal'']) + 1), (((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''bal'']) +  -.(1))))=>(~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a(((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''acc'']), v_1, x))))))) == (~?z_hrr)" (is "?z_hsv == ?z_hsu")
    by (unfold bAll_def)
    have z_Hsv: "?z_hsv" (is "~(\\A x : ?z_htg(x))")
    by (unfold z_Hsv_z_Hsu, fact z_Hsu)
    have z_Hth: "(\\E x:(~((x \\in isa'dotdot((((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''maxVBal'']) + 1), (((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''bal'']) +  -.(1))))=>(~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a(((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''acc'']), v_1, x)))))))" (is "\\E x : ?z_htj(x)")
    by (rule zenon_notallex_0 [of "?z_htg", OF z_Hsv])
    have z_Htk: "?z_htj((CHOOSE x:(~((x \\in isa'dotdot((((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''maxVBal'']) + 1), (((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''bal'']) +  -.(1))))=>(~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a(((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''acc'']), v_1, x))))))))" (is "~(?z_htm=>?z_htn)")
    by (rule zenon_ex_choose_0 [of "?z_htj", OF z_Hth])
    have z_Htm: "?z_htm"
    by (rule zenon_notimply_0 [OF z_Htk])
    have z_Hto: "(~?z_htn)" (is "~~?z_htp")
    by (rule zenon_notimply_1 [OF z_Htk])
    have z_Htp: "?z_htp"
    by (rule zenon_notnot_0 [OF z_Hto])
    have z_Htq_z_Htp: "(\\E x:((x \\in Values)&a_h03062837f0f10c4714e0f53023b1a7a(((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''acc'']), x, (CHOOSE x:(~((x \\in isa'dotdot((((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''maxVBal'']) + 1), (((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''bal'']) +  -.(1))))=>(~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a(((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''acc'']), v_1, x)))))))))) == ?z_htp" (is "?z_htq == _")
    by (unfold bEx_def)
    have z_Htq: "?z_htq" (is "\\E x : ?z_htu(x)")
    by (unfold z_Htq_z_Htp, fact z_Htp)
    have z_Htv: "?z_htu((CHOOSE x:((x \\in Values)&a_h03062837f0f10c4714e0f53023b1a7a(((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''acc'']), x, (CHOOSE x:(~((x \\in isa'dotdot((((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''maxVBal'']) + 1), (((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''bal'']) +  -.(1))))=>(~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a(((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''acc'']), v_1, x)))))))))))" (is "?z_htx&?z_hty")
    by (rule zenon_ex_choose_0 [of "?z_htu", OF z_Htq])
    have z_Htx: "?z_htx"
    by (rule zenon_and_0 [OF z_Htv])
    have z_Hty: "?z_hty"
    by (rule zenon_and_1 [OF z_Htv])
    have z_Hsm: "?z_hfj(((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''acc'']))" (is "\\A x : ?z_hsn(x)")
    by (rule zenon_all_0 [of "?z_hfj" "((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''acc''])", OF z_Hj])
    have z_Htz: "?z_hsn((CHOOSE x:((x \\in Values)&a_h03062837f0f10c4714e0f53023b1a7a(((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''acc'']), x, (CHOOSE x:(~((x \\in isa'dotdot((((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''maxVBal'']) + 1), (((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''bal'']) +  -.(1))))=>(~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a(((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''acc'']), v_1, x)))))))))))" (is "\\A x : ?z_hua(x)")
    by (rule zenon_all_0 [of "?z_hsn" "(CHOOSE x:((x \\in Values)&a_h03062837f0f10c4714e0f53023b1a7a(((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''acc'']), x, (CHOOSE x:(~((x \\in isa'dotdot((((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''maxVBal'']) + 1), (((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''bal'']) +  -.(1))))=>(~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a(((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''acc'']), v_1, x))))))))))", OF z_Hsm])
    have z_Hub: "?z_hua((CHOOSE x:(~((x \\in isa'dotdot((((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''maxVBal'']) + 1), (((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''bal'']) +  -.(1))))=>(~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a(((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''acc'']), v_1, x))))))))" (is "_<=>?z_huc")
    by (rule zenon_all_0 [of "?z_hua" "(CHOOSE x:(~((x \\in isa'dotdot((((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''maxVBal'']) + 1), (((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''bal'']) +  -.(1))))=>(~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a(((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''acc'']), v_1, x)))))))", OF z_Htz])
    show FALSE
    proof (rule zenon_equiv [OF z_Hub])
     assume z_Hud:"(~?z_hty)"
     assume z_Hue:"(~?z_huc)"
     show FALSE
     by (rule notE [OF z_Hud z_Hty])
    next
     assume z_Hty:"?z_hty"
     assume z_Huc:"?z_huc"
     have z_Hrc: "((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])]))))))))) \\in ?z_hfm)" (is "?z_hrc")
     by (rule subst [where P="(\<lambda>zenon_Vevh. ((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])]))))))))) \\in zenon_Vevh))", OF z_Hi z_Hqh])
     show FALSE
     proof (rule zenon_in_cup [of "(CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))" "msgs" "{(''type'' :> (''2a'') @@ ''bal'' :> (b) @@ ''val'' :> (v))}", OF z_Hrc])
      assume z_Hrg:"((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])]))))))))) \\in msgs)" (is "?z_hrg")
      have z_Hrh: "?z_hpr((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])]))))))))))" (is "_=>?z_hri")
      by (rule zenon_all_0 [of "?z_hpr" "(CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))", OF z_Hoo])
      show FALSE
      proof (rule zenon_imply [OF z_Hrh])
       assume z_Hrj:"(~?z_hrg)"
       show FALSE
       by (rule notE [OF z_Hrj z_Hrg])
      next
       assume z_Hri:"?z_hri" (is "?z_hrk&?z_hrl")
       have z_Hrk: "?z_hrk" (is "_=>?z_hrm")
       by (rule zenon_and_0 [OF z_Hri])
       show FALSE
       proof (rule zenon_imply [OF z_Hrk])
        assume z_Hrn:"(?z_hhc~=?z_hbe)"
        show FALSE
        by (rule notE [OF z_Hrn z_Hkl])
       next
        assume z_Hrm:"?z_hrm" (is "?z_hqt&?z_hro")
        have z_Hro: "?z_hro" (is "?z_hsc&?z_hsd")
        by (rule zenon_and_1 [OF z_Hrm])
        have z_Hsd: "?z_hsd"
        by (rule zenon_and_1 [OF z_Hro])
        have z_Huf_z_Hsd: "(\\A x:((x \\in isa'dotdot((((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''maxVBal'']) + 1), (((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''bal'']) +  -.(1))))=>(~bEx(Values, (\<lambda>v. VotedForIn(((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''acc'']), v, x)))))) == ?z_hsd" (is "?z_huf == _")
        by (unfold bAll_def)
        have z_Huf: "?z_huf" (is "\\A x : ?z_hul(x)")
        by (unfold z_Huf_z_Hsd, fact z_Hsd)
        have z_Hum: "?z_hul((CHOOSE x:(~((x \\in isa'dotdot((((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''maxVBal'']) + 1), (((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''bal'']) +  -.(1))))=>(~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a(((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''acc'']), v_1, x))))))))" (is "_=>?z_hun")
        by (rule zenon_all_0 [of "?z_hul" "(CHOOSE x:(~((x \\in isa'dotdot((((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''maxVBal'']) + 1), (((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''bal'']) +  -.(1))))=>(~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a(((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''acc'']), v_1, x)))))))", OF z_Huf])
        show FALSE
        proof (rule zenon_imply [OF z_Hum])
         assume z_Huo:"(~?z_htm)"
         show FALSE
         by (rule notE [OF z_Huo z_Htm])
        next
         assume z_Hun:"?z_hun" (is "~?z_hup")
         have z_Huq_z_Hun: "(~(\\E x:((x \\in Values)&VotedForIn(((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''acc'']), x, (CHOOSE x:(~((x \\in isa'dotdot((((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''maxVBal'']) + 1), (((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''bal'']) +  -.(1))))=>(~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a(((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''acc'']), v_1, x))))))))))) == ?z_hun" (is "?z_huq == _")
         by (unfold bEx_def)
         have z_Huq: "?z_huq" (is "~(\\E x : ?z_huu(x))")
         by (unfold z_Huq_z_Hun, fact z_Hun)
         have z_Huv: "~?z_huu((CHOOSE x:((x \\in Values)&a_h03062837f0f10c4714e0f53023b1a7a(((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''acc'']), x, (CHOOSE x:(~((x \\in isa'dotdot((((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''maxVBal'']) + 1), (((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''bal'']) +  -.(1))))=>(~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a(((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''acc'']), v_1, x)))))))))))"
         by (rule zenon_notex_0 [of "?z_huu" "(CHOOSE x:((x \\in Values)&a_h03062837f0f10c4714e0f53023b1a7a(((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''acc'']), x, (CHOOSE x:(~((x \\in isa'dotdot((((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''maxVBal'']) + 1), (((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''bal'']) +  -.(1))))=>(~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a(((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''acc'']), v_1, x))))))))))", OF z_Huq])
         show FALSE
         proof (rule zenon_notand [OF z_Huv])
          assume z_Huw:"(~?z_htx)"
          show FALSE
          by (rule notE [OF z_Huw z_Htx])
         next
          assume z_Hue:"(~?z_huc)"
          show FALSE
          by (rule notE [OF z_Hue z_Huc])
         qed
        qed
       qed
      qed
     next
      assume z_Hkk:"((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=?z_hbe)=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])]))))))))) \\in {(''type'' :> (''2a'') @@ ''bal'' :> (b) @@ ''val'' :> (v))})" (is "?z_hkk")
      show FALSE
      by (rule zenon_L4_ [OF z_Hi z_Hkk z_Hkl z_Hkm])
     qed
    qed
   qed
  qed
 next
  assume z_Hux:"(~?z_hql)" (is "~(?z_huy&?z_huz)")
  show FALSE
  proof (rule zenon_notand [OF z_Hux])
   assume z_Hva:"(~?z_huy)" (is "~(?z_hmr=>?z_hvb)")
   have z_Hmr: "?z_hmr" (is "?z_hhc=?z_hbt")
   by (rule zenon_notimply_0 [OF z_Hva])
   have z_Hvc: "(~?z_hvb)" (is "~(?z_hvd&?z_hve)")
   by (rule zenon_notimply_1 [OF z_Hva])
   show FALSE
   proof (rule zenon_notand [OF z_Hvc])
    assume z_Hvf:"(~?z_hvd)"
    show FALSE
    proof (rule zenon_imply [OF z_Hm])
     assume z_Hvg:"(~?z_hfy)" (is "~(?z_hfz&?z_he)")
     show FALSE
     proof (rule zenon_notand [OF z_Hvg])
      assume z_Hvh:"(~?z_hfz)" (is "~(?z_ha&_)")
      show FALSE
      proof (rule zenon_notand [OF z_Hvh])
       assume z_Hvi:"(~?z_ha)"
       show FALSE
       proof (rule zenon_notand [OF z_Hvi])
        assume z_Hvj:"(~?z_ho)"
        show FALSE
        proof (rule zenon_notand [OF z_Hvj])
         assume z_Hvk:"(~?z_hp)"
         show FALSE
         proof (rule zenon_notand [OF z_Hvk])
          assume z_Hvl:"(~?z_hq)"
          show FALSE
          by (rule notE [OF z_Hvl z_Hq])
         next
          assume z_Hvm:"(~?z_hby)"
          show FALSE
          proof (rule zenon_notand [OF z_Hvm])
           assume z_Hvn:"(~?z_hbz)"
           show FALSE
           by (rule notE [OF z_Hvn z_Hbz])
          next
           assume z_Hvo:"(~?z_hcc)"
           show FALSE
           proof (rule zenon_notand [OF z_Hvo])
            assume z_Hvp:"(~?z_hcd)"
            show FALSE
            by (rule notE [OF z_Hvp z_Hcd])
           next
            assume z_Hvq:"(~?z_hcf)"
            show FALSE
            proof (rule zenon_notand [OF z_Hvq])
             assume z_Hvr:"(~?z_hcg)"
             show FALSE
             by (rule notE [OF z_Hvr z_Hcg])
            next
             assume z_Hvs:"(~?z_hcj)"
             show FALSE
             by (rule notE [OF z_Hvs z_Hcj])
            qed
           qed
          qed
         qed
        next
         assume z_Hvt:"(~?z_hcp)"
         show FALSE
         by (rule notE [OF z_Hvt z_Hcp])
        qed
       next
        assume z_Hvu:"(~AccInv)"
        show FALSE
        by (rule notE [OF z_Hvu z_Hez])
       qed
      next
       assume z_Hvv:"(~Next)"
       show FALSE
       by (rule notE [OF z_Hvv z_Hb])
      qed
     next
      assume z_Hvw:"(~?z_he)"
      show FALSE
      proof (rule zenon_notand [OF z_Hvw])
       assume z_Hvx:"(~?z_hga)"
       show FALSE
       by (rule notE [OF z_Hvx z_Hga])
      next
       assume z_Hvy:"(~?z_hgb)"
       show FALSE
       proof (rule zenon_notand [OF z_Hvy])
        assume z_Hvz:"(~?z_hgc)"
        show FALSE
        by (rule notE [OF z_Hvz z_Hgc])
       next
        assume z_Hwa:"(~?z_hgd)"
        show FALSE
        proof (rule zenon_notand [OF z_Hwa])
         assume z_Hwb:"(~?z_hge)"
         show FALSE
         by (rule notE [OF z_Hwb z_Hge])
        next
         assume z_Hwc:"(~?z_hgf)"
         show FALSE
         proof (rule zenon_notand [OF z_Hwc])
          assume z_Hwd:"(~?z_hgg)"
          show FALSE
          by (rule notE [OF z_Hwd z_Hgg])
         next
          assume z_Hwe:"(~?z_hgi)"
          show FALSE
          by (rule notE [OF z_Hwe z_Hgi])
         qed
        qed
       qed
      qed
     qed
    next
     assume z_Hgn:"?z_hgn"
     have z_Hwf_z_Hgn: "(\\A x:((x \\in Values)=>bAll(Nat, (\<lambda>b_1. (SafeAt(x, b_1)=>a_hd4a7fa801d94bc2a9c69d39a405ea2a(x, b_1)))))) == ?z_hgn" (is "?z_hwf == _")
     by (unfold bAll_def)
     have z_Hwf: "?z_hwf" (is "\\A x : ?z_hwm(x)")
     by (unfold z_Hwf_z_Hgn, fact z_Hgn)
     have z_Hrc: "((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=?z_hbt)=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=?z_hbt)&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=?z_hbt)&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])]))))))))) \\in ?z_hfm)" (is "?z_hrc")
     by (rule subst [where P="(\<lambda>zenon_Vevh. ((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=?z_hbt)=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=?z_hbt)&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=?z_hbt)&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])]))))))))) \\in zenon_Vevh))", OF z_Hi z_Hqh])
     show FALSE
     proof (rule zenon_in_cup [of "(CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=?z_hbt)=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=?z_hbt)&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=?z_hbt)&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))" "msgs" "{(''type'' :> (?z_hbt) @@ ''bal'' :> (b) @@ ''val'' :> (v))}", OF z_Hrc])
      assume z_Hrg:"((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=?z_hbt)=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=?z_hbt)&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=?z_hbt)&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])]))))))))) \\in msgs)" (is "?z_hrg")
      have z_Hrh: "?z_hpr((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=?z_hbt)=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=?z_hbt)&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=?z_hbt)&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])]))))))))))" (is "_=>?z_hri")
      by (rule zenon_all_0 [of "?z_hpr" "(CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=?z_hbt)=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=?z_hbt)&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=?z_hbt)&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))", OF z_Hoo])
      show FALSE
      proof (rule zenon_imply [OF z_Hrh])
       assume z_Hrj:"(~?z_hrg)"
       show FALSE
       by (rule notE [OF z_Hrj z_Hrg])
      next
       assume z_Hri:"?z_hri" (is "?z_hrk&?z_hrl")
       have z_Hrl: "?z_hrl" (is "?z_hwn&?z_hwo")
       by (rule zenon_and_1 [OF z_Hri])
       have z_Hwn: "?z_hwn" (is "_=>?z_hwp")
       by (rule zenon_and_0 [OF z_Hrl])
       show FALSE
       proof (rule zenon_imply [OF z_Hwn])
        assume z_Hwq:"(?z_hhc~=?z_hbt)"
        show FALSE
        by (rule notE [OF z_Hwq z_Hmr])
       next
        assume z_Hwp:"?z_hwp" (is "?z_hwr&?z_hws")
        have z_Hwr: "?z_hwr"
        by (rule zenon_and_0 [OF z_Hwp])
        have z_Hwt: "?z_hwm(((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=?z_hbt)=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=?z_hbt)&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=?z_hbt)&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''val'']))" (is "?z_hwv=>?z_hww")
        by (rule zenon_all_0 [of "?z_hwm" "((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=?z_hbt)=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=?z_hbt)&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=?z_hbt)&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''val''])", OF z_Hwf])
        show FALSE
        proof (rule zenon_imply [OF z_Hwt])
         assume z_Hwx:"(~?z_hwv)"
         have z_Hwy: "((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=?z_hbt)=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=?z_hbt)&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=?z_hbt)&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])]))))))))) \\in ((([''type'' : ({''1a''}), ''bal'' : (Nat)] \\cup [''type'' : ({''1b''}), ''bal'' : (Nat), ''maxVBal'' : ((Nat \\cup { -.(1)})), ''maxVal'' : ((Values \\cup {None})), ''acc'' : (Acceptors)]) \\cup [''type'' : ({?z_hbt}), ''bal'' : (Nat), ''val'' : (Values)]) \\cup [''type'' : ({''2b''}), ''bal'' : (Nat), ''val'' : (Values), ''acc'' : (Acceptors)]))" (is "?z_hwy")
         by (rule zenon_all_in_0 [of "a_msgshash_primea" "(\<lambda>x. (x \\in ((([''type'' : ({''1a''}), ''bal'' : (Nat)] \\cup [''type'' : ({''1b''}), ''bal'' : (Nat), ''maxVBal'' : ((Nat \\cup { -.(1)})), ''maxVal'' : ((Values \\cup {None})), ''acc'' : (Acceptors)]) \\cup [''type'' : ({?z_hbt}), ''bal'' : (Nat), ''val'' : (Values)]) \\cup [''type'' : ({''2b''}), ''bal'' : (Nat), ''val'' : (Values), ''acc'' : (Acceptors)])))", OF z_Hps z_Hqh])
         show FALSE
         proof (rule zenon_in_cup [of "(CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=?z_hbt)=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=?z_hbt)&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=?z_hbt)&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))" "(([''type'' : ({''1a''}), ''bal'' : (Nat)] \\cup [''type'' : ({''1b''}), ''bal'' : (Nat), ''maxVBal'' : ((Nat \\cup { -.(1)})), ''maxVal'' : ((Values \\cup {None})), ''acc'' : (Acceptors)]) \\cup [''type'' : ({?z_hbt}), ''bal'' : (Nat), ''val'' : (Values)])" "[''type'' : ({''2b''}), ''bal'' : (Nat), ''val'' : (Values), ''acc'' : (Acceptors)]", OF z_Hwy])
          assume z_Hwz:"((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=?z_hbt)=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=?z_hbt)&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=?z_hbt)&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])]))))))))) \\in (([''type'' : ({''1a''}), ''bal'' : (Nat)] \\cup [''type'' : ({''1b''}), ''bal'' : (Nat), ''maxVBal'' : ((Nat \\cup { -.(1)})), ''maxVal'' : ((Values \\cup {None})), ''acc'' : (Acceptors)]) \\cup [''type'' : ({?z_hbt}), ''bal'' : (Nat), ''val'' : (Values)]))" (is "?z_hwz")
          show FALSE
          proof (rule zenon_in_cup [of "(CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=?z_hbt)=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=?z_hbt)&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=?z_hbt)&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))" "([''type'' : ({''1a''}), ''bal'' : (Nat)] \\cup [''type'' : ({''1b''}), ''bal'' : (Nat), ''maxVBal'' : ((Nat \\cup { -.(1)})), ''maxVal'' : ((Values \\cup {None})), ''acc'' : (Acceptors)])" "[''type'' : ({?z_hbt}), ''bal'' : (Nat), ''val'' : (Values)]", OF z_Hwz])
           assume z_Hmq:"((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=?z_hbt)=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=?z_hbt)&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=?z_hbt)&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])]))))))))) \\in ([''type'' : ({''1a''}), ''bal'' : (Nat)] \\cup [''type'' : ({''1b''}), ''bal'' : (Nat), ''maxVBal'' : ((Nat \\cup { -.(1)})), ''maxVal'' : ((Values \\cup {None})), ''acc'' : (Acceptors)]))" (is "?z_hmq")
           show FALSE
           by (rule zenon_L5_ [OF z_Hmq z_Hmr])
          next
           assume z_Hxa:"((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=?z_hbt)=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=?z_hbt)&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=?z_hbt)&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])]))))))))) \\in [''type'' : ({?z_hbt}), ''bal'' : (Nat), ''val'' : (Values)])" (is "?z_hxa")
           let ?z_hhd = "(CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=?z_hbt)=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=?z_hbt)&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=?z_hbt)&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))"
           let ?z_hmg = "<<''type'', ''bal'', ''val''>>"
           let ?z_hmh = "<<{?z_hbt}, Nat, Values>>"
           have z_Hxb: "(3 \\in DOMAIN(?z_hmg))" by auto
           have z_Hxd: "((?z_hhd[(?z_hmg[3])]) \\in (?z_hmh[3]))" (is "?z_hxd")
           by (rule zenon_in_recordset_field [OF z_Hxa z_Hxb])
           have z_Hwv: "?z_hwv"
           using z_Hxd by auto
           show FALSE
           by (rule notE [OF z_Hwx z_Hwv])
          qed
         next
          assume z_Hne:"((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=?z_hbt)=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=?z_hbt)&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=?z_hbt)&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])]))))))))) \\in [''type'' : ({''2b''}), ''bal'' : (Nat), ''val'' : (Values), ''acc'' : (Acceptors)])" (is "?z_hne")
          show FALSE
          by (rule zenon_L6_ [OF z_Hne z_Hmr])
         qed
        next
         assume z_Hww:"?z_hww"
         have z_Hxh_z_Hww: "(\\A x:((x \\in Nat)=>(SafeAt(((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=?z_hbt)=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=?z_hbt)&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=?z_hbt)&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''val'']), x)=>a_hd4a7fa801d94bc2a9c69d39a405ea2a(((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=?z_hbt)=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=?z_hbt)&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=?z_hbt)&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''val'']), x)))) == ?z_hww" (is "?z_hxh == _")
         by (unfold bAll_def)
         have z_Hxh: "?z_hxh" (is "\\A x : ?z_hxn(x)")
         by (unfold z_Hxh_z_Hww, fact z_Hww)
         have z_Hxo: "?z_hxn(((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=?z_hbt)=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=?z_hbt)&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=?z_hbt)&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''bal'']))" (is "?z_hxp=>?z_hxq")
         by (rule zenon_all_0 [of "?z_hxn" "((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=?z_hbt)=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=?z_hbt)&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=?z_hbt)&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''bal''])", OF z_Hxh])
         show FALSE
         proof (rule zenon_imply [OF z_Hxo])
          assume z_Hxr:"(~?z_hxp)"
          have z_Hwy: "((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=?z_hbt)=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=?z_hbt)&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=?z_hbt)&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])]))))))))) \\in ((([''type'' : ({''1a''}), ''bal'' : (Nat)] \\cup [''type'' : ({''1b''}), ''bal'' : (Nat), ''maxVBal'' : ((Nat \\cup { -.(1)})), ''maxVal'' : ((Values \\cup {None})), ''acc'' : (Acceptors)]) \\cup [''type'' : ({?z_hbt}), ''bal'' : (Nat), ''val'' : (Values)]) \\cup [''type'' : ({''2b''}), ''bal'' : (Nat), ''val'' : (Values), ''acc'' : (Acceptors)]))" (is "?z_hwy")
          by (rule zenon_all_in_0 [of "a_msgshash_primea" "(\<lambda>x. (x \\in ((([''type'' : ({''1a''}), ''bal'' : (Nat)] \\cup [''type'' : ({''1b''}), ''bal'' : (Nat), ''maxVBal'' : ((Nat \\cup { -.(1)})), ''maxVal'' : ((Values \\cup {None})), ''acc'' : (Acceptors)]) \\cup [''type'' : ({?z_hbt}), ''bal'' : (Nat), ''val'' : (Values)]) \\cup [''type'' : ({''2b''}), ''bal'' : (Nat), ''val'' : (Values), ''acc'' : (Acceptors)])))", OF z_Hps z_Hqh])
          show FALSE
          proof (rule zenon_in_cup [of "(CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=?z_hbt)=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=?z_hbt)&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=?z_hbt)&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))" "(([''type'' : ({''1a''}), ''bal'' : (Nat)] \\cup [''type'' : ({''1b''}), ''bal'' : (Nat), ''maxVBal'' : ((Nat \\cup { -.(1)})), ''maxVal'' : ((Values \\cup {None})), ''acc'' : (Acceptors)]) \\cup [''type'' : ({?z_hbt}), ''bal'' : (Nat), ''val'' : (Values)])" "[''type'' : ({''2b''}), ''bal'' : (Nat), ''val'' : (Values), ''acc'' : (Acceptors)]", OF z_Hwy])
           assume z_Hwz:"((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=?z_hbt)=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=?z_hbt)&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=?z_hbt)&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])]))))))))) \\in (([''type'' : ({''1a''}), ''bal'' : (Nat)] \\cup [''type'' : ({''1b''}), ''bal'' : (Nat), ''maxVBal'' : ((Nat \\cup { -.(1)})), ''maxVal'' : ((Values \\cup {None})), ''acc'' : (Acceptors)]) \\cup [''type'' : ({?z_hbt}), ''bal'' : (Nat), ''val'' : (Values)]))" (is "?z_hwz")
           show FALSE
           proof (rule zenon_in_cup [of "(CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=?z_hbt)=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=?z_hbt)&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=?z_hbt)&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))" "([''type'' : ({''1a''}), ''bal'' : (Nat)] \\cup [''type'' : ({''1b''}), ''bal'' : (Nat), ''maxVBal'' : ((Nat \\cup { -.(1)})), ''maxVal'' : ((Values \\cup {None})), ''acc'' : (Acceptors)])" "[''type'' : ({?z_hbt}), ''bal'' : (Nat), ''val'' : (Values)]", OF z_Hwz])
            assume z_Hmq:"((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=?z_hbt)=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=?z_hbt)&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=?z_hbt)&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])]))))))))) \\in ([''type'' : ({''1a''}), ''bal'' : (Nat)] \\cup [''type'' : ({''1b''}), ''bal'' : (Nat), ''maxVBal'' : ((Nat \\cup { -.(1)})), ''maxVal'' : ((Values \\cup {None})), ''acc'' : (Acceptors)]))" (is "?z_hmq")
            show FALSE
            by (rule zenon_L5_ [OF z_Hmq z_Hmr])
           next
            assume z_Hxa:"((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=?z_hbt)=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=?z_hbt)&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=?z_hbt)&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])]))))))))) \\in [''type'' : ({?z_hbt}), ''bal'' : (Nat), ''val'' : (Values)])" (is "?z_hxa")
            let ?z_hhd = "(CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=?z_hbt)=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=?z_hbt)&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=?z_hbt)&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))"
            let ?z_hmg = "<<''type'', ''bal'', ''val''>>"
            let ?z_hmh = "<<{?z_hbt}, Nat, Values>>"
            have z_Hxs: "(2 \\in DOMAIN(?z_hmg))" by auto
            have z_Hxu: "((?z_hhd[(?z_hmg[2])]) \\in (?z_hmh[2]))" (is "?z_hxu")
            by (rule zenon_in_recordset_field [OF z_Hxa z_Hxs])
            have z_Hxp: "?z_hxp"
            using z_Hxu by auto
            show FALSE
            by (rule notE [OF z_Hxr z_Hxp])
           qed
          next
           assume z_Hne:"((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=?z_hbt)=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=?z_hbt)&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=?z_hbt)&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])]))))))))) \\in [''type'' : ({''2b''}), ''bal'' : (Nat), ''val'' : (Values), ''acc'' : (Acceptors)])" (is "?z_hne")
           show FALSE
           by (rule zenon_L6_ [OF z_Hne z_Hmr])
          qed
         next
          assume z_Hxq:"?z_hxq"
          show FALSE
          proof (rule zenon_imply [OF z_Hxq])
           assume z_Hxy:"(~?z_hwr)"
           show FALSE
           by (rule notE [OF z_Hxy z_Hwr])
          next
           assume z_Hvd:"?z_hvd"
           show FALSE
           by (rule notE [OF z_Hvf z_Hvd])
          qed
         qed
        qed
       qed
      qed
     next
      assume z_Hkk:"((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=?z_hbt)=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=?z_hbt)&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=?z_hbt)&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])]))))))))) \\in {(''type'' :> (?z_hbt) @@ ''bal'' :> (b) @@ ''val'' :> (v))})" (is "?z_hkk")
      show FALSE
      proof (rule zenon_in_addElt [of "(CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=?z_hbt)=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=?z_hbt)&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=?z_hbt)&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))" "(''type'' :> (?z_hbt) @@ ''bal'' :> (b) @@ ''val'' :> (v))" "{}", OF z_Hkk])
       assume z_Hji:"((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=?z_hbt)=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=?z_hbt)&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=?z_hbt)&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))=(''type'' :> (?z_hbt) @@ ''bal'' :> (b) @@ ''val'' :> (v)))" (is "?z_hhd=?z_hfo")
       show FALSE
       proof (rule notE [OF z_Hvf])
        have z_Hxz: "((?z_hfo[''val''])=(?z_hhd[''val'']))" (is "?z_hfw=?z_hwu")
        proof (rule zenon_nnpp [of "(?z_hfw=?z_hwu)"])
         assume z_Hya:"(?z_hfw~=?z_hwu)"
         show FALSE
         proof (rule zenon_noteq [of "?z_hwu"])
          have z_Hjj: "(?z_hfo=?z_hhd)"
          by (rule sym [OF z_Hji])
          have z_Hyb: "(?z_hwu~=?z_hwu)"
          by (rule subst [where P="(\<lambda>zenon_Viwh. ((zenon_Viwh[''val''])~=?z_hwu))", OF z_Hjj], fact z_Hya)
          thus "(?z_hwu~=?z_hwu)" .
         qed
        qed
        have z_Hyg: "((?z_hfo[''bal''])=(?z_hhd[''bal'']))" (is "?z_hfx=?z_hqu")
        proof (rule zenon_nnpp [of "(?z_hfx=?z_hqu)"])
         assume z_Hyh:"(?z_hfx~=?z_hqu)"
         show FALSE
         proof (rule zenon_noteq [of "?z_hqu"])
          have z_Hjj: "(?z_hfo=?z_hhd)"
          by (rule sym [OF z_Hji])
          have z_Hyi: "(?z_hqu~=?z_hqu)"
          by (rule subst [where P="(\<lambda>zenon_Vjwh. ((zenon_Vjwh[''bal''])~=?z_hqu))", OF z_Hjj], fact z_Hyh)
          thus "(?z_hqu~=?z_hqu)" .
         qed
        qed
        have z_Hyn: "a_hd4a7fa801d94bc2a9c69d39a405ea2a(?z_hwu, ?z_hfx)" (is "?z_hyn")
        by (rule subst [where P="(\<lambda>zenon_Vh. a_hd4a7fa801d94bc2a9c69d39a405ea2a(zenon_Vh, ?z_hfx))", OF z_Hxz], fact z_Hl)
        have z_Hvd: "?z_hvd"
        by (rule subst [where P="(\<lambda>zenon_Vlwh. a_hd4a7fa801d94bc2a9c69d39a405ea2a(?z_hwu, zenon_Vlwh))", OF z_Hyg], fact z_Hyn)
        thus "?z_hvd" .
       qed
      next
       assume z_Hmp:"((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=?z_hbt)=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=?z_hbt)&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=?z_hbt)&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])]))))))))) \\in {})" (is "?z_hmp")
       show FALSE
       by (rule zenon_in_emptyset [of "(CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=?z_hbt)=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=?z_hbt)&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=?z_hbt)&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))", OF z_Hmp])
      qed
     qed
    qed
   next
    assume z_Hyu:"(~?z_hve)"
    have z_Hyv: "(~bAll(?z_hfm, (\<lambda>ma. ((((ma[''type''])=?z_hbt)&((ma[''bal''])=((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=?z_hbt)=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=?z_hbt)&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=?z_hbt)&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''bal''])))=>(ma=(CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=?z_hbt)=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=?z_hbt)&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=?z_hbt)&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])]))))))))))))))" (is "~?z_hyw")
    by (rule subst [where P="(\<lambda>zenon_Vuvh. (~bAll(zenon_Vuvh, (\<lambda>ma. ((((ma[''type''])=?z_hbt)&((ma[''bal''])=((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=?z_hbt)=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=?z_hbt)&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=?z_hbt)&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''bal''])))=>(ma=(CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=?z_hbt)=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=?z_hbt)&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=?z_hbt)&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))))))))", OF z_Hi z_Hyu])
    have z_Hzg_z_Hyv: "(~(\\A x:((x \\in ?z_hfm)=>((((x[''type''])=?z_hbt)&((x[''bal''])=((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=?z_hbt)=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=?z_hbt)&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=?z_hbt)&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''bal''])))=>(x=(CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=?z_hbt)=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=?z_hbt)&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=?z_hbt)&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))))))) == (~?z_hyw)" (is "?z_hzg == ?z_hyv")
    by (unfold bAll_def)
    have z_Hzg: "?z_hzg" (is "~(\\A x : ?z_hzo(x))")
    by (unfold z_Hzg_z_Hyv, fact z_Hyv)
    have z_Hzp: "(\\E x:(~((x \\in ?z_hfm)=>((((x[''type''])=?z_hbt)&((x[''bal''])=((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=?z_hbt)=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=?z_hbt)&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=?z_hbt)&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''bal''])))=>(x=(CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=?z_hbt)=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=?z_hbt)&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=?z_hbt)&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])]))))))))))))))" (is "\\E x : ?z_hzr(x)")
    by (rule zenon_notallex_0 [of "?z_hzo", OF z_Hzg])
    have z_Hzs: "?z_hzr((CHOOSE x:(~((x \\in ?z_hfm)=>((((x[''type''])=?z_hbt)&((x[''bal''])=((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=?z_hbt)=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=?z_hbt)&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=?z_hbt)&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''bal''])))=>(x=(CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=?z_hbt)=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=?z_hbt)&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=?z_hbt)&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))))))))" (is "~(?z_hzu=>?z_hzv)")
    by (rule zenon_ex_choose_0 [of "?z_hzr", OF z_Hzp])
    have z_Hzu: "?z_hzu"
    by (rule zenon_notimply_0 [OF z_Hzs])
    have z_Hzw: "(~?z_hzv)" (is "~(?z_hzx=>?z_hzy)")
    by (rule zenon_notimply_1 [OF z_Hzs])
    have z_Hzx: "?z_hzx" (is "?z_hzz&?z_hbaa")
    by (rule zenon_notimply_0 [OF z_Hzw])
    have z_Hbab: "((CHOOSE x:(~((x \\in ?z_hfm)=>((((x[''type''])=?z_hbt)&((x[''bal''])=((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=?z_hbt)=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=?z_hbt)&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=?z_hbt)&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''bal''])))=>(x=(CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=?z_hbt)=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=?z_hbt)&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=?z_hbt)&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])]))))))))))))))~=(CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=?z_hbt)=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=?z_hbt)&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=''2b'')=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=?z_hbt)&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])]))))))))))" (is "?z_hzt~=?z_hhd")
    by (rule zenon_notimply_1 [OF z_Hzw])
    have z_Hzz: "?z_hzz" (is "?z_hbac=_")
    by (rule zenon_and_0 [OF z_Hzx])
    have z_Hbaa: "?z_hbaa" (is "?z_hbad=?z_hqu")
    by (rule zenon_and_1 [OF z_Hzx])
    have z_Hbae: "?z_hqa(?z_hzt)" (is "?z_hbaf=>?z_hbag")
    by (rule zenon_all_0 [of "?z_hqa" "?z_hzt", OF z_Hpt])
    show FALSE
    proof (rule zenon_imply [OF z_Hbae])
     assume z_Hbah:"(~?z_hbaf)"
     have z_Hbai: "(~?z_hzu)"
     by (rule subst [where P="(\<lambda>zenon_Vwvh. (~(?z_hzt \\in zenon_Vwvh)))", OF z_Hi z_Hbah])
     show FALSE
     by (rule notE [OF z_Hbai z_Hzu])
    next
     assume z_Hbag:"?z_hbag"
     have z_Hban_z_Hbag: "(\\A x:((x \\in a_msgshash_primea)=>(((?z_hzz&((x[''type''])=?z_hbt))&((x[''bal''])=?z_hbad))=>(x=?z_hzt)))) == ?z_hbag" (is "?z_hban == _")
     by (unfold bAll_def)
     have z_Hban: "?z_hban" (is "\\A x : ?z_hbau(x)")
     by (unfold z_Hban_z_Hbag, fact z_Hbag)
     have z_Hbav: "?z_hbau(?z_hhd)" (is "_=>?z_hbaw")
     by (rule zenon_all_0 [of "?z_hbau" "?z_hhd", OF z_Hban])
     show FALSE
     proof (rule zenon_imply [OF z_Hbav])
      assume z_Hbax:"(~?z_hqh)"
      show FALSE
      by (rule notE [OF z_Hbax z_Hqh])
     next
      assume z_Hbaw:"?z_hbaw" (is "?z_hbay=>?z_hbaz")
      show FALSE
      proof (rule zenon_imply [OF z_Hbaw])
       assume z_Hbba:"(~?z_hbay)" (is "~(?z_hbbb&?z_hbbc)")
       show FALSE
       proof (rule zenon_notand [OF z_Hbba])
        assume z_Hbbd:"(~?z_hbbb)"
        show FALSE
        proof (rule zenon_notand [OF z_Hbbd])
         assume z_Hbbe:"(?z_hbac~=?z_hbt)"
         show FALSE
         by (rule notE [OF z_Hbbe z_Hzz])
        next
         assume z_Hwq:"(?z_hhc~=?z_hbt)"
         show FALSE
         by (rule notE [OF z_Hwq z_Hmr])
        qed
       next
        assume z_Hbbf:"(?z_hqu~=?z_hbad)"
        show FALSE
        by (rule zenon_eqsym [OF z_Hbaa z_Hbbf])
       qed
      next
       assume z_Hbaz:"?z_hbaz"
       show FALSE
       by (rule zenon_eqsym [OF z_Hbaz z_Hbab])
      qed
     qed
    qed
   qed
  next
   assume z_Hbbg:"(~?z_huz)" (is "~(?z_hni=>?z_hbbh)")
   have z_Hni: "?z_hni" (is "?z_hhc=?z_hbx")
   by (rule zenon_notimply_0 [OF z_Hbbg])
   have z_Hbbi: "(~?z_hbbh)" (is "~(?z_hbbj&?z_hbbk)")
   by (rule zenon_notimply_1 [OF z_Hbbg])
   show FALSE
   proof (rule zenon_notand [OF z_Hbbi])
    assume z_Hbbl:"(~?z_hbbj)"
    have z_Hbbm: "(~bEx(?z_hfm, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=?z_hbx)=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''bal'']))&((ma[''val''])=((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=?z_hbx)=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''val''])))))))" (is "~?z_hbbn")
    by (rule subst [where P="(\<lambda>zenon_Vyvh. (~bEx(zenon_Vyvh, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=?z_hbx)=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''bal'']))&((ma[''val''])=((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=?z_hbx)=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''val'']))))))))", OF z_Hi z_Hbbl])
    have z_Hbbw_z_Hbbm: "(~(\\E x:((x \\in ?z_hfm)&(((x[''type''])=''2a'')&(((x[''bal''])=((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=?z_hbx)=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''bal'']))&((x[''val''])=((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=?z_hbx)=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''val'']))))))) == (~?z_hbbn)" (is "?z_hbbw == ?z_hbbm")
    by (unfold bEx_def)
    have z_Hbbw: "?z_hbbw" (is "~(\\E x : ?z_hbcc(x))")
    by (unfold z_Hbbw_z_Hbbm, fact z_Hbbm)
    have z_Hrc: "((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=?z_hbx)=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])]))))))))) \\in ?z_hfm)" (is "?z_hrc")
    by (rule subst [where P="(\<lambda>zenon_Vevh. ((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=?z_hbx)=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])]))))))))) \\in zenon_Vevh))", OF z_Hi z_Hqh])
    show FALSE
    proof (rule zenon_in_cup [of "(CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=?z_hbx)=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))" "msgs" "{(''type'' :> (''2a'') @@ ''bal'' :> (b) @@ ''val'' :> (v))}", OF z_Hrc])
     assume z_Hrg:"((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=?z_hbx)=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])]))))))))) \\in msgs)" (is "?z_hrg")
     have z_Hrh: "?z_hpr((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=?z_hbx)=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])]))))))))))" (is "_=>?z_hri")
     by (rule zenon_all_0 [of "?z_hpr" "(CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=?z_hbx)=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))", OF z_Hoo])
     show FALSE
     proof (rule zenon_imply [OF z_Hrh])
      assume z_Hrj:"(~?z_hrg)"
      show FALSE
      by (rule notE [OF z_Hrj z_Hrg])
     next
      assume z_Hri:"?z_hri" (is "?z_hrk&?z_hrl")
      have z_Hrl: "?z_hrl" (is "?z_hwn&?z_hwo")
      by (rule zenon_and_1 [OF z_Hri])
      have z_Hwo: "?z_hwo" (is "_=>?z_hbcd")
      by (rule zenon_and_1 [OF z_Hrl])
      show FALSE
      proof (rule zenon_imply [OF z_Hwo])
       assume z_Hbce:"(?z_hhc~=?z_hbx)"
       show FALSE
       by (rule notE [OF z_Hbce z_Hni])
      next
       assume z_Hbcd:"?z_hbcd" (is "?z_hbcf&?z_hbcg")
       have z_Hbcf: "?z_hbcf"
       by (rule zenon_and_0 [OF z_Hbcd])
       have z_Hbch_z_Hbcf: "(\\E x:((x \\in msgs)&(((x[''type''])=''2a'')&(((x[''bal''])=((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=?z_hbx)=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''bal'']))&((x[''val''])=((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=?z_hbx)=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''val''])))))) == ?z_hbcf" (is "?z_hbch == _")
       by (unfold bEx_def)
       have z_Hbch: "?z_hbch" (is "\\E x : ?z_hbcj(x)")
       by (unfold z_Hbch_z_Hbcf, fact z_Hbcf)
       have z_Hbck: "?z_hbcj((CHOOSE x:((x \\in msgs)&(((x[''type''])=''2a'')&(((x[''bal''])=((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=?z_hbx)=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''bal'']))&((x[''val''])=((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=?z_hbx)=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''val''])))))))" (is "?z_hbcm&?z_hbcn")
       by (rule zenon_ex_choose_0 [of "?z_hbcj", OF z_Hbch])
       have z_Hbcm: "?z_hbcm"
       by (rule zenon_and_0 [OF z_Hbck])
       have z_Hbcn: "?z_hbcn" (is "?z_hbco&?z_hbcp")
       by (rule zenon_and_1 [OF z_Hbck])
       have z_Hbco: "?z_hbco" (is "?z_hbcq=?z_hbt")
       by (rule zenon_and_0 [OF z_Hbcn])
       have z_Hbcp: "?z_hbcp" (is "?z_hbcr&?z_hbcs")
       by (rule zenon_and_1 [OF z_Hbcn])
       have z_Hbcr: "?z_hbcr" (is "?z_hbct=?z_hqu")
       by (rule zenon_and_0 [OF z_Hbcp])
       have z_Hbcs: "?z_hbcs" (is "?z_hbcu=?z_hwu")
       by (rule zenon_and_1 [OF z_Hbcp])
       have z_Hbcv: "~?z_hbcc((CHOOSE x:((x \\in msgs)&(((x[''type''])=?z_hbt)&(((x[''bal''])=?z_hqu)&((x[''val''])=?z_hwu))))))" (is "~(?z_hbcw&_)")
       by (rule zenon_notex_0 [of "?z_hbcc" "(CHOOSE x:((x \\in msgs)&(((x[''type''])=?z_hbt)&(((x[''bal''])=?z_hqu)&((x[''val''])=?z_hwu)))))", OF z_Hbbw])
       show FALSE
       proof (rule zenon_notand [OF z_Hbcv])
        assume z_Hbcx:"(~?z_hbcw)"
        have z_Hbcy: "(~?z_hbcm)"
        by (rule zenon_notin_cup_0 [of "(CHOOSE x:((x \\in msgs)&(((x[''type''])=?z_hbt)&(((x[''bal''])=?z_hqu)&((x[''val''])=?z_hwu)))))" "msgs" "{(''type'' :> (?z_hbt) @@ ''bal'' :> (b) @@ ''val'' :> (v))}", OF z_Hbcx])
        show FALSE
        by (rule notE [OF z_Hbcy z_Hbcm])
       next
        assume z_Hbcz:"(~?z_hbcn)"
        show FALSE
        proof (rule zenon_notand [OF z_Hbcz])
         assume z_Hbda:"(?z_hbcq~=?z_hbt)"
         show FALSE
         by (rule notE [OF z_Hbda z_Hbco])
        next
         assume z_Hbdb:"(~?z_hbcp)"
         show FALSE
         proof (rule zenon_notand [OF z_Hbdb])
          assume z_Hbdc:"(?z_hbct~=?z_hqu)"
          show FALSE
          by (rule notE [OF z_Hbdc z_Hbcr])
         next
          assume z_Hbdd:"(?z_hbcu~=?z_hwu)"
          show FALSE
          by (rule notE [OF z_Hbdd z_Hbcs])
         qed
        qed
       qed
      qed
     qed
    next
     assume z_Hkk:"((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=?z_hbx)=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])]))))))))) \\in {(''type'' :> (''2a'') @@ ''bal'' :> (b) @@ ''val'' :> (v))})" (is "?z_hkk")
     show FALSE
     by (rule zenon_L7_ [OF z_Hi z_Hkk z_Hni z_Hkm])
    qed
   next
    assume z_Hbde:"(~?z_hbbk)"
    have z_Hbdf: "(~(((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=?z_hbx)=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''bal'']) <= (maxVBal[((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=?z_hbx)=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''acc''])])))" (is "~?z_hbcg")
    by (rule subst [where P="(\<lambda>zenon_Vcvh. (~(((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=?z_hbx)=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''bal'']) <= (zenon_Vcvh[((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=?z_hbx)=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))[''acc''])]))))", OF z_Hg z_Hbde])
    have z_Hrc: "((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=?z_hbx)=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])]))))))))) \\in ?z_hfm)" (is "?z_hrc")
    by (rule subst [where P="(\<lambda>zenon_Vevh. ((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=?z_hbx)=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])]))))))))) \\in zenon_Vevh))", OF z_Hi z_Hqh])
    show FALSE
    proof (rule zenon_in_cup [of "(CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=?z_hbx)=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))" "msgs" "{(''type'' :> (''2a'') @@ ''bal'' :> (b) @@ ''val'' :> (v))}", OF z_Hrc])
     assume z_Hrg:"((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=?z_hbx)=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])]))))))))) \\in msgs)" (is "?z_hrg")
     have z_Hrh: "?z_hpr((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=?z_hbx)=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])]))))))))))" (is "_=>?z_hri")
     by (rule zenon_all_0 [of "?z_hpr" "(CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=?z_hbx)=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])])))))))))", OF z_Hoo])
     show FALSE
     proof (rule zenon_imply [OF z_Hrh])
      assume z_Hrj:"(~?z_hrg)"
      show FALSE
      by (rule notE [OF z_Hrj z_Hrg])
     next
      assume z_Hri:"?z_hri" (is "?z_hrk&?z_hrl")
      have z_Hrl: "?z_hrl" (is "?z_hwn&?z_hwo")
      by (rule zenon_and_1 [OF z_Hri])
      have z_Hwo: "?z_hwo" (is "_=>?z_hbcd")
      by (rule zenon_and_1 [OF z_Hrl])
      show FALSE
      proof (rule zenon_imply [OF z_Hwo])
       assume z_Hbce:"(?z_hhc~=?z_hbx)"
       show FALSE
       by (rule notE [OF z_Hbce z_Hni])
      next
       assume z_Hbcd:"?z_hbcd" (is "?z_hbcf&_")
       have z_Hbcg: "?z_hbcg"
       by (rule zenon_and_1 [OF z_Hbcd])
       show FALSE
       by (rule notE [OF z_Hbdf z_Hbcg])
      qed
     qed
    next
     assume z_Hkk:"((CHOOSE x:(~((x \\in a_msgshash_primea)=>((((x[''type''])=''1b'')=>(((x[''bal'']) <= (a_maxBalhash_primea[(x[''acc''])]))&(((((x[''maxVal'']) \\in Values)&(((x[''maxVBal'']) \\in Nat)&a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), (x[''maxVal'']), (x[''maxVBal'']))))|(((x[''maxVal''])=None)&((x[''maxVBal''])= -.(1))))&bAll(isa'dotdot(((x[''maxVBal'']) + 1), ((x[''bal'']) +  -.(1))), (\<lambda>a_ca. (~bEx(Values, (\<lambda>v_1. a_h03062837f0f10c4714e0f53023b1a7a((x[''acc'']), v_1, a_ca)))))))))&((((x[''type''])=''2a'')=>(a_hd4a7fa801d94bc2a9c69d39a405ea2a((x[''val'']), (x[''bal'']))&bAll(a_msgshash_primea, (\<lambda>ma. ((((ma[''type''])=''2a'')&((ma[''bal''])=(x[''bal''])))=>(ma=x))))))&(((x[''type''])=?z_hbx)=>(bEx(a_msgshash_primea, (\<lambda>ma. (((ma[''type''])=''2a'')&(((ma[''bal''])=(x[''bal'']))&((ma[''val''])=(x[''val'']))))))&((x[''bal'']) <= (a_maxVBalhash_primea[(x[''acc''])]))))))))) \\in {(''type'' :> (''2a'') @@ ''bal'' :> (b) @@ ''val'' :> (v))})" (is "?z_hkk")
     show FALSE
     by (rule zenon_L7_ [OF z_Hi z_Hkk z_Hni z_Hkm])
    qed
   qed
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 146"; *} qed
lemma ob'109:
fixes Acceptors
fixes Values
fixes Quorums
fixes msgs msgs'
fixes maxBal maxBal'
fixes maxVBal maxVBal'
fixes maxVal maxVal'
(* usable definition vars suppressed *)
(* usable definition None suppressed *)
(* usable definition Init suppressed *)
(* usable definition Phase1a suppressed *)
(* usable definition Phase1b suppressed *)
(* usable definition Phase2a suppressed *)
(* usable definition Phase2b suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition ChosenIn suppressed *)
(* usable definition Chosen suppressed *)
(* usable definition Consistency suppressed *)
(* usable definition WontVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition MsgInv suppressed *)
(* usable definition AccInv suppressed *)
assumes v'34: "((((((((msgs) \<in> ((SUBSET ((((((([''type'' : ({(''1a'')}), ''bal'' : (Nat)]) \<union> ([''type'' : ({(''1b'')}), ''bal'' : (Nat), ''maxVBal'' : (((Nat) \<union> ({((minus (((Succ[0])))))}))), ''maxVal'' : (((Values) \<union> ({(None)}))), ''acc'' : (Acceptors)]))) \<union> ([''type'' : ({(''2a'')}), ''bal'' : (Nat), ''val'' : (Values)]))) \<union> ([''type'' : ({(''2b'')}), ''bal'' : (Nat), ''val'' : (Values), ''acc'' : (Acceptors)]))))))) & (((maxVBal) \<in> ([(Acceptors) \<rightarrow> (((Nat) \<union> ({((minus (((Succ[0])))))})))]))) & (((maxBal) \<in> ([(Acceptors) \<rightarrow> (((Nat) \<union> ({((minus (((Succ[0])))))})))]))) & (((maxVal) \<in> ([(Acceptors) \<rightarrow> (((Values) \<union> ({(None)})))]))) & (\<forall> a \<in> (Acceptors) : ((geq ((fapply ((maxBal), (a))), (fapply ((maxVBal), (a)))))))) \<and> (MsgInv))) \<and> (AccInv)))"
assumes v'35: "(Next)"
fixes a
assumes a_in : "(a \<in> (Acceptors))"
fixes m
assumes m_in : "(m \<in> (msgs))"
assumes v'56: "((geq ((fapply ((m), (''bal''))), (fapply ((maxBal), (a))))))"
assumes v'57: "(((fapply ((m), (''type''))) = (''2a'')))"
assumes v'58: "((((a_msgshash_primea :: c)) = (((msgs) \<union> ({(((''type'' :> (''2b'')) @@ (''bal'' :> (fapply ((m), (''bal'')))) @@ (''val'' :> (fapply ((m), (''val'')))) @@ (''acc'' :> (a))))})))))"
assumes v'59: "((((a_maxVBalhash_primea :: c)) = ([(maxVBal) EXCEPT ![(a)] = (fapply ((m), (''bal'')))])))"
assumes v'60: "((((a_maxBalhash_primea :: c)) = ([(maxBal) EXCEPT ![(a)] = (fapply ((m), (''bal'')))])))"
assumes v'61: "((((a_maxValhash_primea :: c)) = ([(maxVal) EXCEPT ![(a)] = (fapply ((m), (''val'')))])))"
shows "(\<forall>aa : (\<forall>vv : (\<forall>bb : (((\<exists> m_1 \<in> ((a_msgshash_primea :: c)) : ((((fapply ((m_1), (''type''))) = (''2b''))) & (((fapply ((m_1), (''val''))) = (vv))) & (((fapply ((m_1), (''bal''))) = (bb))) & (((fapply ((m_1), (''acc''))) = (aa))))) \<Leftrightarrow> (((\<exists> m_1 \<in> (msgs) : ((((fapply ((m_1), (''type''))) = (''2b''))) & (((fapply ((m_1), (''val''))) = (vv))) & (((fapply ((m_1), (''bal''))) = (bb))) & (((fapply ((m_1), (''acc''))) = (aa))))) \<or> (((((((aa) = (a))) \<and> (((vv) = (fapply (((a_maxValhash_primea :: c)), (a))))))) \<and> (((bb) = (fapply (((a_maxVBalhash_primea :: c)), (a))))))))))))))"(is "PROP ?ob'109")
proof -
ML_command {* writeln "*** TLAPS ENTER 109"; *}
show "PROP ?ob'109"
using assms by auto
ML_command {* writeln "*** TLAPS EXIT 109"; *} qed
lemma ob'259:
fixes Acceptors
fixes Values
fixes Quorums
(* usable definition Ballots suppressed *)
fixes msgs msgs'
fixes maxBal maxBal'
fixes maxVBal maxVBal'
fixes maxVal maxVal'
(* usable definition vars suppressed *)
(* usable definition Send suppressed *)
(* usable definition None suppressed *)
(* usable definition Phase1a suppressed *)
(* usable definition Phase1b suppressed *)
(* usable definition Phase2a suppressed *)
(* usable definition Phase2b suppressed *)
(* usable definition Next suppressed *)
(* usable definition Spec suppressed *)
(* usable definition Consistency suppressed *)
(* usable definition Messages suppressed *)
(* usable definition TypeOK suppressed *)
(* usable definition WontVoteIn suppressed *)
(* usable definition SafeAt suppressed *)
(* usable definition MsgInv suppressed *)
(* usable definition AccInv suppressed *)
(* usable definition Inv suppressed *)
(* usable definition C!Next suppressed *)
(* usable definition C!Spec suppressed *)
assumes v'39: "(\<forall> b \<in> (Ballots) : (\<forall> Q \<in> ((Quorums ((b)))) : (((Q) \<noteq> ({})))))"
shows "((((((msgs) = ({}))) & (((maxVBal) = ([ a \<in> (Acceptors)  \<mapsto> ((minus (((Succ[0])))))]))) & (((maxBal) = ([ a \<in> (Acceptors)  \<mapsto> ((minus (((Succ[0])))))]))) & (((maxVal) = ([ a \<in> (Acceptors)  \<mapsto> (None)])))) \<Rightarrow> (((subsetOf((Values), %v. (\<exists> b \<in> (Ballots) : (\<exists> Q \<in> ((Quorums ((b)))) : (\<forall> a \<in> (Q) : (\<exists> m \<in> (msgs) : ((((fapply ((m), (''type''))) = (''2b''))) & (((fapply ((m), (''val''))) = (v))) & (((fapply ((m), (''bal''))) = (b))) & (((fapply ((m), (''acc''))) = (a)))))))))) = ({})))))"(is "PROP ?ob'259")
proof -
ML_command {* writeln "*** TLAPS ENTER 259"; *}
show "PROP ?ob'259"

(* BEGIN ZENON INPUT
;; file=FastPaxos.tlaps/tlapm_88c312.znn; PATH='/home/alexis51151/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin:/home/alexis51151/.local/bin:/home/alexis51151/Ecole/EPaxos/toolbox:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >FastPaxos.tlaps/tlapm_88c312.znn.out
;; obligation #259
$hyp "v'39" (TLA.bAll Ballots ((b) (TLA.bAll (Quorums b) ((Q) (-. (= Q
TLA.emptyset))))))
$goal (=> (/\ (= msgs TLA.emptyset) (= maxVBal
(TLA.Fcn Acceptors ((a) (arith.minus (TLA.fapply TLA.Succ 0))))) (= maxBal
(TLA.Fcn Acceptors ((a) (arith.minus (TLA.fapply TLA.Succ 0))))) (= maxVal
(TLA.Fcn Acceptors ((a) None))))
(= (TLA.subsetOf Values ((v) (TLA.bEx Ballots ((b) (TLA.bEx (Quorums b) ((Q) (TLA.bAll Q ((a) (TLA.bEx msgs ((m) (/\ (= (TLA.fapply m "type")
"2b") (= (TLA.fapply m "val") v) (= (TLA.fapply m "bal") b)
(= (TLA.fapply m "acc") a))))))))))))
TLA.emptyset))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Ha:"bAll(Ballots, (\<lambda>b. bAll(Quorums(b), (\<lambda>Q. (Q~={})))))" (is "?z_ha")
 using v'39 by blast
 have zenon_L1_: "((CHOOSE x:((x \\in Quorums((CHOOSE x:((x \\in Ballots)&bEx(Quorums(x), (\<lambda>Q. bAll(Q, (\<lambda>a. bEx(msgs, (\<lambda>m. (((m[''type''])=''2b'')&(((m[''val''])=(CHOOSE zenon_Vj:(~((zenon_Vj \\in subsetOf(Values, (\<lambda>v. bEx(Ballots, (\<lambda>b. bEx(Quorums(b), (\<lambda>Q. bAll(Q, (\<lambda>a. bEx(msgs, (\<lambda>m. (((m[''type''])=''2b'')&(((m[''val''])=v)&(((m[''bal''])=b)&((m[''acc''])=a)))))))))))))))<=>(zenon_Vj \\in {})))))&(((m[''bal''])=x)&((m[''acc''])=a))))))))))))))&bAll(x, (\<lambda>a. bEx(msgs, (\<lambda>m. (((m[''type''])=''2b'')&(((m[''val''])=(CHOOSE zenon_Vj:(~((zenon_Vj \\in subsetOf(Values, (\<lambda>v. bEx(Ballots, (\<lambda>b. bEx(Quorums(b), (\<lambda>Q. bAll(Q, (\<lambda>a. bEx(msgs, (\<lambda>m. (((m[''type''])=''2b'')&(((m[''val''])=v)&(((m[''bal''])=b)&((m[''acc''])=a)))))))))))))))<=>(zenon_Vj \\in {})))))&(((m[''bal''])=(CHOOSE x:((x \\in Ballots)&bEx(Quorums(x), (\<lambda>Q. bAll(Q, (\<lambda>a. bEx(msgs, (\<lambda>m. (((m[''type''])=''2b'')&(((m[''val''])=(CHOOSE zenon_Vj:(~((zenon_Vj \\in subsetOf(Values, (\<lambda>v. bEx(Ballots, (\<lambda>b. bEx(Quorums(b), (\<lambda>Q. bAll(Q, (\<lambda>a. bEx(msgs, (\<lambda>m. (((m[''type''])=''2b'')&(((m[''val''])=v)&(((m[''bal''])=b)&((m[''acc''])=a)))))))))))))))<=>(zenon_Vj \\in {})))))&(((m[''bal''])=x)&((m[''acc''])=a)))))))))))))&((m[''acc''])=a))))))))))~={}) ==> (msgs={}) ==> (\\A x:((x \\in (CHOOSE x:((x \\in Quorums((CHOOSE x:((x \\in Ballots)&bEx(Quorums(x), (\<lambda>Q. bAll(Q, (\<lambda>a. bEx(msgs, (\<lambda>m. (((m[''type''])=''2b'')&(((m[''val''])=(CHOOSE zenon_Vj:(~((zenon_Vj \\in subsetOf(Values, (\<lambda>v. bEx(Ballots, (\<lambda>b. bEx(Quorums(b), (\<lambda>Q. bAll(Q, (\<lambda>a. bEx(msgs, (\<lambda>m. (((m[''type''])=''2b'')&(((m[''val''])=v)&(((m[''bal''])=b)&((m[''acc''])=a)))))))))))))))<=>(zenon_Vj \\in {})))))&(((m[''bal''])=x)&((m[''acc''])=a))))))))))))))&bAll(x, (\<lambda>a. bEx(msgs, (\<lambda>m. (((m[''type''])=''2b'')&(((m[''val''])=(CHOOSE zenon_Vj:(~((zenon_Vj \\in subsetOf(Values, (\<lambda>v. bEx(Ballots, (\<lambda>b. bEx(Quorums(b), (\<lambda>Q. bAll(Q, (\<lambda>a. bEx(msgs, (\<lambda>m. (((m[''type''])=''2b'')&(((m[''val''])=v)&(((m[''bal''])=b)&((m[''acc''])=a)))))))))))))))<=>(zenon_Vj \\in {})))))&(((m[''bal''])=(CHOOSE x:((x \\in Ballots)&bEx(Quorums(x), (\<lambda>Q. bAll(Q, (\<lambda>a. bEx(msgs, (\<lambda>m. (((m[''type''])=''2b'')&(((m[''val''])=(CHOOSE zenon_Vj:(~((zenon_Vj \\in subsetOf(Values, (\<lambda>v. bEx(Ballots, (\<lambda>b. bEx(Quorums(b), (\<lambda>Q. bAll(Q, (\<lambda>a. bEx(msgs, (\<lambda>m. (((m[''type''])=''2b'')&(((m[''val''])=v)&(((m[''bal''])=b)&((m[''acc''])=a)))))))))))))))<=>(zenon_Vj \\in {})))))&(((m[''bal''])=x)&((m[''acc''])=a)))))))))))))&((m[''acc''])=a)))))))))))=>bEx(msgs, (\<lambda>m. (((m[''type''])=''2b'')&(((m[''val''])=(CHOOSE zenon_Vj:(~((zenon_Vj \\in subsetOf(Values, (\<lambda>v. bEx(Ballots, (\<lambda>b. bEx(Quorums(b), (\<lambda>Q. bAll(Q, (\<lambda>a. bEx(msgs, (\<lambda>m. (((m[''type''])=''2b'')&(((m[''val''])=v)&(((m[''bal''])=b)&((m[''acc''])=a)))))))))))))))<=>(zenon_Vj \\in {})))))&(((m[''bal''])=(CHOOSE x:((x \\in Ballots)&bEx(Quorums(x), (\<lambda>Q. bAll(Q, (\<lambda>a. bEx(msgs, (\<lambda>m. (((m[''type''])=''2b'')&(((m[''val''])=(CHOOSE zenon_Vj:(~((zenon_Vj \\in subsetOf(Values, (\<lambda>v. bEx(Ballots, (\<lambda>b. bEx(Quorums(b), (\<lambda>Q. bAll(Q, (\<lambda>a. bEx(msgs, (\<lambda>m. (((m[''type''])=''2b'')&(((m[''val''])=v)&(((m[''bal''])=b)&((m[''acc''])=a)))))))))))))))<=>(zenon_Vj \\in {})))))&(((m[''bal''])=x)&((m[''acc''])=a)))))))))))))&((m[''acc''])=x)))))))) ==> FALSE" (is "?z_hl ==> ?z_hcz ==> ?z_hda ==> FALSE")
 proof -
  assume z_Hl:"?z_hl" (is "?z_hm~=_")
  assume z_Hcz:"?z_hcz"
  assume z_Hda:"?z_hda" (is "\\A x : ?z_hdj(x)")
  have z_Hdk: "(~(\\A zenon_Vjd:((zenon_Vjd \\in ?z_hm)<=>(zenon_Vjd \\in {}))))" (is "~(\\A x : ?z_hdq(x))")
  by (rule zenon_notsetequal_0 [of "?z_hm" "{}", OF z_Hl])
  have z_Hdr: "(\\E zenon_Vjd:(~((zenon_Vjd \\in ?z_hm)<=>(zenon_Vjd \\in {}))))" (is "\\E x : ?z_hdt(x)")
  by (rule zenon_notallex_0 [of "?z_hdq", OF z_Hdk])
  have z_Hdu: "?z_hdt((CHOOSE zenon_Vjd:(~((zenon_Vjd \\in ?z_hm)<=>(zenon_Vjd \\in {})))))" (is "~(?z_hdw<=>?z_hdx)")
  by (rule zenon_ex_choose_0 [of "?z_hdt", OF z_Hdr])
  show FALSE
  proof (rule zenon_notequiv [OF z_Hdu])
   assume z_Hdy:"(~?z_hdw)"
   assume z_Hdx:"?z_hdx"
   show FALSE
   by (rule zenon_in_emptyset [of "(CHOOSE zenon_Vjd:(~((zenon_Vjd \\in ?z_hm)<=>(zenon_Vjd \\in {}))))", OF z_Hdx])
  next
   assume z_Hdw:"?z_hdw"
   assume z_Hdz:"(~?z_hdx)"
   have z_Hea: "?z_hdj((CHOOSE zenon_Vjd:(~((zenon_Vjd \\in ?z_hm)<=>(zenon_Vjd \\in {})))))" (is "_=>?z_heb")
   by (rule zenon_all_0 [of "?z_hdj" "(CHOOSE zenon_Vjd:(~((zenon_Vjd \\in ?z_hm)<=>(zenon_Vjd \\in {}))))", OF z_Hda])
   show FALSE
   proof (rule zenon_imply [OF z_Hea])
    assume z_Hdy:"(~?z_hdw)"
    show FALSE
    by (rule notE [OF z_Hdy z_Hdw])
   next
    assume z_Heb:"?z_heb"
    have z_Hec_z_Heb: "(\\E x:((x \\in msgs)&(((x[''type''])=''2b'')&(((x[''val''])=(CHOOSE zenon_Vj:(~((zenon_Vj \\in subsetOf(Values, (\<lambda>v. bEx(Ballots, (\<lambda>b. bEx(Quorums(b), (\<lambda>Q. bAll(Q, (\<lambda>a. bEx(msgs, (\<lambda>m. (((m[''type''])=''2b'')&(((m[''val''])=v)&(((m[''bal''])=b)&((m[''acc''])=a)))))))))))))))<=>(zenon_Vj \\in {})))))&(((x[''bal''])=(CHOOSE x:((x \\in Ballots)&bEx(Quorums(x), (\<lambda>Q. bAll(Q, (\<lambda>a. bEx(msgs, (\<lambda>m. (((m[''type''])=''2b'')&(((m[''val''])=(CHOOSE zenon_Vj:(~((zenon_Vj \\in subsetOf(Values, (\<lambda>v. bEx(Ballots, (\<lambda>b. bEx(Quorums(b), (\<lambda>Q. bAll(Q, (\<lambda>a. bEx(msgs, (\<lambda>m. (((m[''type''])=''2b'')&(((m[''val''])=v)&(((m[''bal''])=b)&((m[''acc''])=a)))))))))))))))<=>(zenon_Vj \\in {})))))&(((m[''bal''])=x)&((m[''acc''])=a)))))))))))))&((x[''acc''])=(CHOOSE zenon_Vjd:(~((zenon_Vjd \\in ?z_hm)<=>(zenon_Vjd \\in {})))))))))) == ?z_heb" (is "?z_hec == _")
    by (unfold bEx_def)
    have z_Hec: "?z_hec" (is "\\E x : ?z_heq(x)")
    by (unfold z_Hec_z_Heb, fact z_Heb)
    have z_Her: "?z_heq((CHOOSE x:((x \\in msgs)&(((x[''type''])=''2b'')&(((x[''val''])=(CHOOSE zenon_Vj:(~((zenon_Vj \\in subsetOf(Values, (\<lambda>v. bEx(Ballots, (\<lambda>b. bEx(Quorums(b), (\<lambda>Q. bAll(Q, (\<lambda>a. bEx(msgs, (\<lambda>m. (((m[''type''])=''2b'')&(((m[''val''])=v)&(((m[''bal''])=b)&((m[''acc''])=a)))))))))))))))<=>(zenon_Vj \\in {})))))&(((x[''bal''])=(CHOOSE x:((x \\in Ballots)&bEx(Quorums(x), (\<lambda>Q. bAll(Q, (\<lambda>a. bEx(msgs, (\<lambda>m. (((m[''type''])=''2b'')&(((m[''val''])=(CHOOSE zenon_Vj:(~((zenon_Vj \\in subsetOf(Values, (\<lambda>v. bEx(Ballots, (\<lambda>b. bEx(Quorums(b), (\<lambda>Q. bAll(Q, (\<lambda>a. bEx(msgs, (\<lambda>m. (((m[''type''])=''2b'')&(((m[''val''])=v)&(((m[''bal''])=b)&((m[''acc''])=a)))))))))))))))<=>(zenon_Vj \\in {})))))&(((m[''bal''])=x)&((m[''acc''])=a)))))))))))))&((x[''acc''])=(CHOOSE zenon_Vjd:(~((zenon_Vjd \\in ?z_hm)<=>(zenon_Vjd \\in {})))))))))))" (is "?z_het&?z_heu")
    by (rule zenon_ex_choose_0 [of "?z_heq", OF z_Hec])
    have z_Het: "?z_het"
    by (rule zenon_and_0 [OF z_Her])
    have z_Hev: "((CHOOSE x:((x \\in msgs)&(((x[''type''])=''2b'')&(((x[''val''])=(CHOOSE zenon_Vj:(~((zenon_Vj \\in subsetOf(Values, (\<lambda>v. bEx(Ballots, (\<lambda>b. bEx(Quorums(b), (\<lambda>Q. bAll(Q, (\<lambda>a. bEx(msgs, (\<lambda>m. (((m[''type''])=''2b'')&(((m[''val''])=v)&(((m[''bal''])=b)&((m[''acc''])=a)))))))))))))))<=>(zenon_Vj \\in {})))))&(((x[''bal''])=(CHOOSE x:((x \\in Ballots)&bEx(Quorums(x), (\<lambda>Q. bAll(Q, (\<lambda>a. bEx(msgs, (\<lambda>m. (((m[''type''])=''2b'')&(((m[''val''])=(CHOOSE zenon_Vj:(~((zenon_Vj \\in subsetOf(Values, (\<lambda>v. bEx(Ballots, (\<lambda>b. bEx(Quorums(b), (\<lambda>Q. bAll(Q, (\<lambda>a. bEx(msgs, (\<lambda>m. (((m[''type''])=''2b'')&(((m[''val''])=v)&(((m[''bal''])=b)&((m[''acc''])=a)))))))))))))))<=>(zenon_Vj \\in {})))))&(((m[''bal''])=x)&((m[''acc''])=a)))))))))))))&((x[''acc''])=(CHOOSE zenon_Vjd:(~((zenon_Vjd \\in ?z_hm)<=>(zenon_Vjd \\in {})))))))))) \\in {})" (is "?z_hev")
    by (rule subst [where P="(\<lambda>zenon_Vgi. ((CHOOSE x:((x \\in msgs)&(((x[''type''])=''2b'')&(((x[''val''])=(CHOOSE zenon_Vj:(~((zenon_Vj \\in subsetOf(Values, (\<lambda>v. bEx(Ballots, (\<lambda>b. bEx(Quorums(b), (\<lambda>Q. bAll(Q, (\<lambda>a. bEx(msgs, (\<lambda>m. (((m[''type''])=''2b'')&(((m[''val''])=v)&(((m[''bal''])=b)&((m[''acc''])=a)))))))))))))))<=>(zenon_Vj \\in {})))))&(((x[''bal''])=(CHOOSE x:((x \\in Ballots)&bEx(Quorums(x), (\<lambda>Q. bAll(Q, (\<lambda>a. bEx(msgs, (\<lambda>m. (((m[''type''])=''2b'')&(((m[''val''])=(CHOOSE zenon_Vj:(~((zenon_Vj \\in subsetOf(Values, (\<lambda>v. bEx(Ballots, (\<lambda>b. bEx(Quorums(b), (\<lambda>Q. bAll(Q, (\<lambda>a. bEx(msgs, (\<lambda>m. (((m[''type''])=''2b'')&(((m[''val''])=v)&(((m[''bal''])=b)&((m[''acc''])=a)))))))))))))))<=>(zenon_Vj \\in {})))))&(((m[''bal''])=x)&((m[''acc''])=a)))))))))))))&((x[''acc''])=(CHOOSE zenon_Vjd:(~((zenon_Vjd \\in ?z_hm)<=>(zenon_Vjd \\in {})))))))))) \\in zenon_Vgi))", OF z_Hcz z_Het])
    show FALSE
    by (rule zenon_in_emptyset [of "(CHOOSE x:((x \\in msgs)&(((x[''type''])=''2b'')&(((x[''val''])=(CHOOSE zenon_Vj:(~((zenon_Vj \\in subsetOf(Values, (\<lambda>v. bEx(Ballots, (\<lambda>b. bEx(Quorums(b), (\<lambda>Q. bAll(Q, (\<lambda>a. bEx(msgs, (\<lambda>m. (((m[''type''])=''2b'')&(((m[''val''])=v)&(((m[''bal''])=b)&((m[''acc''])=a)))))))))))))))<=>(zenon_Vj \\in {})))))&(((x[''bal''])=(CHOOSE x:((x \\in Ballots)&bEx(Quorums(x), (\<lambda>Q. bAll(Q, (\<lambda>a. bEx(msgs, (\<lambda>m. (((m[''type''])=''2b'')&(((m[''val''])=(CHOOSE zenon_Vj:(~((zenon_Vj \\in subsetOf(Values, (\<lambda>v. bEx(Ballots, (\<lambda>b. bEx(Quorums(b), (\<lambda>Q. bAll(Q, (\<lambda>a. bEx(msgs, (\<lambda>m. (((m[''type''])=''2b'')&(((m[''val''])=v)&(((m[''bal''])=b)&((m[''acc''])=a)))))))))))))))<=>(zenon_Vj \\in {})))))&(((m[''bal''])=x)&((m[''acc''])=a)))))))))))))&((x[''acc''])=(CHOOSE zenon_Vjd:(~((zenon_Vjd \\in ?z_hm)<=>(zenon_Vjd \\in {}))))))))))", OF z_Hev])
   qed
  qed
 qed
 assume z_Hb:"(~(((msgs={})&((maxVBal=Fcn(Acceptors, (\<lambda>a.  -.(1))))&((maxBal=Fcn(Acceptors, (\<lambda>a.  -.(1))))&(maxVal=Fcn(Acceptors, (\<lambda>a. None))))))=>(subsetOf(Values, (\<lambda>v. bEx(Ballots, (\<lambda>b. bEx(Quorums(b), (\<lambda>Q. bAll(Q, (\<lambda>a. bEx(msgs, (\<lambda>m. (((m[''type''])=''2b'')&(((m[''val''])=v)&(((m[''bal''])=b)&((m[''acc''])=a))))))))))))))={})))" (is "~(?z_hfa=>?z_hfr)")
 have z_Hfs_z_Ha: "(\\A x:((x \\in Ballots)=>bAll(Quorums(x), (\<lambda>Q. (Q~={}))))) == ?z_ha" (is "?z_hfs == _")
 by (unfold bAll_def)
 have z_Hfs: "?z_hfs" (is "\\A x : ?z_hfv(x)")
 by (unfold z_Hfs_z_Ha, fact z_Ha)
 have z_Hfa: "?z_hfa" (is "?z_hcz&?z_hfb")
 by (rule zenon_notimply_0 [OF z_Hb])
 have z_Hfw: "(subsetOf(Values, (\<lambda>v. bEx(Ballots, (\<lambda>b. bEx(Quorums(b), (\<lambda>Q. bAll(Q, (\<lambda>a. bEx(msgs, (\<lambda>m. (((m[''type''])=''2b'')&(((m[''val''])=v)&(((m[''bal''])=b)&((m[''acc''])=a))))))))))))))~={})" (is "?z_hbr~=_")
 by (rule zenon_notimply_1 [OF z_Hb])
 have z_Hcz: "?z_hcz"
 by (rule zenon_and_0 [OF z_Hfa])
 have z_Hfx: "(~(\\A zenon_Vj:((zenon_Vj \\in ?z_hbr)<=>(zenon_Vj \\in {}))))" (is "~(\\A x : ?z_hfz(x))")
 by (rule zenon_notsetequal_0 [of "?z_hbr" "{}", OF z_Hfw])
 have z_Hga: "(\\E zenon_Vj:(~((zenon_Vj \\in ?z_hbr)<=>(zenon_Vj \\in {}))))" (is "\\E x : ?z_hgb(x)")
 by (rule zenon_notallex_0 [of "?z_hfz", OF z_Hfx])
 have z_Hgc: "?z_hgb((CHOOSE zenon_Vj:(~((zenon_Vj \\in ?z_hbr)<=>(zenon_Vj \\in {})))))" (is "~(?z_hgd<=>?z_hge)")
 by (rule zenon_ex_choose_0 [of "?z_hgb", OF z_Hga])
 show FALSE
 proof (rule zenon_notequiv [OF z_Hgc])
  assume z_Hgf:"(~?z_hgd)"
  assume z_Hge:"?z_hge"
  show FALSE
  by (rule zenon_in_emptyset [of "(CHOOSE zenon_Vj:(~((zenon_Vj \\in ?z_hbr)<=>(zenon_Vj \\in {}))))", OF z_Hge])
 next
  assume z_Hgd:"?z_hgd"
  assume z_Hgg:"(~?z_hge)"
  have z_Hgh: "bEx(Ballots, (\<lambda>b. bEx(Quorums(b), (\<lambda>Q. bAll(Q, (\<lambda>a. bEx(msgs, (\<lambda>m. (((m[''type''])=''2b'')&(((m[''val''])=(CHOOSE zenon_Vj:(~((zenon_Vj \\in ?z_hbr)<=>(zenon_Vj \\in {})))))&(((m[''bal''])=b)&((m[''acc''])=a))))))))))))" (is "?z_hgh")
  by (rule zenon_in_subsetof_1 [of "(CHOOSE zenon_Vj:(~((zenon_Vj \\in ?z_hbr)<=>(zenon_Vj \\in {}))))" "Values" "(\<lambda>v. bEx(Ballots, (\<lambda>b. bEx(Quorums(b), (\<lambda>Q. bAll(Q, (\<lambda>a. bEx(msgs, (\<lambda>m. (((m[''type''])=''2b'')&(((m[''val''])=v)&(((m[''bal''])=b)&((m[''acc''])=a)))))))))))))", OF z_Hgd])
  have z_Hgr_z_Hgh: "(\\E x:((x \\in Ballots)&bEx(Quorums(x), (\<lambda>Q. bAll(Q, (\<lambda>a. bEx(msgs, (\<lambda>m. (((m[''type''])=''2b'')&(((m[''val''])=(CHOOSE zenon_Vj:(~((zenon_Vj \\in ?z_hbr)<=>(zenon_Vj \\in {})))))&(((m[''bal''])=x)&((m[''acc''])=a)))))))))))) == ?z_hgh" (is "?z_hgr == _")
  by (unfold bEx_def)
  have z_Hgr: "?z_hgr" (is "\\E x : ?z_hgs(x)")
  by (unfold z_Hgr_z_Hgh, fact z_Hgh)
  have z_Hgt: "?z_hgs((CHOOSE x:((x \\in Ballots)&bEx(Quorums(x), (\<lambda>Q. bAll(Q, (\<lambda>a. bEx(msgs, (\<lambda>m. (((m[''type''])=''2b'')&(((m[''val''])=(CHOOSE zenon_Vj:(~((zenon_Vj \\in ?z_hbr)<=>(zenon_Vj \\in {})))))&(((m[''bal''])=x)&((m[''acc''])=a)))))))))))))" (is "?z_hgu&?z_hgv")
  by (rule zenon_ex_choose_0 [of "?z_hgs", OF z_Hgr])
  have z_Hgu: "?z_hgu"
  by (rule zenon_and_0 [OF z_Hgt])
  have z_Hgv: "?z_hgv"
  by (rule zenon_and_1 [OF z_Hgt])
  have z_Hgw_z_Hgv: "(\\E x:((x \\in Quorums((CHOOSE x:((x \\in Ballots)&bEx(Quorums(x), (\<lambda>Q. bAll(Q, (\<lambda>a. bEx(msgs, (\<lambda>m. (((m[''type''])=''2b'')&(((m[''val''])=(CHOOSE zenon_Vj:(~((zenon_Vj \\in ?z_hbr)<=>(zenon_Vj \\in {})))))&(((m[''bal''])=x)&((m[''acc''])=a))))))))))))))&bAll(x, (\<lambda>a. bEx(msgs, (\<lambda>m. (((m[''type''])=''2b'')&(((m[''val''])=(CHOOSE zenon_Vj:(~((zenon_Vj \\in ?z_hbr)<=>(zenon_Vj \\in {})))))&(((m[''bal''])=(CHOOSE x:((x \\in Ballots)&bEx(Quorums(x), (\<lambda>Q. bAll(Q, (\<lambda>a. bEx(msgs, (\<lambda>m. (((m[''type''])=''2b'')&(((m[''val''])=(CHOOSE zenon_Vj:(~((zenon_Vj \\in ?z_hbr)<=>(zenon_Vj \\in {})))))&(((m[''bal''])=x)&((m[''acc''])=a)))))))))))))&((m[''acc''])=a)))))))))) == ?z_hgv" (is "?z_hgw == _")
  by (unfold bEx_def)
  have z_Hgw: "?z_hgw" (is "\\E x : ?z_hgx(x)")
  by (unfold z_Hgw_z_Hgv, fact z_Hgv)
  have z_Hgy: "?z_hgx((CHOOSE x:((x \\in Quorums((CHOOSE x:((x \\in Ballots)&bEx(Quorums(x), (\<lambda>Q. bAll(Q, (\<lambda>a. bEx(msgs, (\<lambda>m. (((m[''type''])=''2b'')&(((m[''val''])=(CHOOSE zenon_Vj:(~((zenon_Vj \\in ?z_hbr)<=>(zenon_Vj \\in {})))))&(((m[''bal''])=x)&((m[''acc''])=a))))))))))))))&bAll(x, (\<lambda>a. bEx(msgs, (\<lambda>m. (((m[''type''])=''2b'')&(((m[''val''])=(CHOOSE zenon_Vj:(~((zenon_Vj \\in ?z_hbr)<=>(zenon_Vj \\in {})))))&(((m[''bal''])=(CHOOSE x:((x \\in Ballots)&bEx(Quorums(x), (\<lambda>Q. bAll(Q, (\<lambda>a. bEx(msgs, (\<lambda>m. (((m[''type''])=''2b'')&(((m[''val''])=(CHOOSE zenon_Vj:(~((zenon_Vj \\in ?z_hbr)<=>(zenon_Vj \\in {})))))&(((m[''bal''])=x)&((m[''acc''])=a)))))))))))))&((m[''acc''])=a)))))))))))" (is "?z_hgz&?z_hha")
  by (rule zenon_ex_choose_0 [of "?z_hgx", OF z_Hgw])
  have z_Hgz: "?z_hgz"
  by (rule zenon_and_0 [OF z_Hgy])
  have z_Hha: "?z_hha"
  by (rule zenon_and_1 [OF z_Hgy])
  have z_Hda_z_Hha: "(\\A x:((x \\in (CHOOSE x:((x \\in Quorums((CHOOSE x:((x \\in Ballots)&bEx(Quorums(x), (\<lambda>Q. bAll(Q, (\<lambda>a. bEx(msgs, (\<lambda>m. (((m[''type''])=''2b'')&(((m[''val''])=(CHOOSE zenon_Vj:(~((zenon_Vj \\in ?z_hbr)<=>(zenon_Vj \\in {})))))&(((m[''bal''])=x)&((m[''acc''])=a))))))))))))))&bAll(x, (\<lambda>a. bEx(msgs, (\<lambda>m. (((m[''type''])=''2b'')&(((m[''val''])=(CHOOSE zenon_Vj:(~((zenon_Vj \\in ?z_hbr)<=>(zenon_Vj \\in {})))))&(((m[''bal''])=(CHOOSE x:((x \\in Ballots)&bEx(Quorums(x), (\<lambda>Q. bAll(Q, (\<lambda>a. bEx(msgs, (\<lambda>m. (((m[''type''])=''2b'')&(((m[''val''])=(CHOOSE zenon_Vj:(~((zenon_Vj \\in ?z_hbr)<=>(zenon_Vj \\in {})))))&(((m[''bal''])=x)&((m[''acc''])=a)))))))))))))&((m[''acc''])=a)))))))))))=>bEx(msgs, (\<lambda>m. (((m[''type''])=''2b'')&(((m[''val''])=(CHOOSE zenon_Vj:(~((zenon_Vj \\in ?z_hbr)<=>(zenon_Vj \\in {})))))&(((m[''bal''])=(CHOOSE x:((x \\in Ballots)&bEx(Quorums(x), (\<lambda>Q. bAll(Q, (\<lambda>a. bEx(msgs, (\<lambda>m. (((m[''type''])=''2b'')&(((m[''val''])=(CHOOSE zenon_Vj:(~((zenon_Vj \\in ?z_hbr)<=>(zenon_Vj \\in {})))))&(((m[''bal''])=x)&((m[''acc''])=a)))))))))))))&((m[''acc''])=x)))))))) == ?z_hha" (is "?z_hda == _")
  by (unfold bAll_def)
  have z_Hda: "?z_hda" (is "\\A x : ?z_hdj(x)")
  by (unfold z_Hda_z_Hha, fact z_Hha)
  have z_Hhb: "?z_hfv((CHOOSE x:((x \\in Ballots)&bEx(Quorums(x), (\<lambda>Q. bAll(Q, (\<lambda>a. bEx(msgs, (\<lambda>m. (((m[''type''])=''2b'')&(((m[''val''])=(CHOOSE zenon_Vj:(~((zenon_Vj \\in ?z_hbr)<=>(zenon_Vj \\in {})))))&(((m[''bal''])=x)&((m[''acc''])=a)))))))))))))" (is "_=>?z_hhc")
  by (rule zenon_all_0 [of "?z_hfv" "(CHOOSE x:((x \\in Ballots)&bEx(Quorums(x), (\<lambda>Q. bAll(Q, (\<lambda>a. bEx(msgs, (\<lambda>m. (((m[''type''])=''2b'')&(((m[''val''])=(CHOOSE zenon_Vj:(~((zenon_Vj \\in ?z_hbr)<=>(zenon_Vj \\in {})))))&(((m[''bal''])=x)&((m[''acc''])=a))))))))))))", OF z_Hfs])
  show FALSE
  proof (rule zenon_imply [OF z_Hhb])
   assume z_Hhd:"(~?z_hgu)"
   show FALSE
   by (rule notE [OF z_Hhd z_Hgu])
  next
   assume z_Hhc:"?z_hhc"
   have z_Hl: "((CHOOSE x:((x \\in Quorums((CHOOSE x:((x \\in Ballots)&bEx(Quorums(x), (\<lambda>Q. bAll(Q, (\<lambda>a. bEx(msgs, (\<lambda>m. (((m[''type''])=''2b'')&(((m[''val''])=(CHOOSE zenon_Vj:(~((zenon_Vj \\in ?z_hbr)<=>(zenon_Vj \\in {})))))&(((m[''bal''])=x)&((m[''acc''])=a))))))))))))))&bAll(x, (\<lambda>a. bEx(msgs, (\<lambda>m. (((m[''type''])=''2b'')&(((m[''val''])=(CHOOSE zenon_Vj:(~((zenon_Vj \\in ?z_hbr)<=>(zenon_Vj \\in {})))))&(((m[''bal''])=(CHOOSE x:((x \\in Ballots)&bEx(Quorums(x), (\<lambda>Q. bAll(Q, (\<lambda>a. bEx(msgs, (\<lambda>m. (((m[''type''])=''2b'')&(((m[''val''])=(CHOOSE zenon_Vj:(~((zenon_Vj \\in ?z_hbr)<=>(zenon_Vj \\in {})))))&(((m[''bal''])=x)&((m[''acc''])=a)))))))))))))&((m[''acc''])=a))))))))))~={})" (is "?z_hm~=_")
   by (rule zenon_all_in_0 [of "Quorums((CHOOSE x:((x \\in Ballots)&bEx(Quorums(x), (\<lambda>Q. bAll(Q, (\<lambda>a. bEx(msgs, (\<lambda>m. (((m[''type''])=''2b'')&(((m[''val''])=(CHOOSE zenon_Vj:(~((zenon_Vj \\in ?z_hbr)<=>(zenon_Vj \\in {})))))&(((m[''bal''])=x)&((m[''acc''])=a)))))))))))))" "(\<lambda>Q. (Q~={}))", OF z_Hhc z_Hgz])
   show FALSE
   by (rule zenon_L1_ [OF z_Hl z_Hcz z_Hda])
  qed
 qed
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 259"; *} qed
end
