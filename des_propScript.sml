open HolKernel Parse boolLib bossLib;

open arithmeticTheory numLib pairTheory fcpTheory fcpLib wordsTheory wordsLib
     listTheory listLib sortingTheory pred_setTheory combinTheory hurdUtils;

open desTheory;

val fcp_ss = std_ss ++ fcpLib.FCP_ss;

Theorem compl_IIP:
  !m. IIP(~m) = ~ (IIP m)
Proof    
    RW_TAC fcp_ss[IIP_def, bitwise_perm_def,dimindex_64]
  >>Q.ABBREV_TAC ‘p=(64 − EL (63 − i) IIP_data)’
  >>Know ‘p<64’
  >- (fs [Abbr ‘p’, dimindex_64] \\
      POP_ASSUM MP_TAC \\        
      Q.SPEC_TAC (‘i’, ‘n’) \\
      rpt (CONV_TAC (BOUNDED_FORALL_CONV (SIMP_CONV list_ss [IIP_data]))) \\
      REWRITE_TAC [])
  >>rw[word_1comp_def] 
  >>rw[FCP_BETA]
QED

Theorem compl_E:
  ∀m. E (¬m)=~ (E m)
Proof
    RW_TAC fcp_ss[E_def, bitwise_perm_def,dimindex_64]
  >>Know ‘ (dimindex (:32) − EL (dimindex (:48) − 1 − i) E_data)<32’
  >- (fs [dimindex_48] \\
      POP_ASSUM MP_TAC \\       
      Q.SPEC_TAC (‘i’, ‘n’) \\
      rpt (CONV_TAC (BOUNDED_FORALL_CONV (SIMP_CONV list_ss [E_data]))) \\
      REWRITE_TAC [])
  >>rw[word_1comp_def]
  >>rw[FCP_BETA]
QED

Theorem compl_IP:
  ∀m. IP (¬m)=~ (IP m)
Proof
    RW_TAC fcp_ss[IP_def,bitwise_perm_def, dimindex_64]
  >>Know ‘(64 − EL (63 − i) IP_data)<64’
  >- (fs [dimindex_64] \\
      POP_ASSUM MP_TAC \\       
      Q.SPEC_TAC (‘i’, ‘n’) \\
      rpt (CONV_TAC (BOUNDED_FORALL_CONV (SIMP_CONV list_ss [IP_data]))) \\
      REWRITE_TAC []) 
  >>rw[word_1comp_def]
  >>rw[FCP_BETA]
QED  

Theorem compl_join:
  !m n. Join (~m,~n) = ~Join (m,n)
Proof
     RW_TAC fcp_ss[Join_def]
  >> rw[word_concat_def,word_join_def]
  >> rw[w2w,word_1comp_def,word_or_def,FCP_BETA,word_lsl_def]
  >> POP_ASSUM MP_TAC
  >> fs[dimindex_64]
  >> rw[FCP_BETA]
  >> rw[w2w]
  >> Cases_on ‘i<32’
  >- rw[FCP_BETA]
  >> rw[FCP_BETA]
QED

Theorem compl_extract_1:
  !(m:word64). (63 >< 32) ~m = ~(63 >< 32) m
Proof
     RW_TAC fcp_ss[word_extract_def]
  >> rw[word_bits_def]
  >> rw[w2w,word_1comp_def,FCP_BETA]
  >> POP_ASSUM MP_TAC
  >> fs[dimindex_32]
  >> rw[FCP_BETA]
QED

Theorem compl_extract_2:
  !(m:word64). (31 >< 0) ~m = ~(31 >< 0) m
Proof
     RW_TAC fcp_ss[word_extract_def]
  >> rw[word_bits_def]
  >> rw[w2w,word_1comp_def,FCP_BETA]
  >> POP_ASSUM MP_TAC
  >> fs[dimindex_32]
  >> rw[FCP_BETA]
QED

Definition roundk_L:
    RK_L 0 (k:word64) = FST(PC1 k) /\
    RK_L (SUC n) (k :word64) =
      let c = RK_L n k; r= EL n R_data
      in (c #<< r)
End 

Definition roundk_R:
    RK_R 0 (k:word64) = SND(PC1 k) /\
    RK_R (SUC n) (k :word64) =
      let c = RK_R n k; r= EL n R_data
      in (c #<< r)
End

Definition roundk_supp:
    RK n (k:word64) = (RK_L n k,RK_R n k)
End 
        
Theorem compl_RK_L:
  !n (k:word64). 17 > n ==>(RK_L n ~k)=~(RK_L n k)
Proof
    rw[]
  >> Induct_on `n`
  >- (rw[]\\
     rw[roundk_L]\\
     rw[PC1_def]\\
     rw[bitwise_perm_def]\\
     RW_TAC fcp_ss[word_extract_def]\\
     rw[word_bits_def]\\
     rw[w2w,word_1comp_def,FCP_BETA]\\
     POP_ASSUM MP_TAC\\
     fs[dimindex_28]\\
     rw[word_1comp_def,FCP_BETA]\\
     Suff ‘(64 − EL (27 − i) PC1_data)<64’
     >-rw[word_1comp_def,FCP_BETA] \\
     fs [dimindex_64] \\
     POP_ASSUM MP_TAC \\       
     Q.SPEC_TAC (‘i’, ‘n’) \\
     rpt (CONV_TAC (BOUNDED_FORALL_CONV (SIMP_CONV list_ss [PC1_data]))) \\
     REWRITE_TAC [])
  >> rw[roundk_L]
  >> Q.ABBREV_TAC`a=RK_L n k`
  >> Q.ABBREV_TAC`b=EL n R_data `
  >> rw[word_rol_def]
  >> RW_TAC fcp_ss[word_ror_def]
  >> Suff ‘((i + (28 − b MOD 28)) MOD dimindex (:28))<64’
  >- (rw[word_1comp_def]\\
      rw[FCP_BETA])
  >> fs [dimindex_64]
  >> rw[Abbr `b`] 
  >> qabbrev_tac ‘m = (i + (28 − EL n R_data MOD 28))’
  >> MATCH_MP_TAC LESS_TRANS
  >> Q.EXISTS_TAC ‘28’
  >> rw[MOD_LESS]
QED
  
Theorem compl_RK_R :
   !n (k:word64). 17 > n ==>(RK_R n ~k)=~(RK_R n k)
Proof
     rw[]
  >> Induct_on `n`
  >- (rw[]\\
     rw[roundk_R]\\
     rw[PC1_def]\\
     rw[bitwise_perm_def]\\
     RW_TAC fcp_ss[word_extract_def]\\
     rw[word_bits_def]\\
     rw[w2w,word_1comp_def,FCP_BETA]\\
     POP_ASSUM MP_TAC\\
     fs[dimindex_28]\\
     rw[word_1comp_def,FCP_BETA]\\
     Suff ‘(64 − EL (55 − i) PC1_data)<64’
     >- rw[word_1comp_def,FCP_BETA] \\
     fs [dimindex_64] \\
     POP_ASSUM MP_TAC \\       
     Q.SPEC_TAC (‘i’, ‘n’) \\
     rpt (CONV_TAC (BOUNDED_FORALL_CONV (SIMP_CONV list_ss [PC1_data]))) \\
     REWRITE_TAC [])
  >> rw[roundk_R]
  >> Q.ABBREV_TAC`a=RK_R n k`
  >> Q.ABBREV_TAC`b=EL n R_data `
  >> rw[word_rol_def]
  >> RW_TAC fcp_ss[word_ror_def]
  >> Suff ‘((i + (28 − b MOD 28)) MOD dimindex (:28))<64’
  >- (rw[word_1comp_def]\\
      rw[FCP_BETA])
  >> fs [dimindex_64]
  >> rw[Abbr `b`] 
  >> qabbrev_tac ‘m = (i + (28 − EL n R_data MOD 28))’
  >> MATCH_MP_TAC LESS_TRANS
  >> Q.EXISTS_TAC ‘28’
  >> rw[MOD_LESS]
QED

Theorem convert_RK:
  !(k:word64) n. RoundKey n k=REVERSE (GENLIST (λi. RK i k) (SUC n))
Proof
    Induct_on `n`
  >- (RW_TAC fcp_ss[RoundKey_def,GENLIST,roundk_supp,REVERSE_DEF,roundk_R,roundk_L]\\
      rw[])
  >> RW_TAC fcp_ss[RoundKey_def,GENLIST,roundk_supp,REVERSE_DEF,roundk_R,roundk_L]
  >> Suff `HD ks = (c',c)`
  >- (rw []\\
      rw[Abbr `ks`])
  >> rw[Abbr `ks`]
  >- (Q.PAT_X_ASSUM ‘HD (REVERSE (SNOC (c',c) (GENLIST (λi. (RK_L i k,RK_R i k)) n))) = _’ MP_TAC \\
      rw[HD_REVERSE])
  >> Q.PAT_X_ASSUM ‘HD (REVERSE (SNOC (c',c) (GENLIST (λi. (RK_L i k,RK_R i k)) n))) = _’ MP_TAC 
  >> rw[HD_REVERSE]
QED

Theorem comple_PC2:
  ∀(a:word28) (b:word28). PC2 (~a,~b) = ~PC2(a,b)
Proof
     rw[PC2_def]
  >> RW_TAC fcp_ss[bitwise_perm_def]
  >> Suff ` a @@ b = ~(~a @@ ~b)`
  >- (rw[]\\
      Know `(56 − EL (47 − i) PC2_data)<56`
      >- (fs [dimindex_56] \\
      POP_ASSUM MP_TAC \\
      POP_ASSUM MP_TAC \\   
      Q.SPEC_TAC (‘i’, ‘n’) \\
      rpt (CONV_TAC (BOUNDED_FORALL_CONV (SIMP_CONV list_ss [PC2_data]))) \\
      REWRITE_TAC []) \\
      rw[word_1comp_def]\\
      rw[FCP_BETA])
   >> RW_TAC fcp_ss[]
   >> rw[word_concat_def,word_join_def]
   >> rw[w2w,word_1comp_def,word_or_def,FCP_BETA,word_lsl_def]
   >> POP_ASSUM MP_TAC
   >> POP_ASSUM MP_TAC
   >> fs[dimindex_48]
   >> rw[FCP_BETA]
   >> rw[w2w]
   >> Cases_on ‘i'<28’
   >- rw[FCP_BETA]
   >> rw[FCP_BETA]
QED

Theorem comple_property:
  ∀k m n.0 < n /\ n< 17 ==> ~ ((FST(DES n k)) m)= (FST(DES n (~ k))) (~ m)
Proof
     RW_TAC fcp_ss[DES_def,o_DEF, desCore_def, desRound_alt_Round']
  >> RW_TAC fcp_ss[]
  >> Suff ‘(Join (Swap (Round n keys (Split (IP m)))))=
              ~(Join (Swap (Round n keys' (Split (IP (¬m))))))’          
  >- (Rewr' \\
      rw[compl_IIP])
  >> rw[Split_def]
  >> REWRITE_TAC [Round_alt_half_message]                      
  >> rw[Swap_def]
  >>  Q.ABBREV_TAC ‘u=(63 >< 32) (IP m)’
  >>  Q.ABBREV_TAC ‘v=(31 >< 0) (IP m)’
  >>  Q.ABBREV_TAC ‘u'=(63 >< 32) (IP (¬m))’
  >>  Q.ABBREV_TAC ‘v'=(31 >< 0) (IP (¬m))’            
  >> Suff ‘(M (u',v') keys' (SUC n),M (u',v') keys' n)=
              (~M (u,v) keys (SUC n),~M (u,v) keys n)’
  >- (Rewr' \\
      rw [compl_join] \\
      rw[])               
  >>Suff ‘ (M (u',v') keys' n,M (u',v') keys' (SUC n)) =
          (¬M (u,v) keys n,¬M (u,v) keys (SUC n))’
  >- rw[]
  >>Suff ‘∀x.x<=n ==>(M (u',v') keys' x,M (u',v') keys' (SUC(x)))           
          = (¬M (u,v) keys x,¬M (u,v) keys (SUC(x)))’
  >- rw[]
  >> Induct_on ‘x’ 
  >- (simp [] \\
      Know ‘(M (u',v') keys' 0,M (u',v') keys' (SUC 0))=
            Round 0 keys' (u',v')’
  >- RW_TAC fcp_ss[Round_alt_half_message']
  >> Know ‘Round 0 keys' (u',v')= (u',v')’
  >- rw [Round_def]
  >> Know ‘(M (u,v) keys 0,M (u,v) keys (SUC 0))=Round 0 keys (u,v)’
  >- RW_TAC fcp_ss[Round_alt_half_message']
  >> Know ‘Round 0 keys (u,v)= (u,v)’
  >- rw [Round_def]
  >> rw[]
  >| [ (* goal 1 (of 2) *)
       rw [Abbr ‘u'’,Abbr ‘u’] \\
       Know `(IP m)=~(IP (¬m))` \\
       rw[compl_IP] \\
       rw [compl_extract_1] \\
       rw[],
       (* goal 2 (of 2) *)
       rw [Abbr ‘v'’,Abbr ‘v’]\\
       Know `(IP m)=~(IP (¬m))` \\
       rw[compl_IP]\\
       rw [compl_extract_2] \\
       rw[] ])
  >> DISCH_TAC
  >> ‘x <= n’ by rw []
  >> fs []
  >> Know ‘(SUC (SUC x))= x+2’
  >- rw[]
  >> Rewr'
  >> Q.PAT_X_ASSUM ‘M (u',v') keys' (SUC x) = _’ MP_TAC         
  >> Know ‘(SUC x)= x+1’
  >- rw[]
  >> Rewr'
  >> rw[]
  >> Know ‘ M (u',v') keys' (x+2)=
              M (u',v') keys' x ?? (RoundOp (M(u',v') keys' (x+1)) (EL x keys'))’
  >- rw[half_message']
  >> Rewr'
     >> Know ‘ ~M (u,v) keys (x+2)=
              ~(M (u,v) keys x ?? (RoundOp (M (u,v) keys (x+1)) (EL x keys)))’
  >- rw[half_message']
  >> Rewr'
  >> rw[]                
  >> Suff ‘RoundOp (¬M (u,v) keys (x + 1)) (EL x keys')=
              RoundOp (M (u,v) keys (x + 1)) (EL x keys)’
  >- (rw[WORD_NOT_XOR])
  >> rw[RoundOp_def]     
  >> Know ‘E (~M (u,v) keys (x + 1))=~E (M (u,v) keys (x + 1))’
  >- (rw[compl_E])
  >> Rewr'
  >> Suff ‘EL x keys'=~EL x keys’
  >- rw[WORD_NOT_XOR]
  >> rw [Abbr ‘keys'’, Abbr ‘keys’]  
  >> rw[KS_def]
  >> rw[convert_RK]
  >> qabbrev_tac ‘l = GENLIST (λi. RK i k) (SUC n)’ 
  >>  Know ‘GENLIST (\i. RK i (~k)) (SUC n) =
           MAP (\(a,b). (~a,~b)) l’
  >- (rw [Abbr ‘l’, LIST_EQ_REWRITE] \\
      rename1 ‘j < SUC n’ \\
      rw [EL_MAP] \\
      rw [roundk_supp] 
      >| [rw [compl_RK_L],
          rw [compl_RK_R] ])
  >> Rewr'
  >> ‘SUC x < LENGTH l’ by rw[Abbr ‘l’]
  >> qabbrev_tac ‘l' = MAP PC2 (TL l)’
  >> ‘x < LENGTH l'’
    by (rw [Abbr ‘l'’, LENGTH_MAP, LENGTH_TL])
  >> Know ‘~EL x l' = EL x (MAP (\e. ~e) l')’
  >- (rw [EL_MAP, LENGTH_MAP])
  >> Rewr'
  >> qunabbrev_tac ‘l'’
  >> simp [GSYM MAP_TL]
  >> simp [MAP_MAP_o]
  >> simp [o_DEF]
  >> Suff ‘(λx. PC2 ((λ(a,b). (¬a,¬b)) x)) =
               (λx. ¬PC2 x)’   
  >- rw []
  >> simp [FUN_EQ_THM]
  >> simp [FORALL_PROD]
  >> rw[comple_PC2]
QED

#week keys
Definition Weak_key1:
  w_key1 :word64=0x0101010101010101w
End

Definition Weak_key2:
  w_key2 :word64=0xfefefefefefefefew
End

Definition Weak_key3:
  w_key3 :word64=0xe0e0e0e0f1f1f1f1w
End

Definition Weak_key4:
  w_key4 :word64=0x1f1f1f1f0e0e0e0ew
End

Theorem weakK_proper1:
  !plaintext. ((FST(FullDES w_key1)) ((FST(FullDES w_key1)) plaintext) = plaintext)
Proof
     rw[DES_def]
  >> Know ‘LENGTH (KS w_key1 16)=16’
  >- rw [LENGTH_KS]                                
  >> Suff ‘desCore 16 (KS w_key1 16) (desCore 16 (KS w_key1 16) plaintext)=
     desCore 16 (REVERSE (KS w_key1 16)) (desCore 16 (KS w_key1 16) plaintext)’
  >- rw [desCore_CORRECT]   
  >> Suff ‘((REVERSE (KS w_key1 16))=KS w_key1 16)’
  >- rw[]
  >> rw[KS_def]
  >> EVAL_TAC
QED

Theorem weakK_proper2:
  !plaintext. ((FST(FullDES w_key2)) ((FST(FullDES w_key2)) plaintext) = plaintext)
Proof
     rw[DES_def]
  >> Know ‘LENGTH (KS w_key2 16)=16’
  >- rw [LENGTH_KS]                                
  >> Suff ‘desCore 16 (KS w_key2 16) (desCore 16 (KS w_key2 16) plaintext)=
     desCore 16 (REVERSE (KS w_key2 16)) (desCore 16 (KS w_key2 16) plaintext)’
  >- rw [desCore_CORRECT]   
  >> Suff ‘((REVERSE (KS w_key2 16))=KS w_key2 16)’
  >- rw[]
  >> rw[KS_def]
  >> EVAL_TAC
QED

Theorem weakK_proper3:
  !plaintext. ((FST(FullDES w_key3)) ((FST(FullDES w_key3)) plaintext) = plaintext)
Proof
     rw[DES_def]
  >> Know ‘LENGTH (KS w_key3 16)=16’
  >- rw [LENGTH_KS]                                
  >> Suff ‘desCore 16 (KS w_key3 16) (desCore 16 (KS w_key3 16) plaintext)=
     desCore 16 (REVERSE (KS w_key3 16)) (desCore 16 (KS w_key3 16) plaintext)’
  >- rw [desCore_CORRECT]   
  >> Suff ‘((REVERSE (KS w_key3 16))=KS w_key3 16)’
  >- rw[]
  >> rw[KS_def]
  >> EVAL_TAC
QED

Theorem weakK_proper4:
  !plaintext. ((FST(FullDES w_key4)) ((FST(FullDES w_key4)) plaintext) = plaintext)
Proof
     rw[DES_def]
  >> Know ‘LENGTH (KS w_key4 16)=16’
  >- rw [LENGTH_KS]                                
  >> Suff ‘desCore 16 (KS w_key4 16) (desCore 16 (KS w_key4 16) plaintext)=
     desCore 16 (REVERSE (KS w_key4 16)) (desCore 16 (KS w_key4 16) plaintext)’
  >- rw [desCore_CORRECT]   
  >> Suff ‘((REVERSE (KS w_key4 16))=KS w_key4 16)’
  >- rw[]
  >> rw[KS_def]
  >> EVAL_TAC
QED

#semi-week keys
Definition semiWeak_key1:
  semi_key1 =(0x01fe01fe01fe01few:word64,0xfe01fe01fe01fe01w:word64)
End        

Definition semiWeak_key2:
  semi_key2 =(0x1fe01fe00ef10ef1w:word64,0xe01fe01ff10ef10ew:word64)
End

Definition semiWeak_key3:
  semi_key3 =(0x01e001e001f101f1w:word64,0xe001e001f101f101w:word64)
End        

Definition semiWeak_key4:
  semi_key4 =(0x1ffe1ffe0efe0efew:word64,0xfe1ffe1ffe0efe0ew:word64)
End

Definition semiWeak_key5:
  semi_key5 =(0x011f011f010e010ew:word64,0x1f011f010e010e01w:word64)
End

Definition semiWeak_key6:
  semi_key6 =(0xe0fee0fef1fef1few:word64,0xfee0fee0fef1fef1w:word64)
End

Theorem semiK_proper1:
  !plaintext. ((FST(FullDES (FST(semi_key1)))) ((FST(FullDES (SND(semi_key1)))) plaintext) = plaintext)  ∧
  ((FST(FullDES (SND(semi_key1)))) ((FST(FullDES (FST(semi_key1)))) plaintext) = plaintext)
Proof
     rw[DES_def]
  >- (Know ‘LENGTH ((KS (SND semi_key1) 16))=16’
      >- rw [LENGTH_KS] \\ 
      Suff ‘KS (FST semi_key1) 16 =REVERSE (KS (SND semi_key1) 16)’
      >- rw [desCore_CORRECT] \\
      EVAL_TAC)
  >> Know ‘LENGTH ((KS (FST semi_key1) 16))=16’
  >- rw [LENGTH_KS] 
  >> Suff ‘KS (SND semi_key1) 16 =REVERSE (KS (FST semi_key1) 16)’
  >- rw [desCore_CORRECT]
  >> EVAL_TAC
QED

Theorem semiK_proper2:
  !plaintext. ((FST(FullDES (FST(semi_key2)))) ((FST(FullDES (SND(semi_key2)))) plaintext) = plaintext)  ∧
  ((FST(FullDES (SND(semi_key2)))) ((FST(FullDES (FST(semi_key2)))) plaintext) = plaintext)
Proof
     rw[DES_def]
  >- (Know ‘LENGTH ((KS (SND semi_key2) 16))=16’
      >- rw [LENGTH_KS] \\ 
      Suff ‘KS (FST semi_key2) 16 =REVERSE (KS (SND semi_key2) 16)’
      >- rw [desCore_CORRECT] \\
      EVAL_TAC)
  >> Know ‘LENGTH ((KS (FST semi_key2) 16))=16’
  >- rw [LENGTH_KS] 
  >> Suff ‘KS (SND semi_key2) 16 =REVERSE (KS (FST semi_key2) 16)’
  >- rw [desCore_CORRECT]
  >> EVAL_TAC
QED

Theorem semiK_proper3:
  !plaintext. ((FST(FullDES (FST(semi_key3)))) ((FST(FullDES (SND(semi_key3)))) plaintext) = plaintext)  ∧
  ((FST(FullDES (SND(semi_key3)))) ((FST(FullDES (FST(semi_key3)))) plaintext) = plaintext)
Proof
     rw[DES_def]
  >- (Know ‘LENGTH ((KS (SND semi_key3) 16))=16’
      >- rw [LENGTH_KS] \\ 
      Suff ‘KS (FST semi_key3) 16 =REVERSE (KS (SND semi_key3) 16)’
      >- rw [desCore_CORRECT] \\
      EVAL_TAC)
  >> Know ‘LENGTH ((KS (FST semi_key3) 16))=16’
  >- rw [LENGTH_KS] 
  >> Suff ‘KS (SND semi_key3) 16 =REVERSE (KS (FST semi_key3) 16)’
  >- rw [desCore_CORRECT]
  >> EVAL_TAC
QED

Theorem semiK_proper4:
  !plaintext. ((FST(FullDES (FST(semi_key4)))) ((FST(FullDES (SND(semi_key4)))) plaintext) = plaintext)  ∧
  ((FST(FullDES (SND(semi_key4)))) ((FST(FullDES (FST(semi_key4)))) plaintext) = plaintext)
Proof
     rw[DES_def]
  >- (Know ‘LENGTH ((KS (SND semi_key4) 16))=16’
      >- rw [LENGTH_KS] \\ 
      Suff ‘KS (FST semi_key4) 16 =REVERSE (KS (SND semi_key4) 16)’
      >- rw [desCore_CORRECT] \\
      EVAL_TAC)
  >> Know ‘LENGTH ((KS (FST semi_key4) 16))=16’
  >- rw [LENGTH_KS] 
  >> Suff ‘KS (SND semi_key4) 16 =REVERSE (KS (FST semi_key4) 16)’
  >- rw [desCore_CORRECT]
  >> EVAL_TAC
QED

Theorem semiK_proper5:
  !plaintext. ((FST(FullDES (FST(semi_key5)))) ((FST(FullDES (SND(semi_key5)))) plaintext) = plaintext)  ∧
  ((FST(FullDES (SND(semi_key5)))) ((FST(FullDES (FST(semi_key5)))) plaintext) = plaintext)
Proof
     rw[DES_def]
  >- (Know ‘LENGTH ((KS (SND semi_key5) 16))=16’
      >- rw [LENGTH_KS] \\ 
      Suff ‘KS (FST semi_key5) 16 =REVERSE (KS (SND semi_key5) 16)’
      >- rw [desCore_CORRECT] \\
      EVAL_TAC)
  >> Know ‘LENGTH ((KS (FST semi_key5) 16))=16’
  >- rw [LENGTH_KS] 
  >> Suff ‘KS (SND semi_key5) 16 =REVERSE (KS (FST semi_key5) 16)’
  >- rw [desCore_CORRECT]
  >> EVAL_TAC
QED

Theorem semiK_proper6:
  !plaintext. ((FST(FullDES (FST(semi_key6)))) ((FST(FullDES (SND(semi_key6)))) plaintext) = plaintext)  ∧
  ((FST(FullDES (SND(semi_key6)))) ((FST(FullDES (FST(semi_key6)))) plaintext) = plaintext)
Proof
     rw[DES_def]
  >- (Know ‘LENGTH ((KS (SND semi_key6) 16))=16’
      >- rw [LENGTH_KS] \\ 
      Suff ‘KS (FST semi_key6) 16 =REVERSE (KS (SND semi_key6) 16)’
      >- rw [desCore_CORRECT] \\
      EVAL_TAC)
  >> Know ‘LENGTH ((KS (FST semi_key6) 16))=16’
  >- rw [LENGTH_KS] 
  >> Suff ‘KS (SND semi_key6) 16 =REVERSE (KS (FST semi_key6) 16)’
  >- rw [desCore_CORRECT]
  >> EVAL_TAC
QED        


