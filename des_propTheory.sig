signature des_propTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val AllpairXor_def : thm
    val Semiwkey_def : thm
    val Wkey1_def : thm
    val Wkey2_def : thm
    val Wkey3_def : thm
    val Wkey4_def : thm
    val Wkey_def : thm
    val Wtext_def : thm
    val Wtextlist_def : thm
    val non_weak_keys_def : thm
    val roundk_L : thm
    val roundk_R : thm
    val roundk_supp : thm
    val trans1_def : thm
    val trans2_def : thm
    val w1trans1_def : thm
    val w1trans2_def : thm
    val w2trans1_def : thm
    val w2trans2_def : thm
    val w3trans1_def : thm
    val w3trans2_def : thm
    val w4trans1_def : thm
    val w4trans2_def : thm
    val wtrans1_def : thm
  
  (*  Theorems  *)
    val BIJ_XORL : thm
    val BIJ_for_weak_keys : thm
    val BIJ_for_weak_keys_explicit : thm
    val BIJ_wtext1 : thm
    val BIJ_wtext2 : thm
    val BIJ_wtext3 : thm
    val BIJ_wtext4 : thm
    val DES_fp_non_weak_keys : thm
    val Wtext1_def : thm
    val Wtext2_def : thm
    val Wtext3_def : thm
    val Wtext4_def : thm
    val compl_E : thm
    val compl_IIP : thm
    val compl_IP : thm
    val compl_RK_L : thm
    val compl_RK_R : thm
    val compl_extract_1 : thm
    val compl_extract_2 : thm
    val compl_join : thm
    val comple_PC2 : thm
    val comple_property : thm
    val convert_RK : thm
    val roundk_L_compute : thm
    val roundk_R_compute : thm
    val semiK_proper1 : thm
    val semiK_proper2 : thm
    val text_num : thm
    val weakK1_proper2 : thm
    val weakK2_proper2 : thm
    val weakK3_proper2 : thm
    val weakK4_proper2 : thm
    val weakK_proper : thm
    val weakK_sup : thm
    val wkey1_equal : thm
    val xor_E : thm
    val xor_P : thm
    val xor_S1 : thm
  
  val des_prop_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [des] Parent theory of "des_prop"
   
   [AllpairXor_def]  Definition
      
      ⊢ ∀X. AllpairXor X = {(x1,x2) | x1 ⊕ x2 = X}
   
   [Semiwkey_def]  Definition
      
      ⊢ Semiwkey =
        [(0x1FE01FE01FE01FEw,0xFE01FE01FE01FE01w);
         (0x1FE01FE00EF10EF1w,0xE01FE01FF10EF10Ew);
         (0x1E001E001F101F1w,0xE001E001F101F101w);
         (0x1FFE1FFE0EFE0EFEw,0xFE1FFE1FFE0EFE0Ew);
         (0x11F011F010E010Ew,0x1F011F010E010E01w);
         (0xE0FEE0FEF1FEF1FEw,0xFEE0FEE0FEF1FEF1w)]
   
   [Wkey1_def]  Definition
      
      ⊢ Wkey1 = 0x101010101010101w
   
   [Wkey2_def]  Definition
      
      ⊢ Wkey2 = 0xFEFEFEFEFEFEFEFEw
   
   [Wkey3_def]  Definition
      
      ⊢ Wkey3 = 0xE0E0E0E0F1F1F1F1w
   
   [Wkey4_def]  Definition
      
      ⊢ Wkey4 = 0x1F1F1F1F0E0E0E0Ew
   
   [Wkey_def]  Definition
      
      ⊢ Wkey =
        [0x101010101010101w; 0xFEFEFEFEFEFEFEFEw; 0xE0E0E0E0F1F1F1F1w;
         0x1F1F1F1F0E0E0E0Ew]
   
   [Wtext_def]  Definition
      
      ⊢ ∀key.
          Wtext key = {x | ∃w. Split (IP (desCore 8 (KS key 8) x)) = (w,w)}
   
   [Wtextlist_def]  Definition
      
      ⊢ Wtextlist = [Wtext1; Wtext2; Wtext3; Wtext4]
   
   [non_weak_keys_def]  Definition
      
      ⊢ non_weak_keys =
        [(0xB0B351C802C83DE0w,0x4739A2F04B7EAB28w);
         (0x5D460701328F2962w,0x9FE10D2E8C496143w);
         (0x4F4CAE37FD37C21Fw,0xB8C65D0FB48154D7w);
         (0xA2B9F8FECD70D69Dw,0x601EF2D173B69EBCw)]
   
   [roundk_L]  Definition
      
      ⊢ (∀k. RK_L 0 k = FST (PC1 k)) ∧
        ∀n k. RK_L (SUC n) k = (let c = RK_L n k; r = EL n R_data in c ⇆ r)
   
   [roundk_R]  Definition
      
      ⊢ (∀k. RK_R 0 k = SND (PC1 k)) ∧
        ∀n k. RK_R (SUC n) k = (let c = RK_R n k; r = EL n R_data in c ⇆ r)
   
   [roundk_supp]  Definition
      
      ⊢ ∀n k. RK n k = (RK_L n k,RK_R n k)
   
   [trans1_def]  Definition
      
      ⊢ ∀x1 x2. trans1 (x1,x2) = x1
   
   [trans2_def]  Definition
      
      ⊢ ∀x. trans2 x = (x,x)
   
   [w1trans1_def]  Definition
      
      ⊢ ∀x. w1trans1 x = FST (Split (IP (desCore 8 (KS Wkey1 8) x)))
   
   [w1trans2_def]  Definition
      
      ⊢ ∀x. w1trans2 x = desCore 8 (KS Wkey1 8) (IIP (Join (x,x)))
   
   [w2trans1_def]  Definition
      
      ⊢ ∀x. w2trans1 x = FST (Split (IP (desCore 8 (KS Wkey2 8) x)))
   
   [w2trans2_def]  Definition
      
      ⊢ ∀x. w2trans2 x = desCore 8 (KS Wkey2 8) (IIP (Join (x,x)))
   
   [w3trans1_def]  Definition
      
      ⊢ ∀x. w3trans1 x = FST (Split (IP (desCore 8 (KS Wkey3 8) x)))
   
   [w3trans2_def]  Definition
      
      ⊢ ∀x. w3trans2 x = desCore 8 (KS Wkey3 8) (IIP (Join (x,x)))
   
   [w4trans1_def]  Definition
      
      ⊢ ∀x. w4trans1 x = FST (Split (IP (desCore 8 (KS Wkey4 8) x)))
   
   [w4trans2_def]  Definition
      
      ⊢ ∀x. w4trans2 x = desCore 8 (KS Wkey4 8) (IIP (Join (x,x)))
   
   [wtrans1_def]  Definition
      
      ⊢ wtrans1 = [w1trans1; w2trans1; w3trans1; w4trans1]
   
   [BIJ_XORL]  Theorem
      
      ⊢ BIJ trans1 (AllpairXor 0w) 𝕌(:word6)
   
   [BIJ_for_weak_keys]  Theorem
      
      ⊢ ∀x. MEM x Wtextlist ⇒ ∃f. BIJ f x 𝕌(:word32)
   
   [BIJ_for_weak_keys_explicit]  Theorem
      
      ⊢ ∀i. i < 4 ⇒ BIJ (EL i wtrans1) (EL i Wtextlist) 𝕌(:word32)
   
   [BIJ_wtext1]  Theorem
      
      ⊢ BIJ w1trans1 Wtext1 𝕌(:word32)
   
   [BIJ_wtext2]  Theorem
      
      ⊢ BIJ w2trans1 Wtext2 𝕌(:word32)
   
   [BIJ_wtext3]  Theorem
      
      ⊢ BIJ w3trans1 Wtext3 𝕌(:word32)
   
   [BIJ_wtext4]  Theorem
      
      ⊢ BIJ w4trans1 Wtext4 𝕌(:word32)
   
   [DES_fp_non_weak_keys]  Theorem
      
      ⊢ ∀i. i < LENGTH non_weak_keys ⇒
            (let
               (key,plaintext) = EL i non_weak_keys;
               (encrypt,decrypt) = FullDES key
             in
               encrypt plaintext = plaintext)
   
   [Wtext1_def]  Theorem
      
      ⊢ Wtext1 = {x | ∃w. Split (IP (desCore 8 (KS Wkey1 8) x)) = (w,w)}
   
   [Wtext2_def]  Theorem
      
      ⊢ Wtext2 = {x | ∃w. Split (IP (desCore 8 (KS Wkey2 8) x)) = (w,w)}
   
   [Wtext3_def]  Theorem
      
      ⊢ Wtext3 = {x | ∃w. Split (IP (desCore 8 (KS Wkey3 8) x)) = (w,w)}
   
   [Wtext4_def]  Theorem
      
      ⊢ Wtext4 = {x | ∃w. Split (IP (desCore 8 (KS Wkey4 8) x)) = (w,w)}
   
   [compl_E]  Theorem
      
      ⊢ ∀m. E (¬m) = ¬E m
   
   [compl_IIP]  Theorem
      
      ⊢ ∀m. IIP (¬m) = ¬IIP m
   
   [compl_IP]  Theorem
      
      ⊢ ∀m. IP (¬m) = ¬IP m
   
   [compl_RK_L]  Theorem
      
      ⊢ ∀n k. 17 > n ⇒ RK_L n (¬k) = ¬RK_L n k
   
   [compl_RK_R]  Theorem
      
      ⊢ ∀n k. 17 > n ⇒ RK_R n (¬k) = ¬RK_R n k
   
   [compl_extract_1]  Theorem
      
      ⊢ ∀m. (63 >< 32) (¬m) = ¬(63 >< 32) m
   
   [compl_extract_2]  Theorem
      
      ⊢ ∀m. (31 >< 0) (¬m) = ¬(31 >< 0) m
   
   [compl_join]  Theorem
      
      ⊢ ∀m n. Join (¬m,¬n) = ¬Join (m,n)
   
   [comple_PC2]  Theorem
      
      ⊢ ∀a b. PC2 (¬a,¬b) = ¬PC2 (a,b)
   
   [comple_property]  Theorem
      
      ⊢ ∀k m n.
          0 < n ∧ n < 17 ∧ DES n k = (encrypt,decrypt) ∧
          DES n (¬k) = (encrypt',decrypt') ⇒
          ¬encrypt m = encrypt' (¬m)
   
   [convert_RK]  Theorem
      
      ⊢ ∀k n. RoundKey n k = REVERSE (GENLIST (λi. RK i k) (SUC n))
   
   [roundk_L_compute]  Theorem
      
      ⊢ (∀k. RK_L 0 k = FST (PC1 k)) ∧
        (∀n k.
           RK_L <..num comp'n..> k =
           (let
              c = RK_L (<..num comp'n..> − 1) k;
              r = EL (<..num comp'n..> − 1) R_data
            in
              c ⇆ r)) ∧
        ∀n k.
          RK_L <..num comp'n..> k =
          (let
             c = RK_L <..num comp'n..> k;
             r = EL <..num comp'n..> R_data
           in
             c ⇆ r)
   
   [roundk_R_compute]  Theorem
      
      ⊢ (∀k. RK_R 0 k = SND (PC1 k)) ∧
        (∀n k.
           RK_R <..num comp'n..> k =
           (let
              c = RK_R (<..num comp'n..> − 1) k;
              r = EL (<..num comp'n..> − 1) R_data
            in
              c ⇆ r)) ∧
        ∀n k.
          RK_R <..num comp'n..> k =
          (let
             c = RK_R <..num comp'n..> k;
             r = EL <..num comp'n..> R_data
           in
             c ⇆ r)
   
   [semiK_proper1]  Theorem
      
      ⊢ ∀plaintext pair.
          MEM pair Semiwkey ∧ pair = (s1,s2) ∧
          FullDES s1 = (encrypt,decrypt) ∧ FullDES s2 = (encrypt',decrypt') ⇒
          encrypt (encrypt' plaintext) = plaintext
   
   [semiK_proper2]  Theorem
      
      ⊢ ∀plaintext pair.
          MEM pair Semiwkey ∧ pair = (s1,s2) ∧
          FullDES s1 = (encrypt,decrypt) ∧ FullDES s2 = (encrypt',decrypt') ⇒
          encrypt' (encrypt plaintext) = plaintext
   
   [text_num]  Theorem
      
      ⊢ ∀x. MEM x Wtextlist ⇒ CARD x = CARD 𝕌(:word32)
   
   [weakK1_proper2]  Theorem
      
      ⊢ ∀x. x ∈ Wtext1 ∧ FullDES Wkey1 = (encrypt,decrypt) ⇒ encrypt x = x
   
   [weakK2_proper2]  Theorem
      
      ⊢ ∀x. x ∈ Wtext2 ∧ FullDES Wkey2 = (encrypt,decrypt) ⇒ encrypt x = x
   
   [weakK3_proper2]  Theorem
      
      ⊢ ∀x. x ∈ Wtext3 ∧ FullDES Wkey3 = (encrypt,decrypt) ⇒ encrypt x = x
   
   [weakK4_proper2]  Theorem
      
      ⊢ ∀x. x ∈ Wtext4 ∧ FullDES Wkey4 = (encrypt,decrypt) ⇒ encrypt x = x
   
   [weakK_proper]  Theorem
      
      ⊢ ∀k plaintext.
          MEM k Wkey ∧ FullDES k = (encrypt,decrypt) ⇒
          encrypt (encrypt plaintext) = plaintext
   
   [weakK_sup]  Theorem
      
      ⊢ ∀n k.
          MEM k Wkey ∧ 0 ≤ n ∧ n ≤ 8 ∧
          Split (IP (desCore 8 (KS k 8) x)) = (w,w) ⇒
          Round (8 − n) (KS k 16) (Split (IP x)) =
          Swap (Round (8 + n) (KS k 16) (Split (IP x)))
   
   [wkey1_equal]  Theorem
      
      ⊢ ∀x n k.
          MEM k Wkey ∧ n ≤ 8 ⇒
          Round n (KS k 8) (Split x) = Round n (KS k 16) (Split x)
   
   [xor_E]  Theorem
      
      ⊢ ∀x1 x2. E x1 ⊕ E x2 = E (x1 ⊕ x2)
   
   [xor_P]  Theorem
      
      ⊢ ∀x1 x2. P x1 ⊕ P x2 = P (x1 ⊕ x2)
   
   [xor_S1]  Theorem
      
      ⊢ ∃x1 x2. S1 x1 ⊕ S1 x2 ≠ S1 (x1 ⊕ x2)
   
   
*)
end
