Definition ready_for_proof (i: instruction) : bool :=
  match i with
  | Pjmp_l_rel jofs => true
  | Pjcc_rel c jofs => true
  | Pcall (inr id) _ => true
  | Pleal rd a => true
  | Pxorl_r rd => true
  | Paddl_ri rd n => true
  | Psubl_ri rd n => true
  | Psubl_rr rd r1 => true
  | Pmovl_ri rd n => true
  | Pmov_rr rd r1 => true
  | Pmovl_rm rd a => true
  | Pmovl_mr a rs => true
  | Pmov_rm_a rd a => true
  | Pmov_mr_a a rs => true
  | Pmov_rs rd id => true
  | Ptestl_rr r1 r2 => true
  | Pret => true
  | Pimull_rr rd r1 => true
  | Pimull_ri rd n => true
  | Pcmpl_rr r1 r2 => true
  | Pcmpl_ri r1 n => true
  | Pcltd => true
  | Pidivl r1 => true
  | Psall_ri rd n => true
  | Plabel _ true
  | Pnop => true
  | _ => false
  end.




(** Encode a single instruction *)
Definition encode_instr (ofs:Z) (i: instruction) : res (list byte) :=
  match i with
  | Pjmp_l_rel jofs =>
    OK (HB["E9"] :: encode_int32 jofs)
  | Pjcc_rel c jofs =>
    let cbytes := encode_testcond c in
    OK (cbytes ++ encode_int32 jofs)
  | Pcall (inr id) _ =>
    do addend <- get_instr_reloc_addend ofs i;
    OK (HB["E8"] :: encode_int32 addend)
  | Pleal rd a =>
    do abytes <- encode_addrmode ofs i a rd;
    OK (HB["8D"] :: abytes)
  | Pxorl_r rd =>
    do rdbits <- encode_ireg rd;
    let modrm := bB[ b["11"] ++ rdbits ++ rdbits ] in
    OK (HB["31"] :: modrm :: nil)
  | Paddl_ri rd n =>
    do rdbits <- encode_ireg rd;
    let modrm := bB[ b["11"] ++ b["000"] ++ rdbits ] in
    let nbytes := encode_int32 (Int.unsigned n) in
    OK (HB["81"] :: modrm :: nbytes)
  | Psubl_ri rd n =>
    do rdbits <- encode_ireg rd;
    let modrm := bB[ b["11"] ++ b["101"] ++ rdbits ] in
    let nbytes := encode_int32 (Int.unsigned n) in
    OK (HB["81"] :: modrm :: nbytes)
  | Psubl_rr rd r1 =>
    do rdbits <- encode_ireg rd;
    do r1bits <- encode_ireg r1;
    let modrm := bB[ b["11"] ++ rdbits ++ r1bits ] in
    OK (HB["2B"] :: modrm :: nil)
  | Pmovl_ri rd n =>
    do rdbits <- encode_ireg rd;
    let opcode := bB[b["10111"] ++ rdbits] in
    let nbytes := encode_int32 (Int.unsigned n) in
    OK (opcode :: nbytes)
  | Pmov_rr rd r1 =>
    do rdbits <- encode_ireg rd;
    do r1bits <- encode_ireg r1;
    let modrm := bB[ b["11"] ++ rdbits ++ r1bits] in
    OK (HB["8B"] :: modrm :: nil)
  | Pmovl_rm rd a =>
    do abytes <- encode_addrmode ofs i a rd;
    OK (HB["8B"] :: abytes)
  | Pmovl_mr a rs =>
    do abytes <- encode_addrmode ofs i a rs;
    OK (HB["89"] :: abytes)
  | Pmov_rm_a rd a =>
    do abytes <- encode_addrmode ofs i a rd;
    OK (HB["8B"] :: abytes)    
  | Pmov_mr_a a rs =>
    do abytes <- encode_addrmode ofs i a rs;
    OK (HB["89"] :: abytes)
  | Pmov_rs rd id =>
    do abytes <- encode_addrmode ofs i (Addrmode None None (inr (id,Ptrofs.zero))) rd;
    OK (HB["8B"] :: abytes)  
  | Ptestl_rr r1 r2 =>
    do r1bits <- encode_ireg r1;
    do r2bits <- encode_ireg r2;
    let modrm := bB[ b["11"] ++ r2bits ++ r1bits ] in
    OK (HB["85"] :: modrm :: nil)
  | Pret =>
    OK (HB["C3"] :: nil)
  | Pimull_rr rd r1 =>
    do rdbits <- encode_ireg rd;
    do r1bits <- encode_ireg r1;
    let modrm := bB[ b["11"] ++ rdbits ++ r1bits ] in
    OK (HB["0F"] :: HB["AF"] :: modrm :: nil)
  | Pimull_ri rd n =>
    do rdbits <- encode_ireg rd;
    let modrm := bB[ b["11"] ++ rdbits ++ rdbits ] in
    let nbytes := encode_int32 (Int.unsigned n) in
    OK (HB["69"] :: modrm :: nbytes)
  | Pcmpl_rr r1 r2 =>
    do r1bits <- encode_ireg r1;
    do r2bits <- encode_ireg r2;
    let modrm := bB[ b["11"] ++ r2bits ++ r1bits ] in
    OK (HB["39"] :: modrm :: nil)
  | Pcmpl_ri r1 n =>
    do r1bits <- encode_ireg r1;
    let modrm := bB[ b["11"] ++ b["111"] ++ r1bits ] in
    let nbytes := encode_int32 (Int.unsigned n) in
    OK (HB["81"] :: modrm :: nbytes)
  | Pcltd =>
    OK (HB["99"] :: nil)
  | Pidivl r1 =>
    do r1bits <- encode_ireg r1;
    let modrm := bB[ b["11"] ++ b["110"] ++ r1bits ] in
    OK (HB["F7"] :: modrm :: nil)
  | Psall_ri rd n =>
    do rdbits <- encode_ireg rd;
    let modrm := bB[ b["11"] ++ b["100"] ++ rdbits ] in
    let nbytes := [Byte.repr (Int.unsigned n)] in
    OK (HB["C1"] :: modrm :: nbytes)
  | Plabel _
  | Pnop =>
    OK (HB["90"] :: nil)
  | _ =>
    Error [MSG "Encoding of the instruction is not supported yet: ";
           MSG (instr_to_string i)]
  end.
