(* Rocksalt assembly program *)
(* Author        : PLDI-authors *)
(* Date Created  : 10-28-2017 *)

Require Import Integers AST.
Require Import X86Model.Encode.
Require Import X86Model.X86Syntax.
Require Import Errors.
Require Import String.

Definition instr_to_string (i: instr) : string :=
  match i with
  (* two parts:  1-byte opcode instructions, followed by 2-byte in alphabetical order,
   following Table B-13 *) 
  | AAA => "AAA"
  | AAD => "AAD"
  | AAM => "AAM"
  | AAS => "AAS"
  (* w is the width bit; 
   with no operand override prefix, 
     when w is true, then it's a 32-bit operation;
     when w is false, then it's a 8-bit operation;
   with an operand override prefix,
     when w is true, it's a 16-bit operation;
     when w is false, it's a 8-bit operation;
   See load_op/set-op in X86Semantics.v *)
  | ADC _ _ _  => "ADC"
  | ADD _ _ _ => "ADD"
  | AND _ _ _ => "AND"
  | ARPL _ _ => "ARPL"
  | BOUND _ _ => "BOUND"
  | BSF  _ _ => "BSF"
  | BSR  _ _ => "BSR"
  | BSWAP _ => "BSWAP"
  | BT  _ _ => "BT"
  | BTC _ _ => "BTC"
  | BTR _ _ => "BTR"
  | BTS _ _ => "BTS"
  | CALL _ _ _ _ => "CALL"
  | CDQ => "CDQ"
  | CLC => "CLC"
  | CLD => "CLD"
  | CLI => "CLI"
  | CLTS => "CLTS"
  | CMC => "CMC"
  | CMOVcc _ _ _ => "CMOVcc"
  | CMP  _ _ _ => "CMP"
  | CMPS  _ => "CMPS"
  | CMPXCHG _ _ _ => "CMPXCNG"
  | CPUID  => "CPUID"
  | CWDE   => "CWDE"
  | DAA    => "DAA"
  | DAS    => "DAS"
  | DEC _ _ => "DEC"
  | DIV _ _ => "DIV"

  (*Floating-point syntax defined starting here. Table B-38 explains how to read instructions and B-39 has the
actual instruction details. Instructions can be found here: 
http://download.intel.com/products/processor/manual/325383.pdf*)
  | F2XM1 => "F2XM1"
  | FABS => "FABS"
  (* zerod is true iff st(0) is the destination; 
   op1 is the destination when zerod=false *)
  | FADD _ _ => "FADD"
  | FADDP _ => "FADDP"
  | FBLD _ => "FBLD"
  | FBSTP _ => "FBSTP"
  | FCHS => "FCHS"
  (* FCLEX is the same as FWAIT followed FNCLEX
   | FCLEX : instr *)
  | FCMOVcc _ _ => "FCMOVcc"
  | FCOM _ => "FCOM"
  | FCOMP _ => "FCOMP"
  | FCOMPP => "FCOMPP"
  | FCOMIP _ => "FCOMIP"
  | FCOS => "FCOS"
  | FDECSTP => "FDECSTP"
  | FDIV _ _ => "FDIV"
  | FDIVP _ => "FDIVP"
  | FDIVR _ _ => "FDIVR"
  | FDIVRP _ => "FDIVP"
  | FFREE _ => "FFREE"
  | FIADD _ => "FIADD"
  | FICOM _ => "FICOM"
  | FICOMP _ => "FICOMP"
  | FIDIV _ => "FIDIV"
  | FIDIVR _ => "FIDIVR"
  | FILD _ => "FILD"
  | FIMUL _ => "FIMUL"
  | FINCSTP => "FINCSTP"
  (* FINIT is FWAIT followed by FNINIT;
   | FINIT : instr *)
  | FIST _ => "FIST"
  | FISTP _ => "FISTP"
  | FISUB _ => "FISUB"
  | FISUBR _ => "FISUBR"
  | FLD _ => "FLD"
  | FLD1 => "FLD1"
  | FLDCW _ => "FLDCW"
  | FLDENV _ => "FLDENV"
  | FLDL2E => "FLDL2E"
  | FLDL2T => "FLDL2T"
  | FLDLG2 => "FLDLG2"
  | FLDLN2 => "FLDN2"
  | FLDPI => "FLDPI"
  | FLDZ => "FLDZ"
  | FMUL _ _ => "FMUL"
  | FMULP _ => "FMULP"
  | FNCLEX => "FNCLEX"
  | FNINIT => "FNINIT"
  | FNOP => "FNOP"
  | FNSAVE _ => "FNSAVE"
  | FNSTCW _ => "FNSTCW"
  (* FNSTSW None means that storing the status word to AX *)
  | FNSTSW _ => "FNSTSW"
  | FPATAN => "FPATAN"
  | FPREM => "FPREM"
  | FPREM1 => "FPREM1"
  | FPTAN => "FPTAN"
  | FRNDINT => "FRNDINT"
  | FRSTOR _ => "FRSTOR"
  (* FSAVE's encoding the same as FWAIT followed FNSAVE
   | FSAVE : forall (op1: fp_operand), instr *)
  | FSCALE => "FSCALE"
  | FSIN => "FSIN"
  | FSINCOS => "FSINCOS"
  | FSQRT => "FSQRT"
  | FST _ => "FST"

  (* FSTCW's is the same as FWAIT followed by FNSTCW
   | FSTCW : forall (op1: fp_operand), instr *)

  | FSTENV _ => "FSTENV"
  | FSTP _ => "FSTP"

  (* FSTSW is the same as FWAIT followed by FNSTSW 
   | FSTSW : forall (op1: option fp_operand), instr *)

  (* st(0) <- st(0) - op, when zerod is true;
   op <- op - st(0), when zerod is false and op can only be st(i) *)
  | FSUB _ _ => "FSUB"
  | FSUBP _ => "FSUBP"
  (* reverse subtraction
   st(0) <- op - st(0), when zerod is true;
   op <- st(0) - op, when zerod is false and op can only be st(i) *)
  | FSUBR _ _ => "FSUBR"
  | FSUBRP _ => "FSUBRP"
  | FTST => "FTST"
  | FUCOM _ => "FUCOM"
  | FUCOMP _ => "FUCOMP"
  | FUCOMPP => "FUCOMPP"
  | FUCOMI _ => "FUCOMI"
  | FUCOMIP _ => "FUCOMIP"
  | FXAM => "FXAM"
  | FXCH _ => "FXCH"
  | FXTRACT => "FXTRACT"
  | FYL2X => "FYL2X"
  | FYL2XP1 => "FYL2XP1"
  | FWAIT => "FWAIT"
  (*Floating-Point syntax ends here for now*)
  (*MMX syntax starting here (from table B.5.3) *)
  | EMMS => "EMMS"
  | MOVD _ _ => "MOVD"
  | MOVQ _ _ => "MOVQ"
  | PACKSSDW _ _ => "PACKSSDW"
  | PACKSSWB _ _ => "PACKSSWB" 
  | PACKUSWB _ _ => "PACKUSWB"
  | PADD _ _ _ => "PADD"
  | PADDS _ _ _ => "PADDS"
  | PADDUS _ _ _ => "PADDUS"
  | PAND _ _ => "PAND"
  | PANDN _ _ => "PANDN"
  | PCMPEQ _ _ _ => "PCMPEQ"
  | PCMPGT _ _ _ => "PCMPGT"
  | PMADDWD _ _ => "PMADDWD"
  | PMULHUW _ _ => "PMULHUW"
  | PMULHW _ _ => "PMULHW"
  | PMULLW _ _ => "PMULLW"
  | POR _ _ => "POR" 
  | PSLL _ _ _ => "PSLL"
  | PSRA _ _ _ => "PSRA"
  | PSRL _ _ _ => "PSRL"
  | PSUB _ _ _ => "PSUB"
  | PSUBS _ _ _ => "PSUBS"
  | PSUBUS _ _ _ => "PSUBUS"
  | PUNPCKH _ _ _  => "PUNPCKH"
  | PUNPCKL _ _ _ => "PUNPCKL"
  | PXOR _ _ => "PXOR"
  (*End of MMX syntax *)

  (*SSE Syntax (Table B.8 in manual) *)
  | ADDPS _ _ => "ADDPS"
  | ADDSS _ _ => "ADDSS"
  | ANDNPS _ _ => "ANDNPS"
  | ANDPS _ _ => "ANDPS"
  | CMPPS _ _ _ => "CMPPS"
  | CMPSS _ _ _ => "CMPSS"
  | COMISS _ _ => "COMISS"
  | CVTPI2PS _ _ => "CVTPI2PS"
  | CVTPS2PI _ _ => "CVTPS2PI"
  | CVTSI2SS _ _ => "CVTSI2SS"
  | CVTSS2SI _ _ => "CVTSS2SI"
  | CVTTPS2PI _ _ => "CVTTPS2PI"
  | CVTTSS2SI _ _ => "CVTTSS2SI"
  | DIVPS _ _ => "DIVPS"
  | DIVSS _ _ => "DIVSS"
  | LDMXCSR _ => "LDMXCSR"
  | MAXPS _ _ => "MAXPS"
  | MAXSS _ _ => "MAXSS"
  | MINPS _ _ => "MINPS"
  | MINSS _ _ => "MINSS"
  | MOVAPS _ _ => "MOVAPS"
  | MOVHLPS _ _ => "MOVHLPS"
  | MOVHPS _ _ => "MOVHPS"
  | MOVLHPS _ _ => "MOVLHPS"
  | MOVLPS _ _ => "MOVLPS"
  | MOVMSKPS _ _ => "MOVMSKPS"
  | MOVSS _ _ => "MOVSS"
  | MOVUPS _ _ => "MOVUPS"
  | MULPS _ _ => "MULPS"
  | MULSS _ _ => "MULSS"
  | ORPS _ _ => "ORPS"
  | RCPPS _ _ => "RCPPS"
  | RCPSS _ _ => "RCPSS"
  | RSQRTPS _ _ => "RSQRTPS"
  | RSQRTSS _ _ => "RSQRTSS"
  | SHUFPS _ _ _ => "SHUFPS"
  | SQRTPS _ _ => "SQRTPS"
  | SQRTSS _ _ => "SQRTSS"
  | STMXCSR _ => "STMXCSR"
  | SUBPS _ _ => "SUBPS"
  | SUBSS _ _ => "SUBSS"
  | UCOMISS _ _ => "UCOMISS"
  | UNPCKHPS _ _ => "UNPCKHPS"
  | UNPCKLPS _ _ => "UNPCKLPS"
  | XORPS _ _ => "XORPS" 
  | PAVGB _ _ => "PAVGB"
  | PEXTRW _ _ _ => "PEXTRW"
  | PINSRW _ _ _ => "PINSRW"
  | PMAXSW _ _ => "PMAXSW"
  | PMAXUB _ _ => "PMAXUB"
  | PMINSW _ _ => "PMINSW"
  | PMINUB _ _ => "PMINUB"
  | PMOVMSKB _ _ => "PMOVMSKB"
  (*| PMULHUW : forall (op1 op2: sse_operand), instr *)
  | PSADBW _ _ => "PSADBW"
  | PSHUFW _ _ _ => "PSHUFW"
  | MASKMOVQ _ _ => "MASKMOVQ"
  | MOVNTPS _ _ => "MOVNTPS"
  | MOVNTQ _ _ => "MOVNTQ"
  | PREFETCHT0 _ => "PREFETCHT0"
  | PREFETCHT1 _ => "PREFETCHT1"
  | PREFETCHT2 _ => "PREFETCHT2"
  | PREFETCHNTA _ => "PREFETCHNTA"
  | SFENCE => "SFENCE" 
  (*end SSE, start SSE2 *)

  (*End of SSE Syntax *)
  | HLT => "HLT"  
  | IDIV _ _ => "IDIV"
  (* This one is kind of funny -- there are three cases:
   one operand, two operand, and three operand. The one operand
   form is precise and implicitly uses EAX; the other two variants
   can potentially lose some data due to overflow. *)
  | IMUL _ _ _ _ => "IMUL"
  | IN _ _ => "IN"  
  | INC _ _ => "INC"
  | INS _ => "INS"
  | INTn _ => "INTn"
  | INT  => "INT"
  | INTO  => "INTO"
  | INVD  => "INVD"
  | INVLPG _ => "INVLPG"
  | IRET   => "IRET"
  | Jcc   _ _ => "Jcc"
  | JCXZ  _ => "JCXZ"
  | JMP   _ _ _ _ => "JMP"
  | LAHF => "LAHF"
  | LAR  _ _ => "LAR"
  | LDS  _ _ => "LDS"
  | LEA  _ _ => "LEA"
  | LEAVE => "LEAVE"
  | LES _ _ => "LES"
  | LFS _ _ => "LFS" 
  | LGDT _ => "LGDT"
  | LGS _ _ => "LGS"
  | LIDT _ => "LIDT"
  | LLDT _ => "LLDT"
  | LMSW _ => "LMSW"
  | LODS _ => "LODS"
  | LOOP _ => "LOOP"
  | LOOPZ _ => "LOOPZ"
  | LOOPNZ _ => "LOOPNZ"
  | LSL _ _ => "LSL"
  | LSS _ _ => "LSS"
  | LTR _ => "LTR"
  | MOV _ _ _ => "MOV"
  (* Note:  when direction is true, we move the first operand to the second.  
   * When the direction is false, we move the second operand to the first. *)
  | MOVCR _ _ _ => "MOVCR"
  | MOVDR _ _ _ => "MOVDR"
  | MOVSR _ _ _ => "MOVSR"
  | MOVBE _ _ => "MOVBE"
  | MOVS _ => "MOVS"
  | MOVSX _ _ _ => "MOVSX"
  | MOVZX _ _ _ => "MOVZX"
  | MUL _ _ => "MUL"
  | NEG _ _ => "NEG"
  | NOP _ => "NOP"
  | NOT _ _ => "NOT"
  | OR _ _ _ => "OR"
  | OUT _ _ => "OUT" 
  | OUTS _ => "OUTS"
  | POP _ => "POP"  
  | POPSR _ => "POPSR"
  | POPA => "POPA" 
  | POPF => "POPF"
  | PUSH _ _ => "PUSH"
  | PUSHSR _ => "PUSHSR"
  | PUSHA => "PUSHA"
  | PUSHF => "PUSHF"
  | RCL _ _ _ => "RCL"
  | RCR _ _ _ => "RCR"
  | RDMSR => "RDMSR"
  | RDPMC => "RDPMC"
  | RDTSC => "RDTSC"
  | RDTSCP => "RDTSCP"
  | RET _ _ => "RET"
  | ROL _ _ _ => "ROL"
  | ROR _ _ _ => "ROR"
  | RSM => "RSM"
  | SAHF => "SAHF"
  | SAR _ _ _ => "SAR"
  | SBB _ _ _ => "SBB"
  | SCAS _ => "SCAS"
  | SETcc _ _ => "SETcc"
  | SGDT _ => "SGDT"
  | SHL _ _ _ => "SHL"
  | SHLD _ _ _ => "SHLD"
  | SHR _ _ _ => "SHR"
  | SHRD _ _ _ => "SHRD"
  | SIDT _ => "SIDT"
  | SLDT _ => "SLDT"
  | SMSW _ => "SMSW"
  | STC => "STC"
  | STD => "STD"
  | STI => "STI"
  | STOS _ => "STOS"
  | STR _ => "STR"   
  | SUB _ _ _ => "SUB"
  | TEST _ _ _ => "TEST"
  | UD2 => "UD2"
  | VERR _ => "VERR"
  | VERW _ => "VERW"
  (* | WAIT  removed because it's the same as FWAIT*)
  | WBINVD => "WBINVD"
  | WRMSR => "WRMSR"
  | XADD _ _ _ => "XADD"
  | XCHG _ _ _ => "XCHG"
  | XLAT => "XLAT"
  | XOR _ _ _ => "XOR"
  end.

(* Segments *)
(* Record segment := mkSegment { *)
(*   seg_offset : int32;  (* offset to the segment in memory*) *)
(*   seg_size : int32; (* size of the segment *)   *)
(* }. *)

Definition ACCUM_LIST (A:Type) := int32 -> list A.

Definition ACCUM_INSTRS := ACCUM_LIST instr.
Definition ACCUM_DATA   := ACCUM_LIST int8.

Definition app_accum_list {A:Type} (l1 l2 : ACCUM_LIST A) :=
  fun data_addr => (l1 data_addr) ++ (l2 data_addr).

Fixpoint flat_map_accum_list {A B:Type} (f: A -> ACCUM_LIST B) (l: list A) : ACCUM_LIST B :=
  match l with 
  | nil => fun data_addr => nil
  | h::t => app_accum_list (f h) (flat_map_accum_list f t)
  end.
  

(* Information of global variables *)
Record gv_info := mkInfo {
  gv_offset : int32;  (* offset to the global variable in the data segment*)
  gv_size : int32 (* size of the global variable *)
}.

(* Information of functions *)
Record function := mkFun {
  fun_offset : int32; (* offset to the function in the text segment*)
  fun_size   : int32; (* size of the function *)
}.

Definition fundef := AST.fundef function.

(* Program *)
Record program := mkProg {
  prog_defs: list (ident * option (globdef fundef gv_info));
  prog_public: list ident;
  prog_main: ident;
  (* Instructions in the text segment. 
     They are parameterized by the starting offset to the data segment *)
  text_instrs : ACCUM_INSTRS;
  (* Initial data for the data segment.
     They are parameterized by the starting offset to the data segment *)
  init_data : ACCUM_DATA;
  (* The offset to the main function in the text segment *)
  main_ofs  : int32;
}.

Definition program_of_program (p: program) : AST.program fundef gv_info :=
  {| AST.prog_defs := p.(prog_defs);
     AST.prog_public := p.(prog_public);
     AST.prog_main := p.(prog_main) |}.

Coercion program_of_program: program >-> AST.program.