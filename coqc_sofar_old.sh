#!/bin/bash

COMMON=(
       #Common
       Errors.v
       AST_old.v 
       Values_old.v
       Linking_old.v
       MemPerm.v
       Memdata_old.v
       Assoc_old.v
       StackADT_old.v
       Memtype_old.v
       Memory_old.v
       Globalenvs_old.v
       Events_old.v
       StackInj_old.v
       Smallstep_old.v
       Behaviors_old.v
       Switch_old.v
       Determinism_old.v
       Unityping_old.v
       Separation_old.v
       )

BACKEND=(
	#Backend
	./backend/Cminor_old.v
	./x86/Op_old.v
	./backend/CminorSel_old.v
	./x86/SelectOp_old.v
	./backend/SplitLong_old.v
	./x86/SelectLong_old.v
	./backend/SelectDiv_old.v
	./x86/Machregs_old.v
	./backend/Selection_old.v
	./x86/SelectOpproof_old.v
	./backend/SplitLongproof_old.v
	./x86/SelectLongproof_old.v
	./backend/SelectDivproof_old.v
	./backend/Selectionproof_old.v
	./backend/Registers_old.v
	./backend/RTL_old.v
	./backend/RTLgen_old.v
	./backend/RTLgenspec_old.v
	./backend/RTLgenproof_old.v
	./backend/Locations_old.v
	./x86/Conventions1_old.v
	./backend/Conventions_old.v
	./backend/Tailcall_old.v
	./backend/Tailcallproof_old.v
	./backend/Inlining_old.v
	./backend/Inliningspec_old.v
	./backend/Inliningproof_old.v
	./backend/Renumber_old.v
	./backend/Renumberproof_old.v
	./backend/RTLtyping_old.v
	./backend/Kildall_old.v
	./backend/Liveness_old.v
	./backend/ValueDomain_old.v
	./x86/ValueAOp_old.v
	./backend/ValueAnalysis_old.v
	./x86/ConstpropOp_old.v
	./backend/Constprop_old.v
	./x86/ConstpropOpproof_old.v
	./backend/Constpropproof_old.v
	./backend/CSEdomain_old.v
	./x86/CombineOp_old.v
	./backend/CSE_old.v
	./x86/CombineOpproof_old.v
	./backend/CSEproof_old.v
	./backend/NeedDomain_old.v
	./x86/NeedOp_old.v
	./backend/Deadcode_old.v
	./backend/Deadcodeproof_old.v
	./backend/Unusedglob_old.v
	./backend/Unusedglobproof_old.v
	./backend/LTL_old.v
	./backend/Allocation_old.v
	./backend/Allocproof_old.v
	./backend/Tunneling_old.v
	./backend/Tunnelingproof_old.v
	./backend/Linear_old.v
	./backend/Linearize_old.v
	./backend/Linearizeproof_old.v
	./backend/CleanupLabels_old.v
	./backend/CleanupLabelsproof_old.v
	./backend/Debugvar_old.v
	./backend/Debugvarproof_old.v
	./backend/Bounds_old.v
	./x86/Stacklayout_old.v
	./backend/Mach_old.v
	./backend/Lineartyping_old.v
	./backend/Stacking_old.v
	./backend/Stackingproof_old.v
	./backend/Mach2Mach2_old.v
	./x86/Asm_old.v
	./x86/Asmgen_old.v
	./backend/Asmgenproof0_old.v
	./x86/Asmgenproof1_old.v
	./x86/Asmgenproof_old.v
	)

FRONTEND=(
        #Frontend
        Ctypes_old.v
        Cop_old.v
        Csyntax_old.v
        Csem_old.v
        Ctyping_old.v
        Cstrategy_old.v
        Cexec_old.v
        #Cexecimpl.v
        Initializers_old.v
        Initializersproof_old.v
        Clight_old.v
        ClightBigstep_old.v
        SimplExpr_old.v
        SimplExprspec_old.v
        SimplExprproof_old.v
        SimplLocals_old.v
        SimplLocalsproof_old.v
        Csharpminor_old.v
        Cshmgen_old.v
        Cshmgenproof_old.v
        Cminorgen_old.v
        Cminorgenproof_old.v
        )
       
COQC="coqc -R flocq compcert.flocq -R lib compcert.lib -R x86_32 compcert.x86_32 -R x86 compcert.x86 -R Common compcert.common -R cfrontend compcert.cfrontend -R driver compcert.driver -R backend compcert.backend"

for i in "${COMMON[@]}"; do
    echo "$i"
    $COQC "./common/$i"
done

for i in "${BACKEND[@]}"; do
    echo "$i"
    $COQC "$i"
done

for i in "${FRONTEND[@]}"; do
    echo "$i"
    $COQC "./cfrontend/$i"
done