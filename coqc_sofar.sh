#!/bin/bash

COMMON=(
       #Common
       Errors.v
       AST.v 
       Values.v
       Linking.v
       MemPerm.v
       Memdata.v
       Assoc.v
       StackADT.v
       Memtype.v
       Memory.v
       Globalenvs.v
       Events.v
       StackInj.v
       Smallstep.v
       Behaviors.v
       Switch.v
       Determinism.v
       Unityping.v
       Separation.v
       )

BACKEND=(
	#Backend
	./backend/Cminor.v
	./x86/Op.v
	./backend/CminorSel.v
	./x86/SelectOp.v
	./backend/SplitLong.v
	./x86/SelectLong.v
	./backend/SelectDiv.v
	./x86/Machregs.v
	./backend/Selection.v
	./x86/SelectOpproof.v
	./backend/SplitLongproof.v
	./x86/SelectLongproof.v
	./backend/SelectDivproof.v
	./backend/Selectionproof.v
	./backend/Registers.v
	./backend/RTL.v
	./backend/RTLgen.v
	./backend/RTLgenspec.v
	./backend/RTLgenproof.v
	./backend/Locations.v
	./x86/Conventions1.v
	./backend/Conventions.v
	./backend/Tailcall.v
	./backend/Tailcallproof.v
	./backend/Inlining.v
	./backend/Inliningspec.v
	./backend/Inliningproof.v
	./backend/Renumber.v
	./backend/Renumberproof.v
	./backend/RTLtyping.v
	./backend/Kildall.v
	./backend/Liveness.v
	./backend/ValueDomain.v
	./x86/ValueAOp.v
	./backend/ValueAnalysis.v
	./x86/ConstpropOp.v
	./backend/Constprop.v
	./x86/ConstpropOpproof.v
	./backend/Constpropproof.v
	./backend/CSEdomain.v
	./x86/CombineOp.v
	./backend/CSE.v
	./x86/CombineOpproof.v
	./backend/CSEproof.v
	./backend/NeedDomain.v
	./x86/NeedOp.v
	./backend/Deadcode.v
	./backend/Deadcodeproof.v
	./backend/Unusedglob.v
	./backend/Unusedglobproof.v
	./backend/LTL.v
	./backend/Allocation.v
	./backend/Allocproof.v
	./backend/Tunneling.v
	./backend/Tunnelingproof.v
	./backend/Linear.v
	./backend/Linearize.v
	./backend/Linearizeproof.v
	./backend/CleanupLabels.v
	./backend/CleanupLabelsproof.v
	./backend/Debugvar.v
	./backend/Debugvarproof.v
	./backend/Bounds.v
	./x86/Stacklayout.v
	./backend/Mach.v
	./backend/Lineartyping.v
	./backend/Stacking.v
	./backend/Stackingproof.v
	)

FRONTEND=(
        #Frontend
        Ctypes.v
        Cop.v
        Csyntax.v
        Csem.v
        Ctyping.v
        Cstrategy.v
        Cexec.v
        #Cexecimpl.v
        Initializers.v
        Initializersproof.v
        Clight.v
        ClightBigstep.v
        SimplExpr.v
        SimplExprspec.v
        SimplExprproof.v
        SimplLocals.v
        SimplLocalsproof.v
        Csharpminor.v
        Cshmgen.v
        Cshmgenproof.v
        Cminorgen.v
        Cminorgenproof.v
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