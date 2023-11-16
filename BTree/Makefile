VS      := Think.v ThinkList.v ThinkArith.v ThinkEq.v LiftOrder.v \
           BPlusTreeImplModel.v \
	   BPlusTreeModelFacts.v \
	   BPlusTreeTactics.v \
           ArrayOps.v \
           BPlusTreeImplNewFree.v \
	   BPlusTreeImplLocalComputeHelp.v \
	   BPlusTreeImplLookup.v \
	   BPlusTreeImplInsert.v \
	   BPlusTreeImplIterate.v \
           BPlusTreeImplLocalCompute.v \
           BPlusTreeImpl.v

.MODULES := $(VS:%.v=%)

.SUFFIXES: .v .vo

.PHONY: coq clean

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

R := -R ../../../src/coq Ynot -R ../../Data Data -R .. Rdb

Makefile.coq: Makefile $(VS)
	coq_makefile $(VS) $(R) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq .depend
	rm -f *.glob *.v.d

.v.vo: $.v
	coqc $(R) -q  $(<:.v=) 
