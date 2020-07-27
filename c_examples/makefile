include ../Makefile.config

CCOMP=../ccomp
CCOMPFLAGS=-stdlib ../runtime -relf -static

CFLAGS=-O1 -Wall

OBJDUMP=objdump
READELF=readelf

PROGS= rodata aes

all: $(PROGS:%=%.ccomp.out) $(PROGS:%=%.gcc.out)

%.ccomp.out: %.c $(CCOMP)
	$(CCOMP) $(CCOMPFLAGS) -o $*.ccomp.out $*.c
	$(OBJDUMP) -D $*.o > $*.obj.ccomp.asm
	$(READELF) -a $*.o > $*.obj.ccomp.hdr

%.gcc.out: %.c $(CCOMP)
	$(CC) $(CFLAGS) -c $*.c
	$(CC) $(CFLAGS) -o $*.gcc.out $*.o
	$(OBJDUMP) -D $*.o > $*.obj.gcc.asm
	$(READELF) -a $*.o > $*.obj.gcc.hdr

test:
	@for i in $(PROGS); do \
	   if ./$$i.ccomp.out | cmp -s - Results/$$i; \
           then echo "$$i: passed"; \
           else echo "$$i: FAILED"; exit 2; \
	   fi; \
         done

test_gcc:
	@for i in $(PROGS); do \
	   if ./$$i.gcc.out | cmp -s - Results/$$i; \
           then echo "$$i: passed"; \
           else echo "$$i: FAILED"; \
	   fi; \
         done

clean:
	rm -f *.o *.out 
	rm -f *.asm *.hdr