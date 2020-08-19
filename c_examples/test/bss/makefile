include ../../../Makefile.config

CCOMP=../../../ccomp
CCOMPFLAGS=-stdlib ../../../runtime -relf -static
#CCOMPFLAGS=-stdlib ../../../runtime -dc -dclight -dasm

CFLAGS=-O1 -Wall

LIBS= -lm

OBJDUMP=objdump
READELF=readelf

all: ccomp gcc
ccomp: bss.ccomp.out
gcc: bss.gcc.out

%.ccomp.out: bss.c link.c $(CCOMP)
	$(CCOMP) $(CCOMPFLAGS) -o bss.ccomp.out bss.c link.c $(LIBS)
	$(OBJDUMP) -D bss.o > bss.obj.ccomp.asm
	$(READELF) -a bss.o > bss.obj.ccomp.hdr
	#$(OBJDUMP) -D $*.ccomp.out > $*.ccomp.out.asm
	#$(READELF) -a $*.ccomp.out > $*.ccomp.out.hdr

%.gcc.out: bss.c link.c $(CCOMP)
	$(CC) $(CFLAGS) -c bss.c
	$(CC) $(CFLAGS) -c link.c
	$(CC) $(CFLAGS) -o bss.gcc.out bss.o link.o $(LIBS)
	$(OBJDUMP) -D bss.o > bss.obj.gcc.asm
	$(READELF) -a bss.o > bss.obj.gcc.hdr

clean:
	rm -f *.o *.out 
	rm -f *.asm *.hdr
