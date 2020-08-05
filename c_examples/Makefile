clean:
	rm -f *.o
	rm -f *.out
	rm -f comp_result.txt gcc_result.txt


compile:
	# ../ccomp -timings -relf *.c
	# ls *.o|sed 's/\(.*\)\.o/gcc -m32 -static -nostdlib stubstart.s \1.o -o \1.out/g'|sh
	ls *.c|sed 's/\(.*\)\.c/\.\.\/ccomp -stdlib ..\/runtime -relf \1.c -o \1.out/g'|sh

test: compile
	chmod +x *.out
	./runt.sh > comp_result.txt
	# ls *.c|sed 's/\(.*\)\.c/gcc -m32 -static -nostdlib stubstart.s \1.c -o \1.o/g'|sh
	ls *.c|sed 's/\(.*\)\.c/gcc \1.c -o \1.o/g'|sh
	chmod +x *.o
	./run.sh > gcc_result.txt
	cat comp_result.txt
	cat gcc_result.txt
	diff comp_result.txt gcc_result.txt
