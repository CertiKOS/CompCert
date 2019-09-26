clean:
	rm *.o
	rm *.out


compile:
	../ccomp -timings -relf *.c
	ls *.o|sed 's/\(.*\)\.o/gcc -m32 -static \1.o -o \1.out/g'|sh

test: compile
	chmod +x *.out
	./runt.sh > comp_result.txt
	ls *.c|sed 's/\(.*\)\.c/gcc \1.c -o \1.o/g'|sh
	chmod +x *.o
	./run.sh > gcc_result.txt
	cat comp_result.txt
	cat gcc_result.txt
	diff comp_result.txt gcc_result.txt
