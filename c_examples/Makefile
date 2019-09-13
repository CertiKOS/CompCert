clean:
	rm *.o


compile:
	../ccomp -timings -machinecode *.c

test: compile
	chmod +x *.o
	./run.sh > comp_result.txt
	ls *.c|sed 's/\(.*\)\.c/gcc \1.c -o \1.o/g'|sh
	chmod +x *.o
	./run.sh > gcc_result.txt
	cat comp_result.txt
	cat gcc_result.txt
	diff comp_result.txt gcc_result.txt
