all: fig3
	@echo "Done."

# Use GNU ld to link object files
fig3: fig3a.o fig3b.o
	gcc -m32 $^ -o fig3

# Use CompCertELF to compile sources
fig3a.o: fig3a.c
	../../ccomp -c -relf fig3a.c

fig3b.o: fig3b.c
	../../ccomp -c -relf fig3b.c

.PHONY: clean

clean:
	rm *.o fig3
