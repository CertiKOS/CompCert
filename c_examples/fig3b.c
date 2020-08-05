extern void record (int);
extern int main();

int c = 0;

int get() {return c;}

void incr() { record(c); c++; }