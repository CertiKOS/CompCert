extern void record (int);

int c = 0;

int get() {return c;}

void incr() { record(c); c++; }