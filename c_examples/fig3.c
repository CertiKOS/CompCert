extern int get(void); 
extern void incr(void); 
int limit = 10;

int rcd [10] = {0};

void record(int c) { rcd[c] = c; }

int main() { 
  int i = get(); 
  while (i < limit) { incr(); i = get();}
return 0; 
}