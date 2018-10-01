#define N  7

int a[N] = {1, 17, 4, 9, 22, 0, -12};

int max(int* p, int size)
{
  int m, i;

  m = p[0];
  for (i = 1; i < size; i++) {
    if (p[i] > m)
      m = p[i];
  }

  return m;
}


int main() {
  int n = max (a, N);
  return n;
}
