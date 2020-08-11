
int fac(int n)
{
  int v = 0;

  if (n == 0) {
    v = 1;
  } else {
    v = n * fac(n-1);
  }

  return v;
}

int main()
{
  return fac(6);
}
