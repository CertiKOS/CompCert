int gcd (int a, int b)
{
  while (b != a) {
    if (a > b)
      a -= b;
    else
      b -= a;
  }
  return a;
}

int x = 42;
int y = 49;

int main()
{
  return gcd(x, y);
}
