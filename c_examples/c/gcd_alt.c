int gcd(int a, int b)
{
  if (b == 0)
    return a; 
  else
    return gcd(b, a % b);
}

int x = 42;
int y = 49;

int main() 
{
  return gcd(x,y);
}
