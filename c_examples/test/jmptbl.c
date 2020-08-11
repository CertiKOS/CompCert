#include <stdio.h>

int cmd[10] = {1, 2, 5, 2, 2, 8, 3, 7, 3, 9};

void test_jmplabel() {
  int sum[10] = {0};
  int i = 0;
  while (1) {
    switch (cmd[i]) {
    case 1:
    case 5:
      sum[i] = 1;
      break;
    case 4:
      sum[i] = 4;
      break;
    case 2:
      sum[i] = 2;
      break;
    case 3:
      sum[i] = 3;
      break;

    case 6:
      sum[i] = 6;
      break;
    case 7:
    case 8:
      sum[i] = 7;
      break;
    case 9:
      sum[i] = 9;
      break;
    default:
      break;
    }
    i++;
    if (i >= 9)
      break;
  }
  for (int x = 0; x < 10; x++) {
    printf("%d ", sum[x]);
  }
  printf("\n");
}

int main() {
  test_jmplabel();
  return 0;
}