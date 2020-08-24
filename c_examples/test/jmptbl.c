#include <stdio.h>

static int cmd[10] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10};

static void test_jmplabel() {
  int sum[10] = {0};
  int i = 0;
  while (1) {
    printf("%d: ", cmd[i]);
    switch (cmd[i]) {
    case 1:
    case 6:
      sum[i] = 1;
      break;
    case 2:
    case 7:
      sum[i] = 2;
      break;
    case 3:
    case 8:
      sum[i] = 3;
      break;
    case 4:
    case 9:
      sum[i] = 4;
      break;
    case 5:
    case 10:
      sum[i] = 5;
      break;
    default:
      break;
    }
    printf("%d\n", sum[i]);
    i++;
    if (i >= 10)
      break;
  }
  for (int x = 0; x < 10; x++) {
    printf("%d ", sum[x]);
  }
  printf("\n");
}

static void test_jmplabel1() {
  int sum[10] = {0};
  int i = 0;
  while (1) {
    printf("%d: ", cmd[i]);
    switch (cmd[i]) {
    case 1:
    case 6:
    case 2:
    case 7:
    case 3:
    case 8:
    case 4:
    case 9:
    case 5:
    case 10:
      sum[i] = 1;
      break;
    }
    printf("%d\n", sum[i]);
    i++;
    if (i >= 10)
      break;
  }
  for (int x = 0; x < 10; x++) {
    printf("%d ", sum[x]);
  }
  printf("\n");
}

int main() {
  test_jmplabel();
  test_jmplabel1();
  return 0;
}