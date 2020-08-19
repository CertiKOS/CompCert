#include <stdio.h>

static int static_uninit;
static int static_init = 1;
int local_uninit;
int local_init = 3;
extern int extern_declare;
int extern_undeclare;

void link();

void test_bss() {
  static int st_inside_uninit;
  static int st_inside_init = 9;
  st_inside_uninit = 10;
  printf("%d\n", static_uninit);
  printf("%d\n", static_init);
  printf("%d\n", local_uninit);
  printf("%d\n", local_init);
  printf("%d\n", extern_declare);
  printf("%d\n", extern_undeclare);
  printf("%d\n", st_inside_init);
  printf("%d\n", st_inside_uninit);
}

int main() {
  static_uninit = 0;
  local_uninit = 2;
  link();
  test_bss();
  return 0;
}