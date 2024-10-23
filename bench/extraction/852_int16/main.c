#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

extern uint16_t bcd_compute(uint16_t);

int main() {
  uint16_t x = bcd_compute(1234u);
  if (x != 4660u) {
    printf("Test failed!\n");
    exit(1);
  }
  return 0;
}
