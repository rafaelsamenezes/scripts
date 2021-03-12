#include <stdlib.h>

// Out of bounds array
int main() {
    int a[3];
    a[__VERIFIER_nondet_int()] = 10;
    return 0;
}