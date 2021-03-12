#include <stdlib.h>

int* deref() {
    int x;
    return &x;
}

// Deref
int main() {
    int *a = deref();
    if(__VERIFIER_nondet_int()) *a = 7;
    return 0;
}