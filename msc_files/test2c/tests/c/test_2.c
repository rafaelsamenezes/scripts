#include <stdlib.h>

// Memory Leak
int main() {
    int *a = malloc(4);
    if(__VERIFIER_nondet_int())
        free(a);
    return 0;
}