#include <stdlib.h>

// Double free
int main() {
    int *a = malloc(4);
    free(a);
    if(__VERIFIER_nondet_int())
        free(a);
    return 0;
}