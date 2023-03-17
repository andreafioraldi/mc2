#include <stdio.h>

int main(int argc, char** argv) {    
    unsigned int byte0 = 0;
    FILE* fp;
    fp = fopen(argv[1], "r");
    int res = fread(&byte0, 1, 1, fp);
    printf("%d is input\n", byte0);

    int sum = 0;
    if ( byte0 < 3) {
        sum = byte0 + 0;      
        printf("Took true direction: %d is the result\n", sum);
    } else {
        sum = byte0 - 15;      
        printf("Took false direction: %d is the result\n", sum);
    }
    
    return 0;
}
