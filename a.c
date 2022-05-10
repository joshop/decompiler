#include <stdio.h>

int myfunction() {
	return 4;
}

int main() {
	printf("Hello, world!\n");
	int a = myfunction();
	printf("%d\n", a);
}
