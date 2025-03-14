#include <femtorv32.h>

int main() {
	while (1) {
		for (int i = 0; i < 4096; i++) {
			*(volatile uint32_t*)(0x404000) = i;
                        delay(1);
		}
	}
	return 0;
}