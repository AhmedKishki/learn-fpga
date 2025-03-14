#include <femtorv32.h>

void main(void){
    while(1){
        printf("HELLO RISCV ON iCE40!\r\n");
        printf("Freq %d MHz\r\n", FEMTORV32_FREQ);
        *(volatile uint32_t*)(IO_BASE + IO_LEDS)=(3); // casting address as pointer and dereferencing
        delay(500);
        *(volatile uint32_t*)(IO_BASE + IO_LEDS)=(0);
        delay(500);
    }
}