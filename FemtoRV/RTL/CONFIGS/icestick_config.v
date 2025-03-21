// Default femtosoc configuration file for IceStick

/************************* Devices **********************************************************************************/

`define NRV_IO_LEDS          // Mapped IO, LEDs D1,D2,D3,D4 (D5 is used to display errors)
// `define NRV_IO_IRDA          // In IO_LEDS, support for the IRDA on the IceStick (WIP)
`define NRV_IO_UART          // Mapped IO, virtual UART (USB)
// `define NRV_IO_SSD1351       // Mapped IO, 128x128x64K OLED screen
// `define NRV_IO_MAX7219       // Mapped IO, 8x8 led matrix
`define NRV_MAPPED_SPI_FLASH // SPI flash mapped in address space. Can be used to run code from SPI flash.
//`define NRV_IO_PWM           // Use PWM peripheral to control LED

/************************* Processor configuration *******************************************************************/

// `define NRV_FEMTORV32_TACHYON       // "Tachyon" (carefully latched for max highfreq). Needs more space (remove MAX7219).
// `define NRV_FREQ 60                 // Validated at 60 MHz on the IceStick. Can overclock to 80-95 MHz.
// `define NRV_RESET_ADDR 32'h00820000 // Jump execution to SPI Flash (800000h, +128k(20000h) for FPGA bitstream)
// `define NRV_COUNTER_WIDTH 24        // Number of bits in cycles counter
// `define NRV_TWOLEVEL_SHIFTER        // Faster shifts
// tinyraytracer: 90 MHz, 14:02
//                95 MHz, 13:18

// `define NRV_FEMTORV32_QUARK
// `define NRV_FREQ 50                 // Validated at 50 MHz on the IceStick. Can overclock to 70 MHz.
// `define NRV_RESET_ADDR 32'h00820000 // Jump execution to SPI Flash (800000h, +128k(20000h) for FPGA bitstream)
// `define NRV_COUNTER_WIDTH 24        // Number of bits in cycles counter
// `define NRV_TWOLEVEL_SHIFTER        // Faster shifts
// tinyraytracer: 70 MHz, 17:30 

`define NRV_FEMTORV32_NEUTRINO
`define NRV_FREQ 50                 // Validated at 50 MHz on the IceStick. Can overclock to 70 MHz.
`define NRV_RESET_ADDR 32'h00820000 // Jump execution to SPI Flash (800000h, +128k(20000h) for FPGA bitstream)
`define NRV_COUNTER_WIDTH 24        // Number of bits in cycles counter
`define NRV_TWOLEVEL_SHIFTER        // Faster shifts

/************************* RAM (in bytes, needs to be a multiple of 4)***********************************************/

`define NRV_RAM 6144 // default for ICESTICK (cannot do more !)


/************************* Advanced devices configuration ***********************************************************/

`define NRV_RUN_FROM_SPI_FLASH // Do not 'readmemh()' firmware from '.hex' file
`define NRV_IO_HARDWARE_CONFIG // Comment-out to disable hardware config registers mapped in IO-Space
                               // (note: firmware libfemtorv32 depends on it)

/********************************************************************************************************************/

`define NRV_CONFIGURED
