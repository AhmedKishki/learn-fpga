/*******************************************************************/
// Neutrino: A minimalistic RISC-V RV32E core (16 registers).
// Base instruction set: RV32E + RDCYCLES
//
// Differences from Quark RV32I:
//   - Register file has size 16 (x0..x15) instead of 32 (x0..x31).
//   - Any access to registers above x15 is ignored (no traps here).
//
// Bruno Levy, Matthias Koch, 2020-2021
// Adapted for RV32E by Ahmed Alkishki
/*******************************************************************/

// Firmware generation flags for this processor
`define NRV_ARCH        "rv32e"
`define NRV_ABI         "ilp32e"
`define NRV_OPTIMIZE    "-Os"

module FemtoRV32(
   input 	 clk,

   output [31:0] mem_addr,  // address bus
   output [31:0] mem_wdata, // data to be written
   output [3:0]  mem_wmask, // write mask for the 4 bytes of each word
   input [31:0]  mem_rdata, // input lines for both data and instr
   output 	 mem_rstrb, // active to initiate memory read (used by IO)
   input 	 mem_rbusy, // asserted if memory is busy reading value
   input 	 mem_wbusy, // asserted if memory is busy writing value

   input 	 reset      // set to 0 to reset the processor
);

    parameter RESET_ADDR       = 32'h00000000;
    parameter ADDR_WIDTH       = 24;

    reg [31:0] registerFile [15:0]; // RV32E provies 16 registers, each 32 bit wide 

    /***************************************************************************/
    // STATE MACHINE
    /***************************************************************************/
	// ONE HOT ENCODING FOR STATES
	localparam FETCH_INSTR_bit     = 0;  // Initiate instruction fetch
	localparam WAIT_INSTR_bit      = 1;  // Wait for instruction from memory
	localparam EXECUTE_bit         = 2;  // Execute decoded instruction
	localparam WAIT_ALU_OR_MEM_bit = 3;  // Wait for ALU/memory operations to complete

	localparam FETCH_INSTR     = 1 << FETCH_INSTR_bit;     // 4'b0001
	localparam WAIT_INSTR      = 1 << WAIT_INSTR_bit;      // 4'b0010
	localparam EXECUTE         = 1 << EXECUTE_bit;         // 4'b0100
	localparam WAIT_ALU_OR_MEM = 1 << WAIT_ALU_OR_MEM_bit; // 4'b1000

	always @(posedge clk) begin
		if (!reset) begin
			// Reset condition: Initialize PC and state
			state <= WAIT_ALU_OR_MEM;
			PC    <= RESET_ADDR[ADDR_WIDTH-1:0];
		end else 
		begin
			case (1'b1) // Reverse case statement (checks which state bit is high)
				//──────────────────────────────────────────────────────
				// STATE: WAIT_INSTR
				// Wait for memory to return instruction
				//──────────────────────────────────────────────────────
				state[WAIT_INSTR_bit]: begin
					if (!mem_rbusy) begin // Instruction ready
						// Latch registers and instruction
						rs1   <= registerFile[mem_rdata[18:15]]; // Read rs1
						rs2   <= registerFile[mem_rdata[23:20]]; // Read rs2
						instr <= mem_rdata[31:2]; // Store instruction (bits 0-1 unused)
						state <= EXECUTE; // Move to EXECUTE
					end
				end

				//──────────────────────────────────────────────────────
				// STATE: EXECUTE
				// Decode/execute instruction
				//──────────────────────────────────────────────────────
				state[EXECUTE_bit]: begin
					// Update PC based on instruction type
					PC <= isJALR          ? {aluPlus[ADDR_WIDTH-1:1], 1'b0} : // Jump-register
						jumpToPCplusImm ? PCplusImm : // Jump/branch
						PCplus4; // Default: next instruction

					// Transition to next state:
					// If operation needs time (memory/ALU), wait; else fetch next instruction
					state <= needToWait ? WAIT_ALU_OR_MEM : FETCH_INSTR;
				end

				//──────────────────────────────────────────────────────
				// STATE: WAIT_ALU_OR_MEM
				// Wait for slow operations (shifts/memory)
				//──────────────────────────────────────────────────────
				state[WAIT_ALU_OR_MEM_bit]: begin
					// Continue when ALU/memory is ready
					if (!aluBusy & !mem_rbusy & !mem_wbusy) state <= FETCH_INSTR;
				end

				//──────────────────────────────────────────────────────
				// DEFAULT STATE: FETCH_INSTR
				// Initiate new instruction fetch
				//──────────────────────────────────────────────────────
				default: begin // FETCH_INSTR
					state <= WAIT_INSTR; // Wait for memory response
				end
			endcase
		end
	end


endmodule