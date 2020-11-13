// femtorv32, a minimalistic RISC-V RV32I core
//    (minus SYSTEM and FENCE that are not implemented)
//
//       Bruno Levy, May-June 2020
//
// Mission statement:
//   - understand basics of FPGA and processor design
//   - learn about RISC-V
//   - create a RISC-V design that is easy to understand (and that
//       I'm able to re-read, re-understand later)
//   - create a RISC-V design that can be used on the cheapest /
//       smallest FPGAs (ICEStick) and that can be programmed in
//       assembly and C using the GNU RISC-V toolchain
//
//   Note: femtorv32 is meant to be used for educational purposes,
// targeting legibility of the design and minimal LUT footprint.
//  For other usages, if your FPGA has more than 1380 LUTs (that means,
// is something else than an ICEStick), I recommend using a more efficient /
// more complete RISC-V core (e.g., Claire Wolf's picorv32).

// LUT-golfing par: 1184 LUTs (ICEStick, ICESTORM_LC)
// Tested with the following configuration:
//   NRV_TWO_STAGE_SHIFTER=ON
//   NRV_NEGATIVE_RESET=ON,
//   NRV_IO_LEDS=ON
//   NRV_IO_UART=ON
//   NRV_IO_SSD1351=OFF
//   NRV_IO_MAX2719=OFF
//   NRV_IO_SPI_FLASH=OFF
//   NRV_FREQ=80
//   NRV_RAM=6144
//   NRV_COUNTERS=OFF
//   NRV_COUNTERS_64=OFF
//   NRV_RV32M=OFF
//
// Dhrystones test (tested on the ULX3S and ECPC-EVN):
// With NRV_TWOSTAGE_SHIFTER: 3.904 CPI, 714 Dhrystones/s/MHz, 0.406 DMIPS/MHz
// With NRV_BARREL_SHIFTER  : 3.854 CPI, 723 Dhrystones/s/MHz, 0.411 DMIPS/MHz

`ifdef VERBOSE
  `define verbose(command) command
`else
  `define verbose(command)
`endif

`ifdef BENCH
 `ifdef QUIET
  `define bench(command) 
 `else
  `define bench(command) command
 `endif
`else
  `define bench(command)
`endif

/***************************** REGISTER FILE *****************************/

module NrvRegisterFile(
  input 	    clk, 
  input [31:0] 	    in,        // Data for write back register
  input [4:0] 	    inRegId,   // Register to write back to
  input 	    inEn,      // Enable register write back
  input [4:0] 	    outRegId1, // Register number for out1
  input [4:0] 	    outRegId2, // Register number for out2
  output reg [31:0] out1, // Data out 1, available one clock after outRegId1 is set
  output reg [31:0] out2  // Data out 2, available one clock after outRegId2 is set
);
   // Register file is duplicated so that we can read rs1 and rs2 simultaneously
   // It is a bit stupid, it wastes four (inferred) SB_RAM40_4K BRAMs, where a single
   // one would suffice, but it makes things simpler (and the CPU faster).
   
   reg [31:0]  bank1 [30:0];
   reg [31:0]  bank2 [30:0];

   always @(posedge clk) begin
      if (inEn) begin
	 // This test seems to be needed ! (else J followed by LI results in wrong result)
	 if(inRegId != 0) begin 
	    bank1[~inRegId] <= in;
	    bank2[~inRegId] <= in;
	 end	  
      end
      // Test bench does not seem to understand that
      // oob access in reg array is supposed to return 0.
      // TODO: test whether it is also required by the
      // IceStick version (does not seem to be the case).
`ifdef BENCH	 
      out1 <= (outRegId1 == 0) ? 0 : bank1[~outRegId1];
      out2 <= (outRegId2 == 0) ? 0 : bank2[~outRegId2];
`else
      out1 <= bank1[~outRegId1];
      out2 <= bank2[~outRegId2];
`endif
   end
endmodule


/********************************* Small ALU **********************************/
// Small version of the ALU
// To be used on the ICEStick, when NRV_RV32M is not set.
// Implements the RV32I instruction set.

module NrvSmallALU #(
   parameter [0:0] TWOSTAGE_SHIFTER = 0 // optional twostage shifter, makes shifts faster
		                        // (but eats up 60 LUTs or so)
)(
  input 	    clk, 
  input [31:0] 	    in1,
  input [31:0] 	    in2,
  input [2:0] 	    op,     // Operation
  input 	    opqual, // Operation qualification (+/-, Logical/Arithmetic)
  output reg [31:0] out,    // ALU result. Latched if operation is a shift
  output 	    busy,   // 1 if ALU is currently computing (that is, shift)
  input 	    wr      // Raise to write ALU inputs and start computing
);

   reg [31:0] ALUreg;          // The internal register of the ALU, used by shifts.
   reg [4:0]  shamt = 0;       // current shift amount.
   assign busy = (shamt != 0); // ALU is busy if shift amount is non-zero.
      
   // Implementation suggested by Matthias Koch, uses a single 33 bits 
   // subtract for all the tests, as in swapforth/J1.
   // NOTE: if you read swapforth/J1 source,
   //   J1's st0,st1 are inverted as compared to in1,in2 (st0<->in2  st1<->in1)
   // Equivalent code:
   // case(op) 
   //    3'b000: out = opqual ? in1 - in2 : in1 + in2;                 // ADD/SUB
   //    3'b010: out = ($signed(in1) < $signed(in2)) ? 32'b1 : 32'b0 ; // SLT
   //    3'b011: out = (in1 < in2) ? 32'b1 : 32'b0;                    // SLTU
   //    ...
	 
   wire [32:0] minus = {1'b1, ~in2} + {1'b0,in1} + 33'b1;
   wire        LT  = (in1[31] ^ in2[31]) ? in1[31] : minus[32];
   wire        LTU = minus[32];

   always @(*) begin
      (* parallel_case, full_case *)
      case(op)
	3'b000: out = opqual ? minus[31:0] : in1 + in2;  // ADD/SUB
	3'b010: out = LT ;                               // SLT
	3'b011: out = LTU;                               // SLTU
	3'b100: out = in1 ^ in2;                         // XOR
	3'b110: out = in1 | in2;                         // OR
	3'b111: out = in1 & in2;                         // AND
	
	// Shift operations, get result from the shifter
	3'b001: out = ALUreg;                           // SLL	   
	3'b101: out = ALUreg;                           // SRL/SRA
      endcase // case (op)
   end
   
   always @(posedge clk) begin
      
      /* verilator lint_off WIDTH */
      /* verilator lint_off CASEINCOMPLETE */

      if(wr) begin
	 case(op)
	   3'b001: begin ALUreg <= in1; shamt <= in2[4:0]; end // SLL	   
	   3'b101: begin ALUreg <= in1; shamt <= in2[4:0]; end // SRL/SRA
	 endcase 
      end else begin
	 if (TWOSTAGE_SHIFTER && shamt > 4) begin
	    shamt <= shamt - 4;
	    case(op)
	      3'b001: ALUreg <= ALUreg << 4;                               // SLL
	      3'b101: ALUreg <= opqual ? {{4{ALUreg[31]}}, ALUreg[31:4]} : // SRL/SRA 
                                         { 4'b0000,        ALUreg[31:4]} ; 
	    endcase 
	 end else  
	   if (shamt != 0) begin
	      shamt <= shamt - 1;
	      case(op)
		3'b001: ALUreg <= ALUreg << 1;                          // SLL
		3'b101: ALUreg <= opqual ? {ALUreg[31], ALUreg[31:1]} : // SRL/SRA 
				           {1'b0,       ALUreg[31:1]} ; 
	      endcase 
	   end
      end 
      /* verilator lint_on WIDTH */
      /* verilator lint_on CASEINCOMPLETE */
   end 
endmodule


/********************************* Large ALU **********************************/
// Large version of the ALU
// Implements the RV32IM instruction set, with MUL,DIV,REM
// Includes a barrel shifter (that shifts in 1 clock)

module NrvLargeALU (
  input 	    clk, 
  input [31:0] 	    in1,
  input [31:0] 	    in2,
  input [2:0] 	    op,     // Operation
  input 	    opqual, // Operation qualification (+/-, Logical/Arithmetic)
  input             opM,    // Asserted if operation is an RV32M operation
  output reg [31:0] out,    // ALU result. Latched if operation is a shift,mul,div,rem
  output 	    busy,   // 1 if ALU is currently computing (that is, shift,mul,div,rem)
  input 	    wr      // Raise to write ALU inputs and start computing
);

   reg [31:0] ALUreg; // The internal register of the ALU, used by MUL(H)(U) and shifts.

   // Implementation of DIV/REM instructions, highly inspired by PICORV32
   reg [31:0] 	      dividend;
   reg [62:0] 	      divisor;
   reg [31:0] 	      quotient;
   reg [31:0] 	      quotient_msk;
   reg 		      outsign;

   assign busy = opM && |quotient_msk; // ALU is busy if a DIV or REM operation is running.
      
   // Implementation suggested by Matthias Koch, uses a single 33 bits 
   // subtract for all the tests, as in swapforth/J1.
   // NOTE: if you read swapforth/J1 source,
   //   J1's st0,st1 are inverted as compared to in1,in2 (st0<->in2  st1<->in1)
   // Equivalent code:
   // case(op) 
   //    3'b000: out = opqual ? in1 - in2 : in1 + in2;                 // ADD/SUB
   //    3'b010: out = ($signed(in1) < $signed(in2)) ? 32'b1 : 32'b0 ; // SLT
   //    3'b011: out = (in1 < in2) ? 32'b1 : 32'b0;                    // SLTU
   //    ...
	 
   wire [32:0] minus = {1'b1, ~in2} + {1'b0,in1} + 33'b1;
   wire        LT  = (in1[31] ^ in2[31]) ? in1[31] : minus[32];
   wire        LTU = minus[32];

   // Implementation of MUL instructions: using a single 33 * 33
   // multiplier, and doing sign extension or not according to
   // the signedness of the operands in instruction.
   // On the ECP5, yosys infers four 18x18 DSPs.
   // For FPGAs that don't have DSP blocks, we could use an
   // iterative algorithm instead (e.g., the one in FIRMWARE/LIB/mul.s)
   wire               in1U = (op == 3'b011);
   wire               in2U = (op == 3'b010 || op == 3'b011);
   wire signed [33:0] in1E = {in1U ? 1'b0 : in1[31], in1};
   wire signed [33:0] in2E = {in2U ? 1'b0 : in2[31], in2};
   wire signed [63:0] times = in1E * in2E;

   always @(*) begin
      if(opM) begin
	 case(op)
	   3'b000: out <= ALUreg;                           // MUL
	   3'b001: out <= ALUreg;                           // MULH
	   3'b010: out <= ALUreg;                           // MULHSU
	   3'b011: out <= ALUreg;                           // MULHU
	   3'b100: out <= outsign ? -quotient : quotient;   // DIV
	   3'b101: out <= quotient;                         // DIVU
	   3'b110: out <= outsign ? -dividend : dividend;   // REM 
	   3'b111: out <= dividend;                         // REMU
	 endcase
      end else begin
	 (* parallel_case, full_case *)
	 case(op)
           3'b000: out = opqual ? minus[31:0] : in1 + in2;  // ADD/SUB
           3'b010: out = LT ;                               // SLT
           3'b011: out = LTU;                               // SLTU
           3'b100: out = in1 ^ in2;                         // XOR
           3'b110: out = in1 | in2;                         // OR
           3'b111: out = in1 & in2;                         // AND
	   
	   // We could generate the barrel shifter here, but doing so
	   // makes the critical path too long, so we keep a two-phase
	   // ALU instead.
           3'b001: out = ALUreg;                           // SLL	   
           3'b101: out = ALUreg;                           // SRL/SRA
	 endcase // case (op)
      end
   end 

   
   always @(posedge clk) begin
      
      /* verilator lint_off WIDTH */
      /* verilator lint_off CASEINCOMPLETE */

      if(opM) begin
	 if(wr) begin 
	    case(op)
	      3'b000: ALUreg <= times[31:0];  // MUL
	      3'b001: ALUreg <= times[63:32]; // MULH
	      3'b010: ALUreg <= times[63:32]; // MULHSU
	      3'b011: ALUreg <= times[63:32]; // MULHU

	      // Initialize internal registers for
	      // DIV, DIVU, REM, REMU.
	      // DIV, and REM: extract operand signs,
	      // and get absolute value of operands.
	      3'b100: begin // DIV
		 dividend <= in1[31] ? -in1 : in1;
		 divisor  <= (in2[31] ? -in2 : in2) << 31;
		 outsign  <= (in1[31] != in2[31]) && |in2;
		 quotient <= 0;
		 quotient_msk <= 1 << 31;
	      end
	      3'b101: begin // DIVU
		 dividend <= in1;
		 divisor  <= in2 << 31;
		 outsign  <= 1'b0;
		 quotient <= 0;
		 quotient_msk <= 1 << 31;
	      end
	      3'b110: begin // REM
		 dividend <= in1[31] ? -in1 : in1;
		 divisor  <= (in2[31] ? -in2 : in2) << 31;		 
		 outsign  <= in1[31];
		 quotient <= 0;
		 quotient_msk <= 1 << 31;
	      end
	      3'b111: begin // REMU
		 dividend <= in1;
		 divisor  <= in2 << 31;
		 outsign  <= 1'b0;
		 quotient <= 0;
		 quotient_msk <= 1 << 31;
	      end
	    endcase // case (op)
	 end else begin // if (wr)
	    // The division algorithm is here.
	    // On exit, divisor is the remainder.
	    if(divisor <= dividend) begin
	       dividend <= dividend - divisor;
	       quotient <= quotient | quotient_msk;
	    end
	    divisor <= divisor >> 1;
	    quotient_msk <= quotient_msk >> 1;
	 end
      end else if(wr) begin // Barrel shifter, latched to reduce combinatorial depth.
	 case(op)
	   3'b001: ALUreg <= in1 << in2[4:0];                                      // SLL	   
	   3'b101: ALUreg <= $signed({opqual ? in1[31] : 1'b0, in1}) >>> in2[4:0]; // SRL/SRA
	 endcase 
      end 
      /* verilator lint_on WIDTH */
      /* verilator lint_on CASEINCOMPLETE */
   end 
endmodule

/********************* Branch predicates *******************************/

module NrvPredicate(
   input [31:0] in1,
   input [31:0] in2,
   input [2:0]  op, // Operation
   output reg   out
);

   // Implementation suggested by Matthias Koch, uses a single 33 bits 
   // subtract for all the tests, as in swapforth/J1.
   // NOTE: if you read swapforth/J1 source, J1's st0,st1 are inverted 
   // as compared to in1,in2 (st0<->in2  st1<->in1)
   // Equivalent code:
   // case(op)
   //   3'b000: out = (in1 == in2);                   // BEQ
   //   3'b001: out = (in1 != in2);                   // BNE
   //   3'b100: out = ($signed(in1) < $signed(in2));  // BLT
   //   3'b101: out = ($signed(in1) >= $signed(in2)); // BGE
   //   3'b110: out = (in1 < in2);                    // BLTU
   //   3'b111: out = (in1 >= in2);                   // BGEU
   //   ...

   wire [32:0] 	minus = {1'b1, ~in2} + {1'b0,in1} + 33'b1;
   wire 	LT  = (in1[31] ^ in2[31]) ? in1[31] : minus[32];
   wire 	LTU = minus[32];
   wire 	EQ  = (minus[31:0] == 0);
      
   always @(*) begin
      (* parallel_case, full_case *)	 
      case(op)
        3'b000: out =  EQ;   // BEQ
        3'b001: out = !EQ;   // BNE
        3'b100: out =  LT;   // BLT
        3'b101: out = !LT;   // BGE
        3'b110: out =  LTU;  // BLTU
	3'b111: out = !LTU;  // BGEU
	default: out = 1'bx; // don't care...
      endcase
   end 
   
endmodule

/********************* Instruction decoder *******************************/

module NrvDecoder(
    input wire [31:0] instr,
    output wire [4:0] writeBackRegId,
    output reg 	      writeBackEn,
    output reg [3:0]  writeBackSel, // 0001: ALU  0010: PC+4  0100: RAM 1000: counters
		                    // (could use 2 wires instead, but using 4 wires (1-hot encoding) 
		                    //  reduces both LUT count and critical path in the end !)
    output wire [4:0] inRegId1,
    output wire [4:0] inRegId2,
    output reg 	      aluSel, // 0: force aluOp,aluQual to zero (ADD)  1: use aluOp,aluQual from instr field
    output reg 	      aluInSel1, // 0: reg  1: pc
    output reg 	      aluInSel2, // 0: reg  1: imm
    output [2:0]      aluOp,
    output reg 	      aluQual,
    output reg 	      aluM, // Asserted if operation is an RV32M operation
    output reg 	      isLoad,
    output reg 	      isStore,
    output reg 	      needWaitALU,
    output reg [2:0]  nextPCSel, // 001: PC+4  010: ALU  100: (predicate ? ALU : PC+4)
		                 // (same as writeBackSel, 1-hot encoding)
    output reg [31:0] imm,
    output reg 	      error
);

   reg inRegId1Sel; // 0: force inRegId1 to zero 1: use inRegId1 instr field

   // Reference:
   // https://content.riscv.org/wp-content/uploads/2017/05/riscv-spec-v2.2.pdf
   // See the table page 104


   // The beauty of RiscV: the instruction decoder is reasonably simple, because
   // - register ids and alu operation are always encoded in the same bits
   // - sign expansion for immediates is always done from bit 31, and minimum
   //   shuffling (nice compromise with register IDs and aluOp that are always
   //   the same bits). 

   // The control signals directly deduced from (fixed pos) fields
   
   assign writeBackRegId = instr[11:7];
   assign inRegId1       = instr[19:15] & {5{inRegId1Sel}}; // Internal sig InRegId1Sel used to force zero in reg1
   assign inRegId2       = instr[24:20];             // (because I'm making maximum reuse of the adder of the ALU)
   assign aluOp          = instr[14:12];  

   // The five immediate formats, see the RiscV reference, Fig. 2.4 p. 12
   // Note: they all do sign expansion (sign bit is instr[31]), except the U format
   wire [31:0] Iimm = {{21{instr[31]}}, instr[30:20]};
   wire [31:0] Simm = {{21{instr[31]}}, instr[30:25], instr[11:7]};
   wire [31:0] Bimm = {{20{instr[31]}}, instr[7], instr[30:25], instr[11:8], 1'b0};
   wire [31:0] Jimm = {{12{instr[31]}}, instr[19:12], instr[20], instr[30:21], 1'b0};   
   wire [31:0] Uimm = {instr[31], instr[30:12], {12{1'b0}}};

   // The rest of instruction decoding, for the following signals:
   // writeBackEn
   // writeBackSel   0001: ALU  0010: PC+4 0100: RAM 1000: counters
   // inRegId1Sel    0: zero   1: regId
   // aluInSel1      0: reg    1: PC 
   // aluInSel2      0: reg    1: imm
   // aluQual        +/- SRLI/SRAI
   // aluM           1 if instr is RV32M
   // aluSel         0: force aluOp,aluQual=00  1: use aluOp/aluQual
   // nextPCSel      001: PC+4  010: ALU   100: (pred ? ALU : PC+4)
   // imm (select one of Iimm,Simm,Bimm,Jimm,Uimm)

   // The beauty of RiscV (again !): in fact there are only 11 instructions !
   //
   // LUI, AUIPC, JAL, JALR
   // Branch variants
   // ALU register variants
   // ALU immediate variants
   // Load, Store 
   // Fence, System (not implemented)

   // We need to distingish shifts for two reasons:
   //  - We need to wait for ALU when it is a shift
   //  - For ALU ops with immediates, aluQual is 0, except
   //    for shifts (then it is instr[30]).
   wire aluOpIsShift = (aluOp == 3'b001) || (aluOp == 3'b101);
   
   always @(*) begin

       error = 1'b0;
       nextPCSel = 3'b001;  // default: PC <- PC+4
       inRegId1Sel = 1'b1; // reg 1 Id from instr
       isLoad = 1'b0;
       isStore = 1'b0;
       aluQual = 1'b0;
       needWaitALU = 1'b0;
       aluM    = 1'b0;
      
       (* parallel_case, full_case *)
       case(instr[6:0])
	   7'b0110111: begin // LUI
	      writeBackEn  = 1'b1;    // enable write back
	      writeBackSel = 4'b0001; // write back source = ALU
	      inRegId1Sel = 1'b0;     // reg 1 Id = 0
	      aluInSel1 = 1'b0;       // ALU source 1 = reg	      
	      aluInSel2 = 1'b1;       // ALU source 2 = imm
	      aluSel = 1'b0;          // ALU op = ADD
	      imm = Uimm;             // imm format = U
	   end
	 
	   7'b0010111: begin // AUIPC
	      writeBackEn  = 1'b1;    // enable write back
	      writeBackSel = 4'b0001; // write back source = ALU
	      inRegId1Sel = 1'bx;     // reg 1 Id : don't care (we use PC)	      
	      aluInSel1 = 1'b1;       // ALU source 1 = PC	      
	      aluInSel2 = 1'b1;       // ALU source 2 = imm
	      aluSel = 1'b0;          // ALU op = ADD
	      imm = Uimm;             // imm format = U
	   end
	 
	   7'b1101111: begin // JAL
	      writeBackEn  = 1'b1;    // enable write back
	      writeBackSel = 4'b0010; // write back source = PC+4
	      inRegId1Sel = 1'bx;     // reg 1 Id : don't care (we use PC)	      	      
	      aluInSel1 = 1'b1;       // ALU source 1 = PC	      
	      aluInSel2 = 1'b1;       // ALU source 2 = imm
	      aluSel = 1'b0;          // ALU op = ADD
	      nextPCSel = 3'b010;     // PC <- ALU	      
	      imm = Jimm;             // imm format = J
	   end
	 
	   7'b1100111: begin // JALR
	      writeBackEn  = 1'b1;    // enable write back
	      writeBackSel = 4'b0010; // write back source = PC+4
	      aluInSel1 = 1'b0;       // ALU source 1 = reg	      
	      aluInSel2 = 1'b1;       // ALU source 2 = imm
	      aluSel = 1'b0;          // ALU op = ADD
	      nextPCSel = 3'b010;     // PC <- ALU	      
	      imm = Iimm;             // imm format = I
	   end
	 
	   7'b1100011: begin // Branch
	      writeBackEn = 1'b0;     // disable write back
	      writeBackSel = 4'bxxxx; // write back source = don't care
	      aluInSel1 = 1'b1;       // ALU source 1 : PC
	      aluInSel2 = 1'b1;       // ALU source 2 : imm
	      aluSel = 1'b0;          // ALU op = ADD
	      nextPCSel = 3'b100;     // PC <- pred ? ALU : PC+4	       
	      imm = Bimm;             // imm format = B
	   end
	   
	   7'b0010011: begin // ALU operation: Register,Immediate
	      writeBackEn = 1'b1;     // enable write back
	      writeBackSel = 4'b0001; // write back source = ALU
	      aluInSel1 = 1'b0;       // ALU source 1 : reg
	      aluInSel2 = 1'b1;       // ALU source 2 : imm
	                              // Qualifier for ALU op: SRLI/SRAI
	      aluQual = aluOpIsShift ? instr[30] : 1'b0;
	      needWaitALU = aluOpIsShift;
	      aluSel = 1'b1;         // ALU op : from instr
	      imm = Iimm;            // imm format = I
	   end
	   
	   7'b0110011: begin // ALU operation: Register,Register
	      writeBackEn = 1'b1;     // enable write back
	      writeBackSel = 4'b0001; // write back source = ALU
	      aluInSel1 = 1'b0;       // ALU source 1 : reg
	      aluInSel2 = 1'b0;       // ALU source 2 : reg
	      aluQual = instr[30];    // Qualifier for ALU op: +/- SRL/SRA
	      aluSel = 1'b1;          // ALU op : from instr
`ifdef NRV_RV32M
	      needWaitALU = aluOpIsShift || instr[25];	
              aluM = instr[25];
`else
	      needWaitALU = aluOpIsShift;
	      error = instr[25];
`endif	      
	      imm = 32'bxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx; // don't care
	   end
	   
           7'b0000011: begin // Load
	      writeBackEn = 1'b1;     // enable write back
	      writeBackSel = 4'b0100; // write back source = RAM
	      aluInSel1 = 1'b0;       // ALU source 1 = reg
	      aluInSel2 = 1'b1;       // ALU source 2 = imm
	      aluSel = 1'b0;          // ALU op = ADD
	      imm = Iimm;             // imm format = I
	      isLoad = 1'b1;
	   end
	 
           7'b0100011: begin // Store
	      writeBackEn = 1'b0;     // disable write back
	      writeBackSel = 4'bxxxx; // write back sel = don't care
	      aluInSel1 = 1'b0;       // ALU source 1 = reg
	      aluInSel2 = 1'b1;       // ALU source 2 = imm
	      aluSel = 1'b0;          // ALU op = ADD
	      imm = Simm;             // imm format = S
	      isStore = 1'b1;
	   end
	    
	   /* 
	   7'b0001111: begin // Fence
	   end
	   7'b1110011: begin // System
	   end
	   */

`ifdef NRV_COUNTERS
	   7'b1110011: begin // System RDCYCLE[H], RDTIME[H] and RDINSTRET[H]
	      writeBackEn = 1'b1;
	      writeBackSel = 4'b1000; // write back sel = counter
	      inRegId1Sel = 1'bx; 
	      aluInSel1 = 1'bx;      
	      aluInSel2 = 1'bx;      
	      aluSel = 1'bx;      
	      imm = 32'bxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx;
	   end
`endif	 

           default: begin
	      writeBackEn = 1'b0;
	      error = 1'b1;
	      writeBackSel = 4'bxxxx;   
	      inRegId1Sel = 1'bx; 
	      aluInSel1 = 1'bx;      
	      aluInSel2 = 1'bx;      
	      aluSel = 1'bx;      
	      nextPCSel = 3'bxxx;  
	      imm = 32'bxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx;
	   end
       endcase
   end

endmodule

/********************* Nrv processor *******************************/

module FemtoRV32 #(
  parameter [0:0] RV32M              = 0, // Set to 1 to support mul/div/rem instructions		   
  parameter       ADDR_WIDTH         = 16 // width of the address bus
) (
   input 	     clk,

   // Memory interface: using the same protocol as Claire Wolf's picoR32
   //                   (WIP: add mem_valid / mem_ready protocol)
   output [31:0]     mem_addr, // address bus, only ADDR_WIDTH bits are used
   output reg [31:0] mem_wdata, // data to be written
   output reg [3:0]  mem_wstrb, // write mask for individual bytes (1 means write byte)   
   input [31:0]      mem_rdata, // input lines for both data and instr
   output reg 	     mem_instr, // active when reading instruction (and not when reading data)
   
   input wire 	     reset, // set to 0 to reset the processor
   output wire 	     error      // 1 if current instruction could not be decoded
);

   // The states, using 1-hot encoding (reduces
   // both LUT count and critical path).
   
   localparam INITIAL              = 8'b00000000;   
   localparam WAIT_INSTR           = 8'b00000001;
   localparam FETCH_INSTR          = 8'b00000010;
   localparam USE_PREFETCHED_INSTR = 8'b00000100;
   localparam FETCH_REGS           = 8'b00001000;
   localparam EXECUTE              = 8'b00010000;
   localparam WAIT_ALU_OR_DATA     = 8'b00100000;
   localparam LOAD                 = 8'b01000000;
   localparam ERROR                = 8'b10000000;

   localparam WAIT_INSTR_bit           = 0;
   localparam FETCH_INSTR_bit          = 1;
   localparam USE_PREFETCHED_INSTR_bit = 2;
   localparam FETCH_REGS_bit           = 3;
   localparam EXECUTE_bit              = 4;
   localparam WAIT_ALU_OR_DATA_bit     = 5;
   localparam LOAD_bit                 = 6;   
   localparam ERROR_bit                = 7;
   
   reg [7:0] state = INITIAL;

   // The internal register that stores the current address,
   // directly wired to the address bus.
   reg [ADDR_WIDTH-1:0] addressReg;

   // The program counter.
   reg [ADDR_WIDTH-3:0] PC;

`ifdef NRV_COUNTERS
 `ifdef NRV_COUNTERS_64   
   reg [63:0] 		counter_cycle;
   reg [63:0] 		counter_instret;
 `else
   reg [31:0] 		counter_cycle;
   reg [31:0] 		counter_instret;
 `endif   
`endif
   
   assign mem_addr = addressReg;

   reg [31:0] instr;     // Latched instruction. 
   reg [31:0] nextInstr; // Prefetched instruction.

 
   // Next program counter in normal operation: advance one word
   // I do not use the ALU, I create an additional adder for that.
   wire [ADDR_WIDTH-3:0] PCplus4 = PC + 1;

   // Internal signals, all generated by the decoder from the current instruction.
   wire [4:0] 	 writeBackRegId; // The register to be written back
   wire 	 writeBackEn;    // Needs to be asserted for writing back
   wire [3:0]	 writeBackSel;   // 0001: ALU  0010: PC+4  0100: RAM  1000: counters
   wire [4:0] 	 regId1;         // Register output 1
   wire [4:0] 	 regId2;         // Register output 2
   wire 	 aluInSel1;      // 0: register  1: pc
   wire 	 aluInSel2;      // 0: register  1: imm
   wire 	 aluSel;         // 0: force aluOp,aluQual to zero (ADD)  1: use aluOp,aluQual from instr field
   wire [2:0] 	 aluOp;          // one of the 8 operations done by the ALU
   wire 	 aluQual;        // 'qualifier' used by some operations (+/-, logical/arith shifts)
   wire          aluM;           // asserted if instr is RV32M.
   wire [2:0] 	 nextPCSel;      // 001: PC+4  010: ALU  100: (predicate ? ALU : PC+4)
   wire [31:0] 	 imm;            // immediate value decoded from the instruction
   wire          needWaitALU;    // asserted if instruction uses at least one additional phase in ALU
   wire 	 isLoad;         // guess what, true if instr is a load
   wire 	 isStore;        // guess what, true if instr is a store
   wire          decoderError;   // true if instr does not correspond to any known instr

   // The instruction decoder, that reads the current instruction 
   // and generates all the signals from it. It is in fact just a
   // big combinatorial function.
   
   NrvDecoder decoder(
     .instr(instr),		     
     .writeBackRegId(writeBackRegId),
     .writeBackEn(writeBackEn),
     .writeBackSel(writeBackSel),
     .inRegId1(regId1),
     .inRegId2(regId2),
     .aluInSel1(aluInSel1), 
     .aluInSel2(aluInSel2),
     .aluSel(aluSel),		     
     .aluOp(aluOp),
     .aluQual(aluQual),
     .aluM(aluM),		      
     .needWaitALU(needWaitALU),		      
     .isLoad(isLoad),
     .isStore(isStore),
     .nextPCSel(nextPCSel),
     .imm(imm),
     .error(decoderError)     		     
   );

   // Maybe not necessary, but I'd rather latch this one,
   // if this one glitches, then it will break everything...
   reg error_latched;
   assign error = error_latched;
   
   wire [31:0] aluOut;
   wire        aluBusy;
   wire	       writeBack = (state[EXECUTE_bit] && writeBackEn) || state[WAIT_ALU_OR_DATA_bit];
   
   // The register file. At each cycle, it can read two
   // registers (available at next cycle) and write one.
   reg  [31:0] writeBackData;
   wire [31:0] regOut1;
   wire [31:0] regOut2;   
   NrvRegisterFile regs(
    .clk(clk),
    .in(writeBackData),
    .inEn(writeBack),
    .inRegId(writeBackRegId),		       
    .outRegId1(regId1),
    .outRegId2(regId2),
    .out1(regOut1),
    .out2(regOut2) 
   );

   // The ALU, partly combinatorial, partly state (for shifts).
   wire [31:0] aluIn1 = aluInSel1 ? {PC, 2'b00} : regOut1;
   wire [31:0] aluIn2 = aluInSel2 ? imm : regOut2;
   
   generate
      if(RV32M) begin
         NrvLargeALU alu(
            .clk(clk),	      
            .in1(aluIn1),
            .in2(aluIn2),
            .op(aluOp & {3{aluSel}}),
            .opqual(aluQual & aluSel),
            .opM(aluM),	 
            .out(aluOut),
            .wr(state == EXECUTE), 
            .busy(aluBusy)	      
         );
      end else begin 
         NrvSmallALU #(
`ifdef NRV_TWOSTAGE_SHIFTER	      
          .TWOSTAGE_SHIFTER(1),
`else
          .TWOSTAGE_SHIFTER(0),	      
`endif
         ) alu(
            .clk(clk),	      
            .in1(aluIn1),
            .in2(aluIn2),
            .op(aluOp & {3{aluSel}}),
            .opqual(aluQual & aluSel),
            .out(aluOut),
            .wr(state == EXECUTE), 
            .busy(aluBusy)	      
         );
      end
   endgenerate
      
   // LOAD: decode datain based on type and address
   
   reg [31:0] decodedDataIn;   
   reg [15:0]  mem_rdata_H;
   reg [7:0]   mem_rdata_B;

   always @(*) begin
      (* parallel_case, full_case *)            
      case(mem_addr[1])
	1'b0: mem_rdata_H = mem_rdata[15:0];
	1'b1: mem_rdata_H = mem_rdata[31:16];
      endcase 
      
      (* parallel_case, full_case *)            
      case(mem_addr[1:0])
	2'b00: mem_rdata_B = mem_rdata[7:0];
	2'b01: mem_rdata_B = mem_rdata[15:8];
	2'b10: mem_rdata_B = mem_rdata[23:16];
	2'b11: mem_rdata_B = mem_rdata[31:24];
      endcase 

      // aluop[1:0] contains data size (00: byte, 01: half word, 10: word)
      // aluop[2] sign expansion toggle (0 = sign expansion, 1 = no sign expansion)
      (* parallel_case, full_case *)      
      case(aluOp[1:0])
	2'b00: decodedDataIn = {{24{aluOp[2]?1'b0:mem_rdata_B[7]}},mem_rdata_B};
	2'b01: decodedDataIn = {{16{aluOp[2]?1'b0:mem_rdata_H[15]}},mem_rdata_H};
	default: decodedDataIn = mem_rdata;
      endcase
   end

`ifdef NRV_COUNTERS
   reg [31:0] counter;
   always @(*) begin
      (* parallel_case, full_case *)      
      case(instr[31:20])
	12'b110000000000: counter = counter_cycle[31:0];    // CYCLE
	12'b110000000001: counter = counter_cycle[31:0];    // TIME
	12'b110000000010: counter = counter_instret[31:0];  // INSTRET
 `ifdef NRV_COUNTERS_64
	12'b110010000000: counter = counter_cycle[63:32];   // CYCLEH
	12'b110010000001: counter = counter_cycle[63:32];   // TIMEH
	12'b110010000010: counter = counter_instret[63:32]; // INSTRETH
 `endif
	default: counter = {32{1'bx}};
      endcase 
   end
`endif   
   
   // The value written back to the register file.
   always @(*) begin
      (* parallel_case, full_case *)
      case(1'b1)
	writeBackSel[0]: writeBackData = aluOut;
	writeBackSel[1]: writeBackData = {PCplus4, 2'b00};
	writeBackSel[2]: writeBackData = decodedDataIn;
`ifdef NRV_COUNTERS
	writeBackSel[3]: writeBackData = counter;	
`endif
      endcase
   end

   // The predicate for conditional branches. 
   wire predOut;
   NrvPredicate pred(
    .in1(regOut1),
    .in2(regOut2),
    .op(aluOp),
    .out(predOut)		    
   );

`ifdef NRV_COUNTERS
   always @(posedge clk) begin
      if(!reset) begin	    
	 counter_instret <= 0;
	 counter_cycle   <= 0;
      end else begin
	 counter_cycle <= counter_cycle+1;
	 if(state[FETCH_REGS_bit]) begin
	    counter_instret <= counter_instret+1;
	 end
      end
   end
`endif
   
   always @(posedge clk) begin
      `verbose($display("state = %h",state));
      if(!reset) begin
	 state <= INITIAL;
	 mem_instr <= 1'b1;
	 mem_wstrb <= 4'b0000;
	 addressReg <= 0;
	 PC <= 0;
      end else
      case(1'b1)
	(state == 0): begin
	   `verbose($display("INITIAL"));
	   state <= WAIT_INSTR;
	end
	state[WAIT_INSTR_bit]: begin
	   // this state to give enough time to fetch the 
	   // instruction. Used for jumps and taken branches (and 
	   // when fetching the first instruction). 
	   `verbose($display("WAIT_INSTR"));
	   state <= FETCH_INSTR;
	end
	state[FETCH_INSTR_bit]: begin
	   `verbose($display("FETCH_INSTR"));	   
	   instr <= mem_rdata;
	   // update instr address so that next instr is fetched during
	   // decode (and ready if there was no jump or branch)
	   addressReg <= {PCplus4, 2'b00}; 
	   state <= FETCH_REGS;
	end
	state[USE_PREFETCHED_INSTR_bit]: begin
	   `verbose($display("USE_PREFETCHED_INSTR"));	   
	   instr <= nextInstr;
	   // update instr address so that next instr is fetched during
	   // decode (and ready if there was no jump or branch)
	   addressReg <= {PCplus4, 2'b00}; 
	   state <= FETCH_REGS;
	   mem_wstrb <= 4'b0000;
	end
	state[FETCH_REGS_bit]: begin
	   // instr was just updated -> input register ids also
	   // input registers available at next cycle 
	   state <= EXECUTE;
	   error_latched <= decoderError;
	end
	state[EXECUTE_bit]: begin
	   // input registers are read, aluOut is up to date
	   
	   // Lookahead instr.
	   nextInstr <= mem_rdata;

	   // Needed for LOAD,STORE,jump,branch
	   // (in other cases it will be ignored)
	   addressReg <= aluOut; 
	   
	   if(error_latched) begin
	      state <= ERROR;
	   end else if(isLoad) begin
	      state <= LOAD;
	      PC <= PCplus4;
	      mem_instr <= 1'b0;
	   end else if(isStore) begin
	      state <= USE_PREFETCHED_INSTR; // Data will be written in USE_PREFETCHED_INSTR
	      PC <= PCplus4;
	      case(aluOp[1:0])
		2'b00: begin
		   case(aluOut[1:0]) // Address is now in aluOut (and not in mem_address yet !!)
		     2'b00: begin
			mem_wstrb <= 4'b0001;
			mem_wdata <= {24'bxxxxxxxxxxxxxxxxxxxxxxxx,regOut2[7:0]};
		     end
		     2'b01: begin
			mem_wstrb <= 4'b0010;
			mem_wdata <= {16'bxxxxxxxxxxxxxxxx,regOut2[7:0],8'bxxxxxxxx};
		     end
		     2'b10: begin
			mem_wstrb <= 4'b0100;
			mem_wdata <= {8'bxxxxxxxx,regOut2[7:0],16'bxxxxxxxxxxxxxxxx};
		     end
		     2'b11: begin
			mem_wstrb <= 4'b1000;
			mem_wdata <= {regOut2[7:0],24'bxxxxxxxxxxxxxxxxxxxxxxxx};
		     end
		   endcase
		end
		2'b01: begin
		   case(aluOut[1]) // Address is now in aluOut (and not in mem_address yet !!)
		     1'b0: begin
			mem_wstrb <= 4'b0011;
			mem_wdata <= {16'bxxxxxxxxxxxxxxxx,regOut2[15:0]};
		     end
		     1'b1: begin
			mem_wstrb <= 4'b1100;
			mem_wdata <= {regOut2[15:0],16'bxxxxxxxxxxxxxxxx};
		     end
		   endcase
		end
		2'b10: begin
		   mem_wstrb <= 4'b1111;
		   mem_wdata <= regOut2;
		end
		default: begin
		   mem_wstrb <= 4'bxxxx;
		   mem_wdata <= 32'bxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx;
		end
	      endcase 
	   end else begin 
	      (* parallel_case, full_case *)
	      case(1'b1)
		nextPCSel[0]: begin // normal operation
		   PC <= PCplus4;
		   state <= needWaitALU ? WAIT_ALU_OR_DATA : USE_PREFETCHED_INSTR;
		end		   
		nextPCSel[1]: begin // unconditional jump (JAL, JALR)
		   PC <= aluOut[31:2];
		   state <= WAIT_INSTR;
		end
		nextPCSel[2]: begin // branch
		   if(predOut) begin
		      PC <= aluOut[31:2];
		      state <= WAIT_INSTR;
		   end else begin
		      PC <= PCplus4;
		      state <= USE_PREFETCHED_INSTR;
		   end
		end
	      endcase 
	   end 
	end
	state[LOAD_bit]: begin
	   `verbose($display("LOAD"));
	   // data address (aluOut) was just updated
	   // data ready at next cycle
	   // we go to WAIT_ALU_OR_DATA to write back read data
	   state <= WAIT_ALU_OR_DATA;
	   mem_instr <= 1'b1;
	end
	state[WAIT_ALU_OR_DATA_bit]: begin
	   `verbose($display("WAIT_ALU_OR_DATA"));	   
	   // - If ALU is still busy, continue to wait.
	   // - register writeback is active
	   state <= aluBusy ? WAIT_ALU_OR_DATA : USE_PREFETCHED_INSTR;
	end
	state[ERROR_bit]: begin
	   `bench($display("ERROR"));
           state <= ERROR;
	end
	default: begin
	   `bench($display("UNKNOWN STATE"));	   	   	   
	   state <= ERROR;
	end
      endcase
  end   
   
endmodule

