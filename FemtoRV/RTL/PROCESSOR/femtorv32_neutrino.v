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

module FemtoRV32E(
    input         clk,

    output [31:0] mem_addr,  // address bus
    output [31:0] mem_wdata, // data to be written
    output [3:0]  mem_wmask, // write mask
    input  [31:0] mem_rdata, // read data
    output        mem_rstrb, // read strobe
    input         mem_rbusy, // read busy
    input         mem_wbusy, // write busy

    input         reset      // active-low reset
);
    parameter RESET_ADDR = 32'h00000000;
    parameter ADDR_WIDTH = 24;

    /***************************************************************************/
    // Instruction decoding.
    /***************************************************************************/
    // Extract rd, rs1, rs2, funct3, imm, and opcode as before.
    wire [4:0] rawRdId  = instr[11:7];
    wire [4:0] rawRs1Id = instr[19:15];
    wire [4:0] rawRs2Id = instr[24:20];

    // For RV32E, only bits [3:0] are valid. If the high bit is set,
    // we treat it as an invalid register and ignore it.
    wire       rdValid  = ~rawRdId[4];
    wire       rs1Valid = ~rawRs1Id[4];
    wire       rs2Valid = ~rawRs2Id[4];

    wire [3:0] rdId     = rawRdId[3:0];
    wire [3:0] rs1Id    = rawRs1Id[3:0];
    wire [3:0] rs2Id    = rawRs2Id[3:0];

    // The usual breakdown of ALU signals and immediates remains the same.
    (* onehot *) wire [7:0] funct3Is = 8'b00000001 << instr[14:12];

    wire [31:0] Uimm = {    instr[31],   instr[30:12],  {12{1'b0}}};
    wire [31:0] Iimm = {{21{instr[31]}}, instr[30:20]};
    wire [31:0] Simm = {{21{instr[31]}}, instr[30:25], instr[11:7]};
    wire [31:0] Bimm = {{20{instr[31]}}, instr[7], instr[30:25], instr[11:8], 1'b0};
    wire [31:0] Jimm = {{12{instr[31]}}, instr[19:12], instr[20], instr[30:21], 1'b0};

    // Identify the 10 base opcodes (RV32I/E).
    wire isLoad    = (instr[6:2] == 5'b00000);
    wire isALUimm  = (instr[6:2] == 5'b00100);
    wire isStore   = (instr[6:2] == 5'b01000);
    wire isALUreg  = (instr[6:2] == 5'b01100);
    wire isSYSTEM  = (instr[6:2] == 5'b11100);
    wire isJAL     = instr[3];  // same as (instr[6:2] == 5'b11011)
    wire isJALR    = (instr[6:2] == 5'b11001);
    wire isLUI     = (instr[6:2] == 5'b01101);
    wire isAUIPC   = (instr[6:2] == 5'b00101);
    wire isBranch  = (instr[6:2] == 5'b11000);

    wire isALU = isALUimm | isALUreg;

    /***************************************************************************/
    // Register file (16 registers, x0..x15).
    /***************************************************************************/
    reg [31:0] rs1;
    reg [31:0] rs2;

    // 16 registers only.
    (* no_rw_check *) reg [31:0] registerFile [15:0];

    always @(posedge clk) begin
        // Write-back only if rd is valid and not x0.
        if (writeBack && rdValid && (rdId != 4'h0)) begin
        registerFile[rdId] <= writeBackData;
        end
    end

    /***************************************************************************/
    // ALU logic and control signals remain the same.
    /***************************************************************************/
    wire [31:0] aluIn1 = rs1;
    wire [31:0] aluIn2 = isALUreg | isBranch ? rs2 : Iimm;

    reg  [31:0] aluReg;
    reg  [4:0]  aluShamt;

    wire aluBusy = |aluShamt;
    wire aluWr   = state[EXECUTE_bit] & isALU;

    wire [31:0] aluPlus  = aluIn1 + aluIn2;
    wire [32:0] aluMinus = {1'b1, ~aluIn2} + {1'b0, aluIn1} + 33'b1;
    wire        LT  = (aluIn1[31] ^ aluIn2[31]) ? aluIn1[31] : aluMinus[32];
    wire        LTU = aluMinus[32];
    wire        EQ  = (aluMinus[31:0] == 0);

    wire [31:0] aluOut =
        (funct3Is[0] ? (instr[30] & instr[5] ? aluMinus[31:0] : aluPlus) : 32'b0)
        | (funct3Is[2] ? {31'b0, LT}                                  : 32'b0)
        | (funct3Is[3] ? {31'b0, LTU}                                 : 32'b0)
        | (funct3Is[4] ? aluIn1 ^ aluIn2                              : 32'b0)
        | (funct3Is[6] ? aluIn1 | aluIn2                              : 32'b0)
        | (funct3Is[7] ? aluIn1 & aluIn2                              : 32'b0)
        | (funct3IsShift ? aluReg                                    : 32'b0);

    wire funct3IsShift = funct3Is[1] | funct3Is[5];

    always @(posedge clk) begin
        if (aluWr) begin
        if (funct3IsShift) begin
            aluReg   <= aluIn1;
            aluShamt <= aluIn2[4:0];
        end
        end
    `ifdef NRV_TWOLEVEL_SHIFTER
        else if(|aluShamt[4:2]) begin
        aluShamt <= aluShamt - 4;
        aluReg   <= funct3Is[1] ? (aluReg << 4)
                                : {{4{instr[30] & aluReg[31]}}, aluReg[31:4]};
        end
    `endif
        if(|aluShamt) begin
        aluShamt <= aluShamt - 1;
        aluReg   <= funct3Is[1] ? (aluReg << 1)
                                : {instr[30] & aluReg[31], aluReg[31:1]};
        end
    end

    wire predicate =
        (funct3Is[0] &  EQ)   // BEQ
        | (funct3Is[1] & ~EQ)   // BNE
        | (funct3Is[4] &  LT)   // BLT
        | (funct3Is[5] & ~LT)   // BGE
        | (funct3Is[6] &  LTU)  // BLTU
        | (funct3Is[7] & ~LTU); // BGEU

    /***************************************************************************/
    // Program counter and the state machine remain the same.
    /***************************************************************************/
    reg  [ADDR_WIDTH-1:0] PC;
    reg  [31:2]           instr;

    wire [ADDR_WIDTH-1:0] PCplus4   = PC + 4;
    wire [ADDR_WIDTH-1:0] PCplusImm = PC + (
        instr[3] ? Jimm[ADDR_WIDTH-1:0] :
        instr[4] ? Uimm[ADDR_WIDTH-1:0] : Bimm[ADDR_WIDTH-1:0]
    );

    wire [ADDR_WIDTH-1:0] loadstore_addr =
        rs1[ADDR_WIDTH-1:0] + (instr[5] ? Simm[ADDR_WIDTH-1:0] : Iimm[ADDR_WIDTH-1:0]);

    assign mem_addr = (state[WAIT_INSTR_bit] | state[FETCH_INSTR_bit]) ? PC
                                                                        : loadstore_addr;

    /***************************************************************************/
    // Write-back data multiplexer.
    /***************************************************************************/
    wire [31:0] writeBackData =
        (isSYSTEM ? cycles    : 32'b0)
        | (isLUI    ? Uimm      : 32'b0)
        | (isALU    ? aluOut    : 32'b0)
        | (isAUIPC  ? PCplusImm : 32'b0)
        | ((isJALR | isJAL) ? PCplus4 : 32'b0)
        | (isLoad   ? LOAD_data : 32'b0);

    /***************************************************************************/
    // Load/store byte/halfword logic is unchanged.
    /***************************************************************************/
    wire mem_byteAccess     = (instr[13:12] == 2'b00);
    wire mem_halfwordAccess = (instr[13:12] == 2'b01);

    wire LOAD_sign =
        !instr[14] & (mem_byteAccess ? LOAD_byte[7] : LOAD_halfword[15]);

    wire [31:0] LOAD_data =
            mem_byteAccess     ? {{24{LOAD_sign}}, LOAD_byte}
        : mem_halfwordAccess ? {{16{LOAD_sign}}, LOAD_halfword}
        : mem_rdata;

    wire [15:0] LOAD_halfword =
        loadstore_addr[1] ? mem_rdata[31:16] : mem_rdata[15:0];

    wire [7:0] LOAD_byte =
        loadstore_addr[0] ? LOAD_halfword[15:8] : LOAD_halfword[7:0];

    assign mem_wdata[7:0]   = rs2[7:0];
    assign mem_wdata[15:8]  = loadstore_addr[0] ? rs2[7:0]  : rs2[15:8];
    assign mem_wdata[23:16] = loadstore_addr[1] ? rs2[7:0]  : rs2[23:16];
    assign mem_wdata[31:24] = loadstore_addr[0] ? rs2[7:0]  :
                                loadstore_addr[1] ? rs2[15:8] : rs2[31:24];

    wire [3:0] STORE_wmask =
        mem_byteAccess      ?
            (loadstore_addr[1] ?
                (loadstore_addr[0] ? 4'b1000 : 4'b0100) :
                (loadstore_addr[0] ? 4'b0010 : 4'b0001)) :
        mem_halfwordAccess ?
            (loadstore_addr[1] ? 4'b1100 : 4'b0011) :
        4'b1111;

    /***************************************************************************/
    // Finite state machine (unchanged).
    /***************************************************************************/
    localparam FETCH_INSTR_bit     = 0;
    localparam WAIT_INSTR_bit      = 1;
    localparam EXECUTE_bit         = 2;
    localparam WAIT_ALU_OR_MEM_bit = 3;
    localparam NB_STATES           = 4;

    localparam FETCH_INSTR     = 1 << FETCH_INSTR_bit;
    localparam WAIT_INSTR      = 1 << WAIT_INSTR_bit;
    localparam EXECUTE         = 1 << EXECUTE_bit;
    localparam WAIT_ALU_OR_MEM = 1 << WAIT_ALU_OR_MEM_bit;

    (* onehot *) reg [NB_STATES-1:0] state;

    wire writeBack  = ~(isBranch | isStore) &
                        (state[EXECUTE_bit] | state[WAIT_ALU_OR_MEM_bit]);
    assign mem_rstrb = (state[EXECUTE_bit] & isLoad) | state[FETCH_INSTR_bit];
    assign mem_wmask = {4{state[EXECUTE_bit] & isStore}} & STORE_wmask;

    `ifdef NRV_IS_IO_ADDR
    wire needToWait =
        isLoad | (isStore & `NRV_IS_IO_ADDR(mem_addr)) | (isALU & funct3IsShift);
    `else
    wire needToWait = isLoad | isStore | (isALU & funct3IsShift);
    `endif
    wire jumpToPCplusImm = isJAL | (isBranch & predicate);

    always @(posedge clk) begin
        if(!reset) begin
        state <= WAIT_ALU_OR_MEM; // wait for !mem_wbusy
        PC    <= RESET_ADDR[ADDR_WIDTH-1:0];
        end else begin
        case(1'b1)

            state[WAIT_INSTR_bit]: begin
            if(!mem_rbusy) begin
                // In RV32E, if rs1 or rs2 are invalid, we read x0 instead.
                rs1   <= rs1Valid ? registerFile[rs1Id] : 32'b0;
                rs2   <= rs2Valid ? registerFile[rs2Id] : 32'b0;
                instr <= mem_rdata[31:2];
                state <= EXECUTE;
            end
            end

            state[EXECUTE_bit]: begin
            PC    <= isJALR          ? {aluPlus[ADDR_WIDTH-1:1],1'b0} :
                        jumpToPCplusImm ? PCplusImm : PCplus4;
            state <= needToWait ? WAIT_ALU_OR_MEM : FETCH_INSTR;
            end

            state[WAIT_ALU_OR_MEM_bit]: begin
            if(!aluBusy & !mem_rbusy & !mem_wbusy) begin
                state <= FETCH_INSTR;
            end
            end

            default: begin // FETCH_INSTR
            state <= WAIT_INSTR;
            end

        endcase
        end
    end

    /***************************************************************************/
    // Cycle counter remains the same (RDCYCLE).
    /***************************************************************************/
    `ifdef NRV_COUNTER_WIDTH
    reg [`NRV_COUNTER_WIDTH-1:0] cycles;
    `else
    reg [31:0] cycles;
    `endif
    always @(posedge clk) cycles <= cycles + 1;

    `ifdef BENCH
    initial begin
        cycles      = 0;
        aluShamt    = 0;
        registerFile[0] = 0;
    end
    `endif

    endmodule
