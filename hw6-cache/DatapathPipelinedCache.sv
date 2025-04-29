`timescale 1ns / 1ns

// registers are 32 bits in RV32
`define REG_SIZE 31:0

// insns are 32 bits in RV32IM
`define INSN_SIZE 31:0

// RV opcodes are 7 bits
`define OPCODE_SIZE 6:0

`define ADDR_WIDTH 32
`define DATA_WIDTH 32

`ifndef DIVIDER_STAGES
`define DIVIDER_STAGES 8
`endif

`ifndef SYNTHESIS
  `include "../hw3-singlecycle/RvDisassembler.sv"
`endif
`include "../hw2b-cla/cla.sv"
`include "../hw4-multicycle/DividerUnsignedPipelined.sv"
`include "../hw5-pipelined/cycle_status.sv"
`include "AxilCache_ref.sv"

module Disasm #(
    PREFIX = "D"
) (
    input wire [31:0] insn,
    output wire [(8*32)-1:0] disasm
);
`ifndef RISCV_FORMAL
`ifndef SYNTHESIS
  // this code is only for simulation, not synthesis
  string disasm_string;
  always_comb begin
    disasm_string = rv_disasm(insn);
  end
  // HACK: get disasm_string to appear in GtkWave, which can apparently show only wire/logic. Also,
  // string needs to be reversed to render correctly.
  genvar i;
  for (i = 3; i < 32; i = i + 1) begin : gen_disasm
    assign disasm[((i+1-3)*8)-1-:8] = disasm_string[31-i];
  end
  assign disasm[255-:8] = PREFIX;
  assign disasm[247-:8] = ":";
  assign disasm[239-:8] = " ";
`endif
`endif
endmodule

// TODO: copy over your RegFile and pipeline structs from HW5


module RegFile (
    input logic [4:0] rd,
    input logic [`REG_SIZE] rd_data,
    input logic [4:0] rs1,
    output logic [`REG_SIZE] rs1_data,
    input logic [4:0] rs2,
    output logic [`REG_SIZE] rs2_data,

    input logic clk,
    input logic we,
    input logic rst
);
  localparam int NumRegs = 32;
  logic [`REG_SIZE] regs[NumRegs];

   // regs[0] (x0) is always 0
  assign regs[0] = 0;

  // output the data for the read ports
  assign rs1_data = regs[rs1];
  assign rs2_data = regs[rs2];
  
  // check if the clk is at its rising edge
  always_ff @(posedge clk) begin 
    if (rst) begin
      regs <= '{default: '0};
      // for (i = 1; i < NumRegs; i ++) begin
      //   regs[i] <= 0;
      // end
    end else if (we && (rd != 0)) begin
      regs[rd] <= rd_data;
    end
  end

endmodule

// Struct to store insn signal
typedef struct packed {

  // misc and jump insns
  logic insn_lui;
  logic insn_auipc;
  logic insn_jal;
  logic insn_jalr;

  // branch insns
  logic insn_beq;
  logic insn_bne;
  logic insn_blt;
  logic insn_bge;
  logic insn_bltu;
  logic insn_bgeu;

  // load insns
  logic insn_lb;
  logic insn_lh;
  logic insn_lw;
  logic insn_lbu;
  logic insn_lhu;

  // store insns
  logic insn_sb;
  logic insn_sh;
  logic insn_sw;

  // immediate insns
  logic insn_addi;
  logic insn_slti;
  logic insn_sltiu;
  logic insn_xori;
  logic insn_ori;
  logic insn_andi;
  logic insn_slli;
  logic insn_srli;
  logic insn_srai;

  // regreg insns
  logic insn_add;
  logic insn_sub ;
  logic insn_sll ;
  logic insn_slt;
  logic insn_sltu ;
  logic insn_xor ;
  logic insn_srl;
  logic insn_sra;
  logic insn_or;
  logic insn_and;
  logic insn_mul;
  logic insn_mulh;
  logic insn_mulhsu;
  logic insn_mulhu;
  logic insn_div;
  logic insn_divu;
  logic insn_rem;
  logic insn_remu;

  // more misc insns
  logic insn_ecall;
  logic insn_fence;
} insn_key;

/** state at the start of Decode stage */
typedef struct packed {
  logic [`REG_SIZE] pc;
  //logic [`INSN_SIZE] insn;
  cycle_status_e cycle_status;  
} stage_decode_t;

/** state at the start of Execute stage **/
typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`INSN_SIZE] insn;
  cycle_status_e cycle_status;

  logic [`OPCODE_SIZE] opcode;
  
  logic [4:0] insn_rd;

  logic [11:0] imm_i;
  logic [11:0] imm_s;
  logic [12:0] imm_b;
  logic [20:0] imm_j;
  
  logic [`REG_SIZE] imm_i_sext;
  logic [`REG_SIZE] imm_s_sext;
  logic [`REG_SIZE] imm_b_sext;
  logic [`REG_SIZE] imm_j_sext;

  logic [19:0] imm_u;

  // data taken from register file
  logic [`REG_SIZE] rs1_data;
  logic [`REG_SIZE] rs2_data;

  logic [4:0] insn_rs1;
  logic [4:0] insn_rs2;
  

  // insn_key containing the insn signal
  insn_key insn_set;

  logic halt;


} stage_execute_t;

/** state at the start of Memory stage **/

typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`INSN_SIZE] insn;
  cycle_status_e cycle_status;
  logic [`OPCODE_SIZE] opcode;

  // register signals
  logic [4:0] insn_rd;
  logic [`REG_SIZE] rd_data;
  logic we;


  // // memory signals
  logic [`REG_SIZE] addr_to_dmem;
  logic [`REG_SIZE] store_data_to_dmem;
  logic [3:0] store_we_to_dmem;

  logic [`REG_SIZE] rs2_data;
  logic [4:0] insn_rs2;

  // branch signal
  logic [`REG_SIZE] branched_pc; // represents the pc value that will be branched to IF there is a branch
  logic branch_taken; // 1: branch, 0: no branch

  //insn_key insn_set;
  insn_key insn_set;
  logic halt;
} stage_memory_t;

/** state at the start of Write stage **/

typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`INSN_SIZE] insn;
  cycle_status_e cycle_status;
  logic [`OPCODE_SIZE] opcode;

  // register signals
  logic [4:0] insn_rd;
  logic [`REG_SIZE] rd_data;
  logic we;

  insn_key insn_set;
  logic [1:0] mem_bytes;

  logic halt;
} stage_write_t;

module DatapathPipelinedCache (
    input wire clk,
    input wire rst,

    // AXIL interface to insn memory
    axi_if.manager icache,
    // AXIL interface to data memory/cache
    axi_if.manager dcache,

    output logic halt,

    // The PC of the insn currently in Writeback. 0 if not a valid insn.
    output logic [`REG_SIZE] trace_writeback_pc,
    // The bits of the insn currently in Writeback. 0 if not a valid insn.
    output logic [`INSN_SIZE] trace_writeback_insn,
    // The status of the insn (or stall) currently in Writeback. See the cycle_status.sv file for valid values.
    output cycle_status_e trace_writeback_cycle_status
);

  // localparam bit True = 1'b1;
  // localparam bit False = 1'b0;

  // cycle counter
  logic [`REG_SIZE] cycles_current;
  always_ff @(posedge clk) begin
    if (rst) begin
      cycles_current <= 0;
    end else begin
      cycles_current <= cycles_current + 1;
    end
  end

  // TODO: copy in your HW5B datapath as a starting point

  // opcodes - see section 19 of RiscV spec
  localparam bit [`OPCODE_SIZE] OpLoad = 7'b00_000_11;
  localparam bit [`OPCODE_SIZE] OpStore = 7'b01_000_11;
  localparam bit [`OPCODE_SIZE] OpBranch = 7'b11_000_11;
  localparam bit [`OPCODE_SIZE] OpJalr = 7'b11_001_11;
  localparam bit [`OPCODE_SIZE] OpMiscMem = 7'b00_011_11;
  localparam bit [`OPCODE_SIZE] OpJal = 7'b11_011_11;

  localparam bit [`OPCODE_SIZE] OpRegImm = 7'b00_100_11;
  localparam bit [`OPCODE_SIZE] OpRegReg = 7'b01_100_11;
  localparam bit [`OPCODE_SIZE] OpEnviron = 7'b11_100_11;

  localparam bit [`OPCODE_SIZE] OpAuipc = 7'b00_101_11;
  localparam bit [`OPCODE_SIZE] OpLui = 7'b01_101_11;

  // ALL MODULES

  // REGFILE
  // WE, rd, and rd_data should come from the WRITE stage
  RegFile rf (
    .clk(clk),
    .rst(rst),
    .we(w_we),
    .rd(w_insn_rd),
    .rd_data(w_rd_data),
    .rs1(d_insn_rs1),
    .rs2(d_insn_rs2),
    .rs1_data(d_rs1_data_temp),
    .rs2_data(d_rs2_data_temp));


  // CLA inputs
  logic [31:0] cla_a;
  logic [31:0] cla_b;
  logic cla_cin;
  logic [31:0] cla_sum;

  assign cla_a = x_rs1_data;
  
  // determine b and cin for the cla
  always_comb begin
    cla_b = x_rs2_data;
    cla_cin = 0;
    
    if (x_insn_key.insn_sub) begin
      cla_b = ~x_rs2_data;
      cla_cin = 1;
    end else if (x_insn_key.insn_addi || x_opcode == OpLoad) begin
      // addi and load insns use rs1 + sext(imm12)
      cla_b = x_imm_i_sext;
    end else if (x_opcode == OpStore) begin
      cla_b = x_imm_s_sext;
    end
  end

  cla adder(.a(cla_a), .b(cla_b), .cin(cla_cin), .sum(cla_sum));

  // intermediary for multiplier instructions
  logic [63:0] multiple;
  logic [31:0] product_temp;

  // division vars

  wire [31:0] signed_quotient;
  wire [31:0] signed_remainder;
  
  wire [31:0] unsigned_divisor;
  wire [31:0] unsigned_dividend;
  wire [31:0] unsigned_quotient;
  wire [31:0] unsigned_remainder;

  // convert dividend and divisor to unsigned
  assign unsigned_dividend = x_rs1_data[31] ? (~x_rs1_data + 1) : x_rs1_data;
  assign unsigned_divisor = x_rs2_data[31] ? (~x_rs2_data + 1) : x_rs2_data;

  logic [31:0] dividend;
  logic [31:0] divisor;
  always_comb begin
    dividend = x_rs1_data;
    divisor = x_rs2_data;
    if (x_insn_key.insn_div || x_insn_key.insn_rem) begin
      dividend = unsigned_dividend;
      divisor = unsigned_divisor;
    end
  end

  // convert outputs from unsigned division to be signed
  assign signed_quotient = (div_sign_7) ? (~unsigned_quotient + 1) : unsigned_quotient;
  assign signed_remainder = (dividend_sign_7) ? (~unsigned_remainder + 1) : unsigned_remainder;

  // need to wait 8 cycles to run
  DividerUnsignedPipelined divider(.clk(clk), .rst(rst), .stall(0), 
          .i_dividend(dividend), .i_divisor(divisor), 
          .o_quotient(unsigned_quotient), .o_remainder(unsigned_remainder));

  // DIVIDER CONTROL SIGNALS

  // number of cycles the latest div has been executing
  logic [2:0] div_count_latest;

  // number of cycles the first div in a chain has been executing
  logic [2:0] div_count_first;

  // if div_count_latest < div_count_first && div_count_first == 7 => div_count_first <= 7
  // Since there can't be any stalls in a chain of divides, we need to keep treating the divider output as 
  // a real insn

  // the divider output only gets passed onto the memory stage if div_count_first == 7
  
  // whether there is a divide insn in decode
  logic d_div_insn;
  assign d_div_insn = d_insn_key.insn_div || d_insn_key.insn_divu || d_insn_key.insn_rem || d_insn_key.insn_remu;

  // whether there is a divide insn in execute
  logic x_div_insn;
  assign x_div_insn = x_insn_key.insn_div || x_insn_key.insn_divu || x_insn_key.insn_rem || x_insn_key.insn_remu;

  // whether to stall for a divide insn
  logic div_stall;

  // INITIAL STALL if divide in execute && (no divide in decode || data dependent divide in decode)
  // if there is a STALL, the values will be stay the same in execute stage, so data dependency will remain
  assign div_stall = x_div_insn && 
                    (~d_div_insn || (x_insn_rd == d_insn_rs1 || x_insn_rd == d_insn_rs2)) && 
                    div_count_latest != 0;

  // we should NOT stall when div_count_latest == 0, since that is when we are reading out our divider

  always_ff @(posedge clk) begin
    div_count_first <= 0;
    div_count_latest <= 0;
    if (rst) begin
      div_count_first <= 0;
      div_count_latest <= 0;
    end else begin
      
      // div_count_first
      if (div_count_latest > div_count_first && div_count_first == 0) begin
        div_count_first <= 0;
      end else if (d_div_insn || x_div_insn) begin
        div_count_first <= div_count_first + 1;
      end

      // div_count_latest
      if (div_stall) begin
        div_count_latest <= div_count_latest + 1;
      end else if (d_div_insn || x_div_insn) begin
        // a new divide insn is being put into the divider
        div_count_latest <= 1;
      end
    end
  end

  // // Create 7 registers to hold important values through the divide datapath
  logic div_by_zero_1;
  logic div_sign_1;
  logic dividend_sign_1;

  logic [`REG_SIZE] div_pc_1; // probably unnecessary
  logic [`REG_SIZE] div_insn_1; // probably unnecessary
  logic [4:0] div_insn_rd_1; // NECESSARY

  always_ff @(posedge clk) begin
    if (rst) begin
      div_by_zero_1 <= 0;
      div_sign_1 <= 0;
      dividend_sign_1 <= 0;
      div_pc_1 <= 0;
      div_insn_1 <= 0;
      div_insn_rd_1 <= 0;
    end else begin
      div_by_zero_1 <= x_rs2_data == 0;
      div_sign_1 <= x_rs1_data[31] ^ x_rs2_data[31];
      dividend_sign_1 <= x_rs1_data[31];
      div_pc_1 <= x_pc;
      div_insn_1 <= x_insn;
      div_insn_rd_1 <= x_insn_rd;
    end
  end

  logic div_by_zero_2;
  logic div_sign_2;
  logic dividend_sign_2;

  logic [`REG_SIZE] div_pc_2;
  logic [`REG_SIZE] div_insn_2;
  logic [4:0] div_insn_rd_2;

  always_ff @(posedge clk) begin
    if (rst) begin
      div_by_zero_2 <= 0;
      div_sign_2 <= 0;
      dividend_sign_2 <= 0;
      div_pc_2 <= 0;
      div_insn_2 <= 0;
      div_insn_rd_2 <= 0;
    end else begin
      div_by_zero_2 <= div_by_zero_1;
      div_sign_2 <= div_sign_1;
      dividend_sign_2 <= dividend_sign_1;
      div_pc_2 <= div_pc_1;
      div_insn_2 <= div_insn_1;
      div_insn_rd_2 <= div_insn_rd_1;
    end
  end

  logic div_by_zero_3;
  logic div_sign_3;
  logic dividend_sign_3;
  logic [`REG_SIZE] div_pc_3;
  logic [`REG_SIZE] div_insn_3;
  logic [4:0] div_insn_rd_3;

  always_ff @(posedge clk) begin
    if (rst) begin
      div_by_zero_3 <= 0;
      div_sign_3 <= 0;
      dividend_sign_3 <= 0;
      div_pc_3 <= 0;
      div_insn_3 <= 0;
      div_insn_rd_3 <= 0;
    end else begin
      div_by_zero_3 <= div_by_zero_2;
      div_sign_3 <= div_sign_2;
      dividend_sign_3 <= dividend_sign_2;
      div_pc_3 <= div_pc_2;
      div_insn_3 <= div_insn_2;
      div_insn_rd_3 <= div_insn_rd_2;
    end
  end

  logic div_by_zero_4;
  logic div_sign_4;
  logic dividend_sign_4;
  logic [`REG_SIZE] div_pc_4;
  logic [`REG_SIZE] div_insn_4;
  logic [4:0] div_insn_rd_4;

  always_ff @(posedge clk) begin
    if (rst) begin
      div_by_zero_4 <= 0;
      div_sign_4 <= 0;
      dividend_sign_4 <= 0;
      div_pc_4 <= 0;
      div_insn_4 <= 0;
      div_insn_rd_4 <= 0;
    end else begin
      div_by_zero_4 <= div_by_zero_3;
      div_sign_4 <= div_sign_3;
      dividend_sign_4 <= dividend_sign_3;
      div_pc_4 <= div_pc_3;
      div_insn_4 <= div_insn_3;
      div_insn_rd_4 <= div_insn_rd_3;
    end
  end

  logic div_by_zero_5;
  logic div_sign_5;
  logic dividend_sign_5;
  logic [`REG_SIZE] div_pc_5;
  logic [`REG_SIZE] div_insn_5;
  logic [4:0] div_insn_rd_5;

  always_ff @(posedge clk) begin
    if (rst) begin
      div_by_zero_5 <= 0;
      div_sign_5 <= 0;
      dividend_sign_5 <= 0;
      div_pc_5 <= 0;
      div_insn_5 <= 0;
      div_insn_rd_5 <= 0;
    end else begin
      div_by_zero_5 <= div_by_zero_4;
      div_sign_5 <= div_sign_4;
      dividend_sign_5 <= dividend_sign_4;
      div_pc_5 <= div_pc_4;
      div_insn_5 <= div_insn_4;
      div_insn_rd_5 <= div_insn_rd_4;
    end
  end

  logic div_by_zero_6;
  logic div_sign_6;
  logic dividend_sign_6;
  logic [`REG_SIZE] div_pc_6;
  logic [`REG_SIZE] div_insn_6;
  logic [4:0] div_insn_rd_6;

  always_ff @(posedge clk) begin
    if (rst) begin
      div_by_zero_6 <= 0;
      div_sign_6 <= 0;
      dividend_sign_6 <= 0;
      div_pc_6 <= 0;
      div_insn_6 <= 0;
      div_insn_rd_6 <= 0;
    end else begin
      div_by_zero_6 <= div_by_zero_5;
      div_sign_6 <= div_sign_5;
      dividend_sign_6 <= dividend_sign_5;
      div_pc_6 <= div_pc_5;
      div_insn_6 <= div_insn_5;
      div_insn_rd_6 <= div_insn_rd_5;
    end
  end

  logic div_by_zero_7;
  logic div_sign_7;
  logic dividend_sign_7;
  logic [`REG_SIZE] div_pc_7;
  logic [`REG_SIZE] div_insn_7;
  logic [4:0] div_insn_rd_7;

  always_ff @(posedge clk) begin
    if (rst) begin
      div_by_zero_7 <= 0;
      div_sign_7 <= 0;
      dividend_sign_7 <= 0;
      div_pc_7 <= 0;
      div_insn_7 <= 0;
      div_insn_rd_7 <= 0;
    end else begin
      div_by_zero_7 <= div_by_zero_6;
      div_sign_7 <= div_sign_6;
      dividend_sign_7 <= dividend_sign_6;
      div_pc_7 <= div_pc_6;
      div_insn_7 <= div_insn_6;
      div_insn_rd_7 <= div_insn_rd_6;
    end
  end

  
  /***************/
  /* FETCH STAGE */
  /***************/

  logic [`REG_SIZE] f_pc_current;
  cycle_status_e f_cycle_status;

  // program counter
  always_ff @(posedge clk) begin
    if (rst) begin
      f_pc_current <= 32'd0;
      // NB: use CYCLE_NO_STALL since this is the value that will persist after the last reset cycle
      f_cycle_status <= CYCLE_NO_STALL;
    end else if (x_branch_taken) begin
      // BRANCH TO NEW PC
      f_pc_current <= x_branched_pc;
      f_cycle_status <= CYCLE_NO_STALL;
    end else if (data_dependent_load || div_stall) begin
      // if data_dependent_load, we keep the insn in fetch
      f_pc_current <= f_pc_current;
      f_cycle_status <= CYCLE_NO_STALL;
    end else begin
      f_cycle_status <= CYCLE_NO_STALL;
      f_pc_current <= f_pc_current + 4;
    end
  end
  // send PC to imem
 
  // We need to do a read request to the icache through the AR lines
  logic fetch_insn;
  assign fetch_insn = 1;
  always_comb begin
    icache.ARVALID = 0;
    icache.ARADDR = 0;
    icache.RREADY = 0;
    if (fetch_insn) begin
      icache.ARVALID = 1;
      icache.ARADDR = f_pc_current;
      icache.RREADY = 1;
    end
  end
 


  // Here's how to disassemble an insn into a string you can view in GtkWave.
  // Use PREFIX to provide a 1-character tag to identify which stage the insn comes from.
  
  wire [255:0] d_disasm;
  Disasm #(
      .PREFIX("D")
  ) disasm_1decode (
      .insn  (d_insn),
      .disasm(d_disasm)
  );
  wire [255:0] x_disasm;
  Disasm #(
      .PREFIX("X")
  ) disasm_2execute (
      .insn  (execute_state.insn),
      .disasm(x_disasm)
  );
  wire [255:0] m_disasm;
  Disasm #(
      .PREFIX("M")
  ) disasm_3memory (
      .insn  (memory_state.insn),
      .disasm(m_disasm)
  );
  wire [255:0] w_disasm;
  Disasm #(
      .PREFIX("W")
  ) disasm_4write (
      .insn  (write_state.insn),
      .disasm(w_disasm)
  );

  /****************/
  /* DECODE STAGE */
  /****************/

  // this shows how to package up state in a `struct packed`, and how to pass it between stages
  // stage_decode_t decode_state_temp;

  // always_comb begin

  // end
  stage_decode_t decode_state;
  always_ff @(posedge clk) begin
    if (rst) begin
      decode_state <= '{
        pc: 0,
        cycle_status: CYCLE_RESET
      };
    end else if (x_branch_taken) begin
      // FLUSH
      decode_state <= '{
        pc: 0,
        cycle_status: CYCLE_TAKEN_BRANCH
      };
    end else if (data_dependent_load || div_stall) begin
      // STALL
      decode_state <= '{
        pc: d_pc_current,
        cycle_status: d_cycle_status
      };
    end else begin
      // NORMAL
      decode_state <= '{
        pc: f_pc_current,
        cycle_status: f_cycle_status
      };
    end
  end
  

  logic [`REG_SIZE] d_pc_current;
  logic [`INSN_SIZE] d_insn;
  cycle_status_e d_cycle_status;

  assign d_pc_current = decode_state.pc;
  assign d_cycle_status = decode_state.cycle_status;

  // get insn from icache
  logic ignore_insn; // 1 if brach misprediction occured
  assign ignore_insn = 0;

  always_comb begin
    d_insn = icache.RDATA;
    if (ignore_insn) begin
      d_insn = 0;
    end
  end


  // DECODE INSN

  // components of the instruction
  logic [6:0] d_insn_funct7;
  logic [4:0] d_insn_rs2;
  logic [4:0] d_insn_rs1;
  logic [2:0] d_insn_funct3;
  logic [4:0] d_insn_rd;
  logic [4:0] d_insn_rd_temp;
  logic [`OPCODE_SIZE] d_insn_opcode;

  // split R-type instruction - see section 2.2 of RiscV spec
  assign {d_insn_funct7, d_insn_rs2, d_insn_rs1, d_insn_funct3, d_insn_rd_temp, d_insn_opcode} = d_insn;

  assign d_insn_rd = (d_insn_opcode == OpBranch || d_insn_opcode == OpStore) ? 0 : d_insn_rd_temp;
  
  // setup for I, S, B & J type instructions
  // I - short immediates and loads
  logic [11:0] d_imm_i;
  assign d_imm_i = d_insn[31:20];

  // S - stores
  logic [11:0] d_imm_s;
  assign d_imm_s[11:5] = d_insn_funct7, d_imm_s[4:0] = d_insn_rd_temp;

  // B - conditionals
  logic [12:0] d_imm_b;
  assign {d_imm_b[12], d_imm_b[10:5]} = d_insn_funct7, {d_imm_b[4:1], d_imm_b[11]} = d_insn_rd_temp, d_imm_b[0] = 1'b0;

  // J - unconditional jumps
  logic [20:0] d_imm_j;
  assign {d_imm_j[20], d_imm_j[10:1], d_imm_j[11], d_imm_j[19:12], d_imm_j[0]} = {d_insn[31:12], 1'b0};

  logic [`REG_SIZE] d_imm_i_sext;
  logic [`REG_SIZE] d_imm_s_sext;
  logic [`REG_SIZE] d_imm_b_sext;
  logic [`REG_SIZE] d_imm_j_sext;

  assign d_imm_i_sext = {{20{d_imm_i[11]}}, d_imm_i[11:0]};
  assign d_imm_s_sext = {{20{d_imm_s[11]}}, d_imm_s[11:0]};
  assign d_imm_b_sext = {{19{d_imm_b[12]}}, d_imm_b[12:0]};
  assign d_imm_j_sext = {{11{d_imm_j[20]}}, d_imm_j[20:0]};

  logic [19:0] d_imm_u;
  assign d_imm_u = d_insn[31:12];

  // data taken from register file
  logic [`REG_SIZE] d_rs1_data_temp;
  logic [`REG_SIZE] d_rs2_data_temp;

  logic [`REG_SIZE] d_rs1_data;
  logic [`REG_SIZE] d_rs2_data;

  // WD Bypass
  always_comb begin
    d_rs1_data = d_rs1_data_temp;
    d_rs2_data = d_rs2_data_temp;
  
  
    if (w_insn_rd == d_insn_rs1 && d_insn_rs1 != 0) begin
      d_rs1_data = w_rd_data;
    end
    if (w_insn_rd == d_insn_rs2 && d_insn_rs2 != 0) begin
      d_rs2_data = w_rd_data;
    end

  end

  // LOAD DATA DEPENDENCY CHECK
  // logic load_data_dependency_stall; // if 1, stall for one cycle
  // assign load_data_dependency_stall = x_opcode == OpLoad && (x_insn_rd == d_insn_rs1 || x_insn_rd == d_insn_rs2);

  
  insn_key d_insn_key;
  assign d_insn_key.insn_lui   = d_insn_opcode == OpLui;
  assign d_insn_key.insn_auipc = d_insn_opcode == OpAuipc;
  assign d_insn_key.insn_jal   = d_insn_opcode == OpJal;
  assign d_insn_key.insn_jalr  = d_insn_opcode == OpJalr;

  assign d_insn_key.insn_beq  = d_insn_opcode == OpBranch && d_insn_funct3 == 3'b000;
  assign d_insn_key.insn_bne  = d_insn_opcode == OpBranch && d_insn_funct3 == 3'b001;
  assign d_insn_key.insn_blt  = d_insn_opcode == OpBranch && d_insn_funct3 == 3'b100;
  assign d_insn_key.insn_bge  = d_insn_opcode == OpBranch && d_insn_funct3 == 3'b101;
  assign d_insn_key.insn_bltu = d_insn_opcode == OpBranch && d_insn_funct3 == 3'b110;
  assign d_insn_key.insn_bgeu = d_insn_opcode == OpBranch && d_insn_funct3 == 3'b111;

  assign d_insn_key.insn_lb  = d_insn_opcode == OpLoad && d_insn_funct3 == 3'b000;
  assign d_insn_key.insn_lh  = d_insn_opcode == OpLoad && d_insn_funct3 == 3'b001;
  assign d_insn_key.insn_lw  = d_insn_opcode == OpLoad && d_insn_funct3 == 3'b010;
  assign d_insn_key.insn_lbu = d_insn_opcode == OpLoad && d_insn_funct3 == 3'b100;
  assign d_insn_key.insn_lhu = d_insn_opcode == OpLoad && d_insn_funct3 == 3'b101;

  assign d_insn_key.insn_sb = d_insn_opcode == OpStore && d_insn_funct3 == 3'b000;
  assign d_insn_key.insn_sh = d_insn_opcode == OpStore && d_insn_funct3 == 3'b001;
  assign d_insn_key.insn_sw = d_insn_opcode == OpStore && d_insn_funct3 == 3'b010;

  assign d_insn_key.insn_addi  = d_insn_opcode == OpRegImm && d_insn_funct3 == 3'b000;
  assign d_insn_key.insn_slti  = d_insn_opcode == OpRegImm && d_insn_funct3 == 3'b010;
  assign d_insn_key.insn_sltiu = d_insn_opcode == OpRegImm && d_insn_funct3 == 3'b011;
  assign d_insn_key.insn_xori  = d_insn_opcode == OpRegImm && d_insn_funct3 == 3'b100;
  assign d_insn_key.insn_ori   = d_insn_opcode == OpRegImm && d_insn_funct3 == 3'b110;
  assign d_insn_key.insn_andi  = d_insn_opcode == OpRegImm && d_insn_funct3 == 3'b111;

  assign d_insn_key.insn_slli = d_insn_opcode == OpRegImm && d_insn_funct3 == 3'b001 && d_insn_funct7 == 7'd0;
  assign d_insn_key.insn_srli = d_insn_opcode == OpRegImm && d_insn_funct3 == 3'b101 && d_insn_funct7 == 7'd0;
  assign d_insn_key.insn_srai = d_insn_opcode == OpRegImm && d_insn_funct3 == 3'b101 && d_insn_funct7 == 7'b0100000;

  assign d_insn_key.insn_add  = d_insn_opcode == OpRegReg && d_insn_funct3 == 3'b000 && d_insn_funct7 == 7'd0;
  assign d_insn_key.insn_sub  = d_insn_opcode == OpRegReg && d_insn_funct3 == 3'b000 && d_insn_funct7 == 7'b0100000;
  assign d_insn_key.insn_sll  = d_insn_opcode == OpRegReg && d_insn_funct3 == 3'b001 && d_insn_funct7 == 7'd0;
  assign d_insn_key.insn_slt  = d_insn_opcode == OpRegReg && d_insn_funct3 == 3'b010 && d_insn_funct7 == 7'd0;
  assign d_insn_key.insn_sltu = d_insn_opcode == OpRegReg && d_insn_funct3 == 3'b011 && d_insn_funct7 == 7'd0;
  assign d_insn_key.insn_xor  = d_insn_opcode == OpRegReg && d_insn_funct3 == 3'b100 && d_insn_funct7 == 7'd0;
  assign d_insn_key.insn_srl  = d_insn_opcode == OpRegReg && d_insn_funct3 == 3'b101 && d_insn_funct7 == 7'd0;
  assign d_insn_key.insn_sra  = d_insn_opcode == OpRegReg && d_insn_funct3 == 3'b101 && d_insn_funct7 == 7'b0100000;
  assign d_insn_key.insn_or   = d_insn_opcode == OpRegReg && d_insn_funct3 == 3'b110 && d_insn_funct7 == 7'd0;
  assign d_insn_key.insn_and  = d_insn_opcode == OpRegReg && d_insn_funct3 == 3'b111 && d_insn_funct7 == 7'd0;

  assign d_insn_key.insn_mul    = d_insn_opcode == OpRegReg && d_insn_funct7 == 7'd1 && d_insn_funct3 == 3'b000;
  assign d_insn_key.insn_mulh   = d_insn_opcode == OpRegReg && d_insn_funct7 == 7'd1 && d_insn_funct3 == 3'b001;
  assign d_insn_key.insn_mulhsu = d_insn_opcode == OpRegReg && d_insn_funct7 == 7'd1 && d_insn_funct3 == 3'b010;
  assign d_insn_key.insn_mulhu  = d_insn_opcode == OpRegReg && d_insn_funct7 == 7'd1 && d_insn_funct3 == 3'b011;
  assign d_insn_key.insn_div    = d_insn_opcode == OpRegReg && d_insn_funct7 == 7'd1 && d_insn_funct3 == 3'b100;
  assign d_insn_key.insn_divu   = d_insn_opcode == OpRegReg && d_insn_funct7 == 7'd1 && d_insn_funct3 == 3'b101;
  assign d_insn_key.insn_rem    = d_insn_opcode == OpRegReg && d_insn_funct7 == 7'd1 && d_insn_funct3 == 3'b110;
  assign d_insn_key.insn_remu   = d_insn_opcode == OpRegReg && d_insn_funct7 == 7'd1 && d_insn_funct3 == 3'b111;

  assign d_insn_key.insn_ecall = d_insn_opcode == OpEnviron && d_insn[31:7] == 25'd0;
  assign d_insn_key.insn_fence = d_insn_opcode == OpMiscMem;

  stage_execute_t normal_execute_state;
  assign normal_execute_state = '{
    pc: d_pc_current,
    insn: d_insn,
    cycle_status: d_cycle_status,

    opcode: d_insn_opcode,
    
    insn_rd: d_insn_rd,

    imm_i: d_imm_i,
    imm_s: d_imm_s,
    imm_b: d_imm_b,
    imm_j: d_imm_j,
    
    imm_i_sext: d_imm_i_sext,
    imm_s_sext: d_imm_s_sext,
    imm_b_sext: d_imm_b_sext,
    imm_j_sext: d_imm_j_sext,

    imm_u: d_imm_u,

    // data taken from register file
    rs1_data: d_rs1_data,
    rs2_data: d_rs2_data,
    insn_rs1: d_insn_rs1,
    insn_rs2: d_insn_rs2,

    // insn_key containing the insn signal
    insn_set: d_insn_key,

    halt: 0

  };

  /****************/
  /* EXECUTE STAGE */
  /****************/

  stage_execute_t execute_state;
  always_ff @(posedge clk) begin
    if (rst) begin
      execute_state <= 0;
      execute_state.cycle_status <= CYCLE_RESET;
    end else if (x_branch_taken) begin
      // FLUSH
      execute_state <= 0;
      execute_state.cycle_status <= CYCLE_TAKEN_BRANCH;
    end else if (data_dependent_load) begin
      // NOP
      execute_state <= 0;
      execute_state.cycle_status <= CYCLE_LOAD2USE;
    end else if (div_stall) begin
      execute_state <= execute_state;
      execute_state.cycle_status <= CYCLE_DIV;
    
    end else begin
      execute_state <= normal_execute_state;
    end
  end

  // Execute Signals
  logic x_we;
  logic [31:0] x_rd_data;

  logic [`REG_SIZE] x_pc;
  assign x_pc = execute_state.pc;
  logic [`INSN_SIZE] x_insn;
  assign x_insn = execute_state.insn;
  cycle_status_e x_cycle_status;
  assign x_cycle_status = execute_state.cycle_status;
  

  logic [`OPCODE_SIZE] x_opcode;
  assign x_opcode = execute_state.opcode;
  
  logic [4:0] x_insn_rd;
  assign x_insn_rd = execute_state.insn_rd;

  logic [11:0] x_imm_i;
  assign x_imm_i = execute_state.imm_i;
  logic [11:0] x_imm_s;
  assign x_imm_s = execute_state.imm_s;
  logic [12:0] x_imm_b;
  assign x_imm_b = execute_state.imm_b;
  logic [20:0] x_imm_j;
  assign x_imm_j = execute_state.imm_j;
  
  logic [`REG_SIZE] x_imm_i_sext;
  assign x_imm_i_sext = execute_state.imm_i_sext;
  logic [`REG_SIZE] x_imm_s_sext;
  assign x_imm_s_sext = execute_state.imm_s_sext;
  logic [`REG_SIZE] x_imm_b_sext;
  assign x_imm_b_sext = execute_state.imm_b_sext;
  logic [`REG_SIZE] x_imm_j_sext;
  assign x_imm_j_sext = execute_state.imm_j_sext;

  logic [19:0] x_imm_u;
  assign x_imm_u = execute_state.imm_u;

  // data taken from register file
  logic [`REG_SIZE] x_rs1_data_temp;
  assign x_rs1_data_temp = execute_state.rs1_data;
  logic [`REG_SIZE] x_rs2_data_temp;
  assign x_rs2_data_temp = execute_state.rs2_data;

  logic [4:0] x_insn_rs1;
  assign x_insn_rs1 = execute_state.insn_rs1;
  logic [4:0] x_insn_rs2;
  assign x_insn_rs2 = execute_state.insn_rs2;

  logic [`REG_SIZE] x_rs1_data;
  logic [`REG_SIZE] x_rs2_data;

  // insn_key containing the insn signal
  insn_key x_insn_key;
  assign x_insn_key = execute_state.insn_set;

  // memory signals
  logic [`REG_SIZE] x_addr_to_dmem;
  logic [`REG_SIZE] x_store_mem_to_dmem;
  logic [3:0] x_store_we_to_dmem;
  logic [1:0] x_mem_bytes;

  // branch signal
  logic [`REG_SIZE] x_branched_pc; // represents the pc value that will be branched to IF there is a branch
  logic x_branch_taken; // 1: branch, 0: no branch

  // MX and WX Bypass

  always_comb begin
    // default
    x_rs1_data = x_rs1_data_temp;
    x_rs2_data = x_rs2_data_temp;

    // rs1_data
    if (x_insn_rs1 != 0) begin
      if (m_insn_rd == x_insn_rs1) begin
        x_rs1_data = m_rd_data;
      end else if (w_insn_rd == x_insn_rs1) begin
        x_rs1_data = w_rd_data;
      end
    end
    // rs2_data
    if (x_insn_rs2 != 0) begin
      if (m_insn_rd == x_insn_rs2) begin
        x_rs2_data = m_rd_data;
      end else if (w_insn_rd == x_insn_rs2) begin
        x_rs2_data = w_rd_data;
      end
    end

  end

  // halt signal
  logic x_halt;

  // determine data-dependent load -> if insn in execute is load && rd is a operator for the previous insn
  logic data_dependent_load; // = x_opcode == OpLoad && (x_insn_rd == d_insn_rs1 || x_insn_rd == d_insn_rs2);
  always_comb begin
    data_dependent_load = 0;
    if (x_opcode == OpLoad) begin
      if (d_insn_opcode == OpStore || d_insn_opcode == OpRegImm || d_insn_opcode == OpLoad) begin
        // if store or imm insn, only stall if x_insn_rd == d_insn_rs1
        data_dependent_load = x_insn_rd == d_insn_rs1;
      end else if (d_insn_opcode != OpLui && d_insn_opcode != OpJal 
          && d_insn_opcode != OpJalr) begin
        data_dependent_load = x_insn_rd == d_insn_rs1 || x_insn_rd == d_insn_rs2;
      end
    end
  end

  always_comb begin
    // register signals
    x_we = 0;
    x_rd_data = 0;

    // data memory signals
    x_addr_to_dmem = 0;
    x_store_mem_to_dmem = 0;
    x_store_we_to_dmem = 0;

    x_mem_bytes = 0;

    //
    multiple = 0;

    // branch signals
    x_branched_pc = x_pc; 
    x_branch_taken = 0;

    // halt signal
    x_halt = 0;

    case (x_opcode)
      OpLui: begin
        x_we = 1;
        x_rd_data = x_imm_u << 12;
                
      end

      OpAuipc : begin
        x_we = 1;
        x_rd_data = x_pc + (x_imm_u << 12);
      end

      // I-TYPE
      OpRegImm : begin // rs_data = rs1_data _ immi
        x_we = 1;
        
        case (1)
          x_insn_key.insn_addi: begin
            x_rd_data = cla_sum;
          end
          x_insn_key.insn_slti: begin
            x_rd_data = $signed(x_rs1_data) < $signed(x_imm_i_sext) ? 1 : 0;
          end
          x_insn_key.insn_sltiu: begin
            x_rd_data = x_rs1_data < x_imm_i_sext ? 1 : 0;
          end
          x_insn_key.insn_xori: begin
            x_rd_data = x_rs1_data ^ x_imm_i_sext;
          end
          x_insn_key.insn_ori: begin
            x_rd_data = x_rs1_data | x_imm_i_sext;
          end
          x_insn_key.insn_andi: begin
            x_rd_data = x_rs1_data & x_imm_i_sext;
          end
          x_insn_key.insn_slli: begin
            x_rd_data = x_rs1_data << x_imm_i[4:0];
          end
          x_insn_key.insn_srli: begin
            x_rd_data = x_rs1_data >> x_imm_i[4:0];
          end
          x_insn_key.insn_srai: begin
            x_rd_data = $signed(x_rs1_data) >>> (x_imm_i[4:0]);
          end
          
        endcase
      // R-TYPE 
      end

      OpRegReg: begin // rs_data = rs1_data _ rs2_data
        x_we = 1;
        case (1) 
          x_insn_key.insn_add: begin
            x_rd_data = cla_sum;
          end
          x_insn_key.insn_sub: begin
            x_rd_data = cla_sum;
          end
          x_insn_key.insn_sll: begin
            x_rd_data = x_rs1_data << x_rs2_data[4:0];
          end
          x_insn_key.insn_slt: begin
            x_rd_data = $signed(x_rs1_data) < $signed(x_rs2_data) ? 1 : 0;
          end
          x_insn_key.insn_sltu: begin
            x_rd_data = x_rs1_data < x_rs2_data ? 1 : 0;
          end
          x_insn_key.insn_xor: begin
            x_rd_data = x_rs1_data ^ x_rs2_data;
          end
          x_insn_key.insn_srl: begin
            x_rd_data = x_rs1_data >> (x_rs2_data[4:0]);
          end
          x_insn_key.insn_sra: begin
            x_rd_data = $signed(x_rs1_data) >>> (x_rs2_data[4:0]);
          end
          x_insn_key.insn_or: begin
            x_rd_data = x_rs1_data | x_rs2_data;
          end
          x_insn_key.insn_and: begin
            x_rd_data = x_rs1_data & x_rs2_data;
          end
          // Multiply
          x_insn_key.insn_mul: begin
            multiple = (x_rs1_data * x_rs2_data);
            x_rd_data = multiple[31:0];
          end
          x_insn_key.insn_mulh: begin
            multiple = $signed(x_rs1_data) * $signed(x_rs2_data);
            x_rd_data = multiple[63:32];
          end
          x_insn_key.insn_mulhsu: begin
            multiple = {{32{x_rs1_data[31]}}, x_rs1_data} * {{32{1'b0}}, x_rs2_data};
            x_rd_data = multiple[63:32];
          end
          x_insn_key.insn_mulhu: begin
            multiple = $unsigned(x_rs1_data) * $unsigned(x_rs2_data);
            x_rd_data = multiple[63:32];
          end
          // Divide
          x_insn_key.insn_div: begin
            if (div_by_zero_7) begin
              // return -1 if dividing by zero
              x_rd_data = 32'hFFFFFFFF; 
            end else begin
              x_rd_data = signed_quotient;
            end

            // check if divide is not finished yet
            // if (divide_count != 3'b111) begin
            //   pcNext = pcCurrent;
            // end
          end
          x_insn_key.insn_divu: begin
            x_rd_data = unsigned_quotient;
            // check if divide is not finished yet
            // if (divide_count != 3'b111) begin
            //   pcNext = pcCurrent;
            // end
          end
          // Modulus
          x_insn_key.insn_rem: begin
            x_rd_data = signed_remainder;
            // // check if divide is not finished yet
            // if (divide_count != 3'b111) begin
            //   pcNext = pcCurrent;            
            // end
          end
          x_insn_key.insn_remu: begin
            x_rd_data = unsigned_remainder;
            // check if divide is not finished yet
            // if (divide_count != 3'b111) begin
            //   pcNext = pcCurrent;

            // end
          end

        endcase
      end

      OpBranch: begin
        x_branched_pc = x_pc + x_imm_b_sext;
        case (1)
          x_insn_key.insn_beq: begin
            x_branch_taken = x_rs1_data == x_rs2_data;
          end
          x_insn_key.insn_bne: begin
            x_branch_taken = x_rs1_data != x_rs2_data;
          end
          x_insn_key.insn_blt: begin
            x_branch_taken = $signed(x_rs1_data) < $signed(x_rs2_data);
          end
          x_insn_key.insn_bge: begin
            x_branch_taken = $signed(x_rs1_data) >= $signed(x_rs2_data);
          end
          x_insn_key.insn_bltu: begin
            x_branch_taken = $signed(x_rs1_data) < $unsigned(x_rs2_data);
          end
          x_insn_key.insn_bgeu: begin
            x_branch_taken = $signed(x_rs1_data) >= $unsigned(x_rs2_data);
          end
         
        endcase
        
      end

      OpLoad: begin
        x_we = 1;
        x_addr_to_dmem = cla_sum;
        

      end

      OpStore: begin
        x_addr_to_dmem = cla_sum;
      end

      OpJalr: begin
        x_we = 1;
        // load next instruction in register
        x_rd_data = x_pc + 4;
        // jump to desired location
        x_branch_taken = 1;
        x_branched_pc = (x_rs1_data + x_imm_i_sext) & ~(32'd1);
      end

      OpJal: begin
        x_we = 1;
        // load next instruction in register
        x_rd_data = x_pc + 4;
        // jump to desired offset
        x_branch_taken = 1;
        x_branched_pc = x_pc + x_imm_j_sext;

      end
      

      OpEnviron: begin
        // ecall > halt program, transfer control to OS (we don't have to do for now)
        x_halt = 1;
        
      end

      OpMiscMem: begin
        // fence > do nothing but increment PC

      end

      default: begin
        //illegal_insn = 1'b1;
      end
    endcase
  end
  
  
  /****************/
  /* MEMORY STAGE */
  /****************/

  stage_memory_t memory_state;
  always_ff @(posedge clk) begin
    if (rst) begin
      memory_state <= 0;
      memory_state.cycle_status <= CYCLE_RESET;
    end else if (x_div_insn && ~(div_count_first == 3'b0)) begin
      // only let through divide insns if div_count_first == 0
      memory_state <= 0;
      memory_state.cycle_status <= CYCLE_DIV;
    end else if (x_div_insn) begin
      // SPECIAL CASE TO READ DIV INSNS TO MEMORY STAGE
      memory_state <= '{
          pc: div_pc_7,
          insn: div_insn_7,
          cycle_status: CYCLE_NO_STALL,
          opcode: div_insn_7[6:0],

          // register signals
          insn_rd: div_insn_rd_7,
          rd_data: x_rd_data,
          we: 1,

          // memory signals
          addr_to_dmem: 0,
          store_data_to_dmem: 0,
          store_we_to_dmem: 0,

          rs2_data: 0,
          insn_rs2: 0,

          // branch signals
          branched_pc: 0, // represents the pc value that will be branched to IF there is a branch
          branch_taken: 0, // 1: branch, 0: no branch

          insn_set: 0,

          halt: 0

        };
    end else begin
        memory_state <= '{
          pc: x_pc,
          insn: x_insn,
          cycle_status: x_cycle_status,
          opcode: x_opcode,

          // register signals
          insn_rd: x_insn_rd,
          rd_data: x_rd_data,
          we: x_we,

          // memory signals
          addr_to_dmem: x_addr_to_dmem,
          store_data_to_dmem: x_store_mem_to_dmem,
          store_we_to_dmem: x_store_we_to_dmem,

          rs2_data: x_rs2_data,
          insn_rs2: x_insn_rs2,

          // branch signals
          branched_pc: x_branched_pc, // represents the pc value that will be branched to IF there is a branch
          branch_taken: x_branch_taken, // 1: branch, 0: no branch

          insn_set: x_insn_key,

          halt: x_halt

        };
    end
  end

  // MEMORY SIGNALS

  logic [`REG_SIZE] m_pc;
  assign m_pc = memory_state.pc;

  logic [`INSN_SIZE] m_insn;
  assign m_insn = memory_state.insn;

  cycle_status_e m_cycle_status;
  assign m_cycle_status = memory_state.cycle_status;

  logic [`OPCODE_SIZE] m_opcode;
  assign m_opcode = memory_state.opcode;

  // register signals
  logic [4:0] m_insn_rd;
  assign m_insn_rd = memory_state.insn_rd;

  // set a m_rd_data_temp in case the data loaded to register comes from data memory
  logic [31:0] m_rd_data;

  logic [`REG_SIZE] m_rd_data_temp;
  assign m_rd_data_temp = memory_state.rd_data;

  logic m_we;
  assign m_we = memory_state.we;

  // memory signals
  logic [`REG_SIZE] m_addr_to_dmem;
  assign m_addr_to_dmem = memory_state.addr_to_dmem;

  // logic [`REG_SIZE] m_addr_to_dmem_temp;
  // assign m_addr_to_dmem_temp = memory_state.addr_to_dmem;

  logic [`REG_SIZE] m_store_data_to_dmem;

  // DATA TO STORE IN MEMORY
  logic [`REG_SIZE] m_rs2_data;
  logic [`REG_SIZE] m_rs2_data_temp;
  assign m_rs2_data_temp = memory_state.rs2_data;

  logic [4:0] m_insn_rs2;
  assign m_insn_rs2 = memory_state.insn_rs2;

  logic [3:0] m_store_we_to_dmem;
  
  logic [1:0] m_mem_bytes; // which bytes we want from memory
  assign m_mem_bytes = m_addr_to_dmem[1:0]; 

  // insn_key
  insn_key m_insn_key;
  assign m_insn_key = memory_state.insn_set;

  logic m_halt;
  assign m_halt = memory_state.halt;

  // send inputs to data memory
  logic m_write;
  logic m_read;

  always_comb begin
    dcache.ARVALID = 0;
    dcache.ARADDR = 0;
    dcache.AWVALID = 0;
    dcache.AWADDR = 0;
    if (m_read) begin
      dcache.ARVALID = 1;
      dcache.ARADDR = m_addr_to_dmem & 32'hFFFFFFFC;
    end else if (m_write) begin
      dcache.AWVALID = 1;
      dcache.AWADDR = m_addr_to_dmem & 32'hFFFFFFFC;
    end
  end


  // determine addr_to_dmem -> WM BYPASS
  // always_comb begin
  //   m_addr_to_dmem = m_addr_to_dmem_temp;
  //   if (w_insn_load && w_insn_rd == m_insn_rs2 && m_opcode == OpStore && w_insn_rd != 0) begin
  //     m_addr_to_dmem = w_rd_data;
  //   end
  // end
  always_comb begin
    m_rs2_data = m_rs2_data_temp; // Default to the value from the memory stage
    if (m_opcode == OpStore && m_insn_rs2 != 0) begin
      // Check if the value needs to be bypassed from the write-back stage
      if (w_insn_load && w_insn_rd == m_insn_rs2) begin
        m_rs2_data = w_rd_data;
      end
    end
  end

  // loaded data should be inputed into the processor at the negedge of CLK
  always_comb begin
    m_rd_data = m_rd_data_temp;
    m_store_we_to_dmem = 0;
    m_store_data_to_dmem = 0;
    m_write = 0;
    m_read = 0;
    case (m_opcode)
      // load insns
      OpLoad: begin
        m_read = 1;
        

      end

      OpStore: begin
        m_write = 1;
        case (1)
          m_insn_key.insn_sb: begin
            // store only one byte
            m_store_we_to_dmem = 4'b1 << m_mem_bytes;
            m_store_data_to_dmem = ({24'd0, m_rs2_data[7:0]}) << ({3'b0, m_mem_bytes} << 3);
          
          end
          m_insn_key.insn_sh: begin
            // store 2 bytes
            m_store_we_to_dmem = 4'b11 << m_mem_bytes;
              
            m_store_data_to_dmem = ({16'd0, m_rs2_data[15:0]}) << ({3'b0, m_mem_bytes} << 3);
          end
          m_insn_key.insn_sw: begin
            // store all 4 bytes
            m_store_we_to_dmem = 4'b1111;
            m_store_data_to_dmem = m_rs2_data;
          end
        endcase
      end

      default: begin
      
      end

    endcase
  end
  
  /****************/
  /* WRITE STAGE */
  /****************/

  
  stage_write_t write_state;
  always_ff @(posedge clk) begin
    if (rst) begin
      write_state <= 0;
      write_state.cycle_status <= CYCLE_RESET;
    end else begin
      write_state <= '{
        pc: m_pc,
        insn: m_insn,
        cycle_status: m_cycle_status,
        opcode: m_opcode,

        // register signals
        insn_rd: m_insn_rd,
        rd_data: m_rd_data,
        we: m_we,

        insn_set: m_insn_key,
        mem_bytes: m_mem_bytes,

        halt: m_halt

      };
    end
  end

  // WRITE SIGNALS
  logic [`REG_SIZE] w_pc;
  assign w_pc = write_state.pc;

  logic [`INSN_SIZE] w_insn;
  assign w_insn = write_state.insn;

  cycle_status_e w_cycle_status;
  assign w_cycle_status = write_state.cycle_status;

  // bytes to load from DATA if LOAD insn
 
  // // list of insns
  insn_key w_insn_key;
  assign w_insn_key = write_state.insn_set;

  // load insn?
  logic w_insn_load;
  assign w_insn_load = w_opcode == OpLoad;

  logic [`OPCODE_SIZE] w_opcode;
  assign w_opcode = write_state.opcode;

  // register signals
  logic [4:0] w_insn_rd;
  assign w_insn_rd = write_state.insn_rd;

  logic [31:0] w_rd_data;
  logic [31:0] w_rd_data_temp;
  assign w_rd_data_temp = write_state.rd_data;

  logic [1:0] w_mem_bytes;
  assign w_mem_bytes = write_state.mem_bytes;
  
  logic w_we;
  assign w_we = write_state.we;

  // halt
  logic w_halt;
  assign w_halt = write_state.halt;

  assign halt = w_halt;

  // set trace signals
  assign trace_writeback_pc = w_pc;
  assign trace_writeback_insn = w_insn;
  assign trace_writeback_cycle_status = w_cycle_status;

  // process data from memory if load insn
  always_comb begin
    w_rd_data = w_rd_data_temp;
    if (w_opcode == OpLoad) begin
      case (1) 
        w_insn_key.insn_lb: begin
        // offset: 0, 1, 2, 3           
        case (w_mem_bytes)
          0: begin
            // load first byte
            w_rd_data = {{24{dcache.RDATA[7]}}, dcache.RDATA[7:0]};
          end
          1: begin
            // load second byte
            w_rd_data = {{24{dcache.RDATA[15]}}, dcache.RDATA[15:8]};
          end
          2: begin
            // load third byte
            w_rd_data = {{24{dcache.RDATA[23]}}, dcache.RDATA[23:16]};
          end
          3: begin
            // load fourth byte
            w_rd_data = {{24{dcache.RDATA[31]}}, dcache.RDATA[31:24]};
          end
        endcase
        
        end
        w_insn_key.insn_lh: begin
        // offset: 0 or 1
        
          if (w_mem_bytes[1]) begin
            // load the second half of the word
            w_rd_data = {{16{dcache.RDATA[31]}}, dcache.RDATA[31:16]};
          end else begin
            // load the first half of the word
            w_rd_data = {{16{dcache.RDATA[15]}}, dcache.RDATA[15:0]};
          end
        
        end
        w_insn_key.insn_lw: begin
          w_rd_data = dcache.RDATA;
        end
        w_insn_key.insn_lbu: begin 
        // offset: 0, 1, 2, 3      (zero extended)     
        case (w_mem_bytes)
          0: begin
            // load first byte
            w_rd_data = {{24{1'b0}}, dcache.RDATA[7:0]};
          end
          1: begin
            // load second byte
            w_rd_data = {{24{1'b0}}, dcache.RDATA[15:8]};
          end
          2: begin
            // load third byte
            w_rd_data = {{24{1'b0}}, dcache.RDATA[23:16]};
          end
          3: begin
            // load fourth byte
            w_rd_data = {{24{1'b0}}, dcache.RDATA[31:24]};
          end
        endcase
        end
        w_insn_key.insn_lhu: begin
          if (w_mem_bytes[1]) begin
            // load the second half of the word (zero extended)
            w_rd_data = {{16{1'b0}}, dcache.RDATA[31:16]};
          end else begin
            // load the first half of the word (zero extended)
            w_rd_data = {{16{1'b0}}, dcache.RDATA[15:0]};
          end
        end
      endcase
    end
  end


endmodule // DatapathPipelinedCache

module Processor (
    input wire                       clk,
    input wire                       rst,
    output logic                     halt,
    output wire [`REG_SIZE]          trace_writeback_pc,
    output wire [`INSN_SIZE]         trace_writeback_insn,
    output                           cycle_status_e trace_writeback_cycle_status
);

  // This wire is set by cocotb to the name of the currently-running test, to make it easier
  // to see what is going on in the waveforms.
  wire [(8*32)-1:0] test_case;

  axi_if axi_data_cache ();
  axi_if axi_insn_cache ();
  // memory is dual-ported, to connect to both I$ and D$
  axi_if axi_mem_ro ();
  axi_if axi_mem_rw ();

AxilMemory #(.NUM_WORDS(8192)) memory (
  .ACLK(clk),
  .ARESETn(~rst),
  .port_ro(axi_mem_ro.subord),
  .port_rw(axi_mem_rw.subord)
);

`ifdef ENABLE_INSN_CACHE
  AxilCache #(
    .BLOCK_SIZE_BITS(32),
    .NUM_SETS(16)) icache (
    .ACLK(clk),
    .ARESETn(~rst),
    .proc(axi_insn_cache.subord),
    .mem(axi_mem_ro.manager)
  );
`endif
`ifdef ENABLE_DATA_CACHE
  AxilCache #(
    .BLOCK_SIZE_BITS(32),
    .NUM_SETS(16)) dcache (
    .ACLK(clk),
    .ARESETn(~rst),
    .proc(axi_data_cache.subord),
    .mem(axi_mem_rw.manager)
  );
`endif

  DatapathPipelinedCache datapath (
      .clk(clk),
      .rst(rst),
`ifdef ENABLE_INSN_CACHE
      .icache(axi_insn_cache.manager),
`else
      .icache(axi_mem_ro.manager),
`endif
`ifdef ENABLE_DATA_CACHE
      .dcache(axi_data_cache.manager),
`else
      .dcache(axi_mem_rw.manager),
`endif
      .halt(halt),
      .trace_writeback_pc(trace_writeback_pc),
      .trace_writeback_insn(trace_writeback_insn),
      .trace_writeback_cycle_status(trace_writeback_cycle_status)
  );

endmodule
