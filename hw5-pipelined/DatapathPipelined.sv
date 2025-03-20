`timescale 1ns / 1ns

// registers are 32 bits in RV32
`define REG_SIZE 31:0

// insns are 32 bits in RV32IM
`define INSN_SIZE 31:0

// RV opcodes are 7 bits
`define OPCODE_SIZE 6:0

`ifndef DIVIDER_STAGES
`define DIVIDER_STAGES 8
`endif

`ifndef SYNTHESIS
`include "../hw3-singlecycle/RvDisassembler.sv"
`endif
`include "../hw2b-cla/cla.sv"
`include "../hw4-multicycle/DividerUnsignedPipelined.sv"
`include "cycle_status.sv"

module Disasm #(
    byte PREFIX = "D"
) (
    input wire [31:0] insn,
    output wire [(8*32)-1:0] disasm
);
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
endmodule

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
  logic insn_lui;
  logic insn_auipc;
  logic insn_jal;
  logic insn_jalr;

  logic insn_beq;
  logic insn_bne;
  logic insn_blt;
  logic insn_bge;
  logic insn_bltu;
  logic insn_bgeu;

  logic insn_lb;
  logic insn_lh;
  logic insn_lw;
  logic insn_lbu;
  logic insn_lhu;

  logic insn_sb;
  logic insn_sh;
  logic insn_sw;

  logic insn_addi;
  logic insn_slti;
  logic insn_sltiu;
  logic insn_xori;
  logic insn_ori;
  logic insn_andi;

  logic insn_slli;
  logic insn_srli;
  logic insn_srai;

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

  logic insn_ecall;
  logic insn_fence;
} insn_set;

// Credit to Manvi Agarwal for the insn_set structure

/** state at the start of Decode stage */
typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`INSN_SIZE] insn;
  cycle_status_e cycle_status;  
} stage_decode_t;

/** state at the start of Execute stage **/
typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`INSN_SIZE] insn;
  cycle_status_e cycle_status;
  
  logic [4:0] insn_rs1;
  logic [4:0] insn_rs2;
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

  // insn_set containing the insn signal
  insn_set insn_set;

  // // memory signals
  // logic [`REG_SIZE] addr_to_dmem;
  // logic [`REG_SIZE] store_data_to_dmem;
  // logic [3:0] store_we_to_dmem;


  logic halt;


} state_execute_t;

/** state at the start of Memory stage **/

typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`INSN_SIZE] insn;
  cycle_status_e cycle_status;
} state_memory_t;

/** state at the start of Write stage **/

typedef struct packed {
  logic [`REG_SIZE] pc;
  logic [`INSN_SIZE] insn;
  cycle_status_e cycle_status;
} state_write_t;

module DatapathPipelined (
    input wire clk,
    input wire rst,
    output logic [`REG_SIZE] pc_to_imem,
    input wire [`INSN_SIZE] insn_from_imem,
    // dmem is read/write
    output logic [`REG_SIZE] addr_to_dmem,
    input wire [`REG_SIZE] load_data_from_dmem,
    output logic [`REG_SIZE] store_data_to_dmem,
    output logic [3:0] store_we_to_dmem,

    output logic halt,

    // The PC of the insn currently in Writeback. 0 if not a valid insn.
    output logic [`REG_SIZE] trace_writeback_pc,
    // The bits of the insn currently in Writeback. 0 if not a valid insn.
    output logic [`INSN_SIZE] trace_writeback_insn,
    // The status of the insn (or stall) currently in Writeback. See the cycle_status.sv file for valid values.
    output cycle_status_e trace_writeback_cycle_status
);

  // opcodes - see section 19 of RiscV spec
  localparam bit [`OPCODE_SIZE] OpcodeLoad = 7'b00_000_11;
  localparam bit [`OPCODE_SIZE] OpcodeStore = 7'b01_000_11;
  localparam bit [`OPCODE_SIZE] OpcodeBranch = 7'b11_000_11;
  localparam bit [`OPCODE_SIZE] OpcodeJalr = 7'b11_001_11;
  localparam bit [`OPCODE_SIZE] OpcodeMiscMem = 7'b00_011_11;
  localparam bit [`OPCODE_SIZE] OpcodeJal = 7'b11_011_11;

  localparam bit [`OPCODE_SIZE] OpcodeRegImm = 7'b00_100_11;
  localparam bit [`OPCODE_SIZE] OpcodeRegReg = 7'b01_100_11;
  localparam bit [`OPCODE_SIZE] OpcodeEnviron = 7'b11_100_11;

  localparam bit [`OPCODE_SIZE] OpcodeAuipc = 7'b00_101_11;
  localparam bit [`OPCODE_SIZE] OpcodeLui = 7'b01_101_11;

  // cycle counter, not really part of any stage but useful for orienting within GtkWave
  // do not rename this as the testbench uses this value
  logic [`REG_SIZE] cycles_current;
  always_ff @(posedge clk) begin
    if (rst) begin
      cycles_current <= 0;
    end else begin
      cycles_current <= cycles_current + 1;
    end
  end

  /***************/
  /* FETCH STAGE */
  /***************/

  logic [`REG_SIZE] f_pc_current;
  wire [`REG_SIZE] f_insn;
  cycle_status_e f_cycle_status;

  // program counter
  always_ff @(posedge clk) begin
    if (rst) begin
      f_pc_current <= 32'd0;
      // NB: use CYCLE_NO_STALL since this is the value that will persist after the last reset cycle
      f_cycle_status <= CYCLE_NO_STALL;
    end else begin
      f_cycle_status <= CYCLE_NO_STALL;
      f_pc_current <= f_pc_current + 4;
    end
  end
  // send PC to imem
  assign pc_to_imem = f_pc_current;
  assign f_insn = insn_from_imem;

  // Here's how to disassemble an insn into a string you can view in GtkWave.
  // Use PREFIX to provide a 1-character tag to identify which stage the insn comes from.
  wire [255:0] f_disasm;
  Disasm #(
      .PREFIX("F")
  ) disasm_0fetch (
      .insn  (f_insn),
      .disasm(f_disasm)
  );

  /****************/
  /* DECODE STAGE */
  /****************/

  // this shows how to package up state in a `struct packed`, and how to pass it between stages
  stage_decode_t decode_state;
  always_ff @(posedge clk) begin
    if (rst) begin
      decode_state <= '{
        pc: 0,
        insn: 0,
        cycle_status: CYCLE_RESET
      };
    end else begin
      begin
        decode_state <= '{
          pc: f_pc_current,
          insn: f_insn,
          cycle_status: f_cycle_status
        };
      end
    end
  end
  wire [255:0] d_disasm;
  Disasm #(
      .PREFIX("D")
  ) disasm_1decode (
      .insn  (decode_state.insn),
      .disasm(d_disasm)
  );

  logic [`REG_SIZE] d_pc_current = decode_state.pc;
  wire [`REG_SIZE] d_insn = decode_state.insn;
  cycle_status_e d_cycle_status = decode_state.cycle_status;


  // DECODE INSN

  // components of the instruction
  wire [6:0] d_insn_funct7;
  wire [4:0] d_insn_rs2;
  wire [4:0] d_insn_rs1;
  wire [2:0] d_insn_funct3;
  wire [4:0] d_insn_rd;
  wire [`OPCODE_SIZE] d_insn_opcode;

  // split R-type instruction - see section 2.2 of RiscV spec
  assign {d_insn_funct7, d_insn_rs2, d_insn_rs1, d_insn_funct3, d_insn_rd, d_insn_opcode} = d_insn;

  // setup for I, S, B & J type instructions
  // I - short immediates and loads
  wire [11:0] d_imm_i;
  assign d_imm_i = d_insn[31:20];

  // S - stores
  wire [11:0] d_imm_s;
  assign d_imm_s[11:5] = d_insn_funct7, d_imm_s[4:0] = d_insn_rd;

  // B - conditionals
  wire [12:0] d_imm_b;
  assign {d_imm_b[12], d_imm_b[10:5]} = d_insn_funct7, {d_imm_b[4:1], d_imm_b[11]} = d_insn_rd, d_imm_b[0] = 1'b0;

  // J - unconditional jumps
  wire [20:0] d_imm_j;
  assign {d_imm_j[20], d_imm_j[10:1], d_imm_j[11], d_imm_j[19:12], d_imm_j[0]} = {d_insn[31:12], 1'b0};

  wire [`REG_SIZE] d_imm_i_sext = {{20{d_imm_i[11]}}, d_imm_i[11:0]};
  wire [`REG_SIZE] d_imm_s_sext = {{20{d_imm_s[11]}}, d_imm_s[11:0]};
  wire [`REG_SIZE] d_imm_b_sext = {{19{d_imm_b[12]}}, d_imm_b[12:0]};
  wire [`REG_SIZE] d_imm_j_sext = {{11{d_imm_j[20]}}, d_imm_j[20:0]};

  wire [19:0] d_imm_u = d_insn[31:12];

  // data taken from register file
  logic [`REG_SIZE] d_rs1_data;
  logic [`REG_SIZE] d_rs2_data;

  // write enable -> DETERMINED AT WRITE STAGE
  logic we;

  // data to load into regfile -> DETERMINED AT WRITE STAGE or XD bypass
  logic[`REG_SIZE] rd_data;
  
  // REGFILE
  // WE, rd, and rd_data should come from the WRITE stage
  RegFile rf (
    .clk(clk),
    .rst(rst),
    .we(we),
    .rd(insn_rd),
    .rd_data(rd_data),
    .rs1(d_insn_rs1),
    .rs2(d_insn_rs2),
    .rs1_data(d_rs1_data),
    .rs2_data(d_rs2_data));
  
  // determine specific insn
  insn_set d_insn_set = '{
    insn_lui: d_insn_lui,
    insn_auipc: d_insn_auipc,
    insn_jal: d_insn_jal,
    insn_jalr: d_insn_jalr,

    insn_beq: d_insn_beq,
    insn_bne: d_insn_bne,
    insn_blt: d_insn_blt,
    insn_bge: d_insn_bge,
    insn_bltu: d_insn_bltu,
    insn_bgeu: d_insn_bgeu,
    insn_lb: d_insn_lb,
    insn_lh: d_insn_lh,
    insn_lw: d_insn_lw,
    insn_lbu: d_insn_lbu,
    insn_lhu: d_insn_lhu,

    insn_sb: d_insn_sb,
    insn_sh: d_insn_sh,
    insn_sw: d_insn_sw,

    insn_addi: d_insn_addi,
    insn_slti: d_insn_slti,
    insn_sltiu: d_insn_sltiu,
    insn_xori: d_insn_xori,
    insn_ori: d_insn_ori,
    insn_andi: d_insn_andi,

    insn_slli: d_insn_slli,
    insn_srli: d_insn_srli,
    insn_srai: d_insn_srai,

    insn_add: d_insn_add,
    insn_sub: d_insn_sub,
    insn_sll: d_insn_sll,
    insn_slt: d_insn_slt,
    insn_sltu: d_insn_sltu,
    insn_xor: d_insn_xor,
    insn_srl: d_insn_srl,
    insn_sra: d_insn_sra,
    insn_or: d_insn_or,
    insn_and: d_insn_and,

    insn_mul: d_insn_mul,
    insn_mulh: d_insn_mulh,
    insn_mulhsu: d_insn_mulhsu,
    insn_mulhu: d_insn_mulhu,
    insn_div: d_insn_div,
    insn_divu: d_insn_divu,
    insn_rem: d_insn_rem,
    insn_remu: d_insn_remu,

    insn_ecall: d_insn_ecall,
    insn_fence: d_insn_fence
  };
  wire d_insn_lui   = d_insn_opcode == OpLui;
  wire d_insn_auipc = d_insn_opcode == OpAuipc;
  wire d_insn_jal   = d_insn_opcode == OpJal;
  wire d_insn_jalr  = d_insn_opcode == OpJalr;

  wire d_insn_beq  = d_insn_opcode == OpBranch && d_insn_funct3 == 3'b000;
  wire d_insn_bne  = d_insn_opcode == OpBranch && d_insn_funct3 == 3'b001;
  wire d_insn_blt  = d_insn_opcode == OpBranch && d_insn_funct3 == 3'b100;
  wire d_insn_bge  = d_insn_opcode == OpBranch && d_insn_funct3 == 3'b101;
  wire d_insn_bltu = d_insn_opcode == OpBranch && d_insn_funct3 == 3'b110;
  wire d_insn_bgeu = d_insn_opcode == OpBranch && d_insn_funct3 == 3'b111;

  wire d_insn_lb  = d_insn_opcode == OpLoad && d_insn_funct3 == 3'b000;
  wire d_insn_lh  = d_insn_opcode == OpLoad && d_insn_funct3 == 3'b001;
  wire d_insn_lw  = d_insn_opcode == OpLoad && d_insn_funct3 == 3'b010;
  wire d_insn_lbu = d_insn_opcode == OpLoad && d_insn_funct3 == 3'b100;
  wire d_insn_lhu = d_insn_opcode == OpLoad && d_insn_funct3 == 3'b101;

  wire d_insn_sb = d_insn_opcode == OpStore && d_insn_funct3 == 3'b000;
  wire d_insn_sh = d_insn_opcode == OpStore && d_insn_funct3 == 3'b001;
  wire d_insn_sw = d_insn_opcode == OpStore && d_insn_funct3 == 3'b010;

  wire d_insn_addi  = d_insn_opcode == OpRegImm && d_insn_funct3 == 3'b000;
  wire d_insn_slti  = d_insn_opcode == OpRegImm && d_insn_funct3 == 3'b010;
  wire d_insn_sltiu = d_insn_opcode == OpRegImm && d_insn_funct3 == 3'b011;
  wire d_insn_xori  = d_insn_opcode == OpRegImm && d_insn_funct3 == 3'b100;
  wire d_insn_ori   = d_insn_opcode == OpRegImm && d_insn_funct3 == 3'b110;
  wire d_insn_andi  = d_insn_opcode == OpRegImm && d_insn_funct3 == 3'b111;

  wire d_insn_slli = d_insn_opcode == OpRegImm && d_insn_funct3 == 3'b001 && d_insn_funct7 == 7'd0;
  wire d_insn_srli = d_insn_opcode == OpRegImm && d_insn_funct3 == 3'b101 && d_insn_funct7 == 7'd0;
  wire d_insn_srai = d_insn_opcode == OpRegImm && d_insn_funct3 == 3'b101 && d_insn_funct7 == 7'b0100000;

  wire d_insn_add  = d_insn_opcode == OpRegReg && d_insn_funct3 == 3'b000 && d_insn_funct7 == 7'd0;
  wire d_insn_sub  = d_insn_opcode == OpRegReg && d_insn_funct3 == 3'b000 && d_insn_funct7 == 7'b0100000;
  wire d_insn_sll  = d_insn_opcode == OpRegReg && d_insn_funct3 == 3'b001 && d_insn_funct7 == 7'd0;
  wire d_insn_slt  = d_insn_opcode == OpRegReg && d_insn_funct3 == 3'b010 && d_insn_funct7 == 7'd0;
  wire d_insn_sltu = d_insn_opcode == OpRegReg && d_insn_funct3 == 3'b011 && d_insn_funct7 == 7'd0;
  wire d_insn_xor  = d_insn_opcode == OpRegReg && d_insn_funct3 == 3'b100 && d_insn_funct7 == 7'd0;
  wire d_insn_srl  = d_insn_opcode == OpRegReg && d_insn_funct3 == 3'b101 && d_insn_funct7 == 7'd0;
  wire d_insn_sra  = d_insn_opcode == OpRegReg && d_insn_funct3 == 3'b101 && d_insn_funct7 == 7'b0100000;
  wire d_insn_or   = d_insn_opcode == OpRegReg && d_insn_funct3 == 3'b110 && d_insn_funct7 == 7'd0;
  wire d_insn_and  = d_insn_opcode == OpRegReg && d_insn_funct3 == 3'b111 && d_insn_funct7 == 7'd0;

  wire d_insn_mul    = d_insn_opcode == OpRegReg && d_insn_funct7 == 7'd1 && d_insn_funct3 == 3'b000;
  wire d_insn_mulh   = d_insn_opcode == OpRegReg && d_insn_funct7 == 7'd1 && d_insn_funct3 == 3'b001;
  wire d_insn_mulhsu = d_insn_opcode == OpRegReg && d_insn_funct7 == 7'd1 && d_insn_funct3 == 3'b010;
  wire d_insn_mulhu  = d_insn_opcode == OpRegReg && d_insn_funct7 == 7'd1 && d_insn_funct3 == 3'b011;
  wire d_insn_div    = d_insn_opcode == OpRegReg && d_insn_funct7 == 7'd1 && d_insn_funct3 == 3'b100;
  wire d_insn_divu   = d_insn_opcode == OpRegReg && d_insn_funct7 == 7'd1 && d_insn_funct3 == 3'b101;
  wire d_insn_rem    = d_insn_opcode == OpRegReg && d_insn_funct7 == 7'd1 && d_insn_funct3 == 3'b110;
  wire d_insn_remu   = d_insn_opcode == OpRegReg && d_insn_funct7 == 7'd1 && d_insn_funct3 == 3'b111;

  wire d_insn_ecall = insn_opcode == OpEnviron && d_insn[31:7] == 25'd0;
  wire d_insn_fence = insn_opcode == OpMiscMem;




  /****************/
  /* EXECUTE STAGE */
  /****************/

  stage_state_t execute_state;
  always_ff @(posedge clk) begin
    if (rst) begin
      execute_state <= '{
        pc: 0,
        insn: 0,
        cycle_status: CYCLE_RESET
      };
    end else begin
      begin
        execute_state <= '{
          pc: d_pc_current,
          insn: d_insn,
          cycle_status: d_cycle_status,
          
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

          // insn_set containing the insn signal
          insn_set: d_insn_set,

          // memory signals
          // addr_to_dmem; // cannot determine until execute
          // store_data_to_dmem; // 
          // store_we_to_dmem;


          //halt;

        };
      end
    end
  end

  // CLA inputs
  logic [31:0] cla_a;
  logic [31:0] cla_b;
  logic cla_cin;
  logic [31:0] cla_sum;

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
  assign unsigned_dividend = rs1_data[31] ? (~rs1_data + 1) : rs1_data;
  assign unsigned_divisor = rs2_data[31] ? (~rs2_data + 1) : rs2_data;

  // convert outputs from unsigned division to be signed
  assign signed_quotient = (rs1_data[31] ^ rs2_data[31]) ? (~unsigned_quotient + 1) : unsigned_quotient;
  assign signed_remainder = (rs1_data[31]) ? (~unsigned_remainder + 1) : unsigned_remainder;

  // need to wait 8 cycles to run
  DividerUnsignedPipelined divider(.clk(clk), .rst(rst), .stall(0), 
          .i_dividend(unsigned_dividend), .i_divisor(unsigned_divisor), 
          .o_quotient(unsigned_quotient), .o_remainder(unsigned_remainder));

  // Execute Signals
  logic x_we;
  logic [31:0] x_rd_data;

  logic [`REG_SIZE] x_pc = execute_state.pc;
  logic [`INSN_SIZE] x_insn = execute_state.insn;
  cycle_status_e x_cycle_status = execute_state.cycle_status;
  
  logic [4:0] x_insn_rs1 = execute_state.insn_rs1;
  logic [4:0] x_insn_rs2 = execute_state.insn_rs2;
  logic [4:0] x_insn_rd = execute_state.insn_rd;

  logic [11:0] x_imm_i = execute_state.imm_i;
  logic [11:0] x_imm_s = execute_state.imm_s;
  logic [12:0] x_imm_b = execute_state.imm_b;
  logic [20:0] x_imm_j = execute_state.imm_j;
  
  logic [`REG_SIZE] x_imm_i_sext = execute_state.imm_i_sext;
  logic [`REG_SIZE] x_imm_s_sext = execute_state.imm_s_sext;
  logic [`REG_SIZE] x_imm_b_sext = execute_state.imm_b_sext;
  logic [`REG_SIZE] x_imm_j_sext = execute_state.imm_j_sext;

  logic [19:0] x_imm_u = execute_state.imm_u;

  // data taken from register file
  logic [`REG_SIZE] x_rs1_data = execute_state.rs1_data;
  logic [`REG_SIZE] x_rs2_data = execute_state.rs2_data;

  // insn_set containing the insn signal
  insn_set x_insn_set = execute_state.insn_set;



  case ()
      OpLui: begin
        x_we = 1;
        rd_data = x_imm_u << 12;
               
      end

      OpAuipc : begin
        x_we = 1;
        rd_data = x_pc + (x_imm_u << 12);
      end
  endcase
  
  /****************/
  /* MEMORY STAGE */
  /****************/

  

  /****************/
  /* WRITE STAGE */
  /****************/

  // data to load into register
  logic [31:0] rd_data;

  // write enable
  logic we;
  
endmodule

module MemorySingleCycle #(
    parameter int NUM_WORDS = 512
) (
    // rst for both imem and dmem
    input wire rst,

    // clock for both imem and dmem. The memory reads/writes on @(negedge clk)
    input wire clk,

    // must always be aligned to a 4B boundary
    input wire [`REG_SIZE] pc_to_imem,

    // the value at memory location pc_to_imem
    output logic [`REG_SIZE] insn_from_imem,

    // must always be aligned to a 4B boundary
    input wire [`REG_SIZE] addr_to_dmem,

    // the value at memory location addr_to_dmem
    output logic [`REG_SIZE] load_data_from_dmem,

    // the value to be written to addr_to_dmem, controlled by store_we_to_dmem
    input wire [`REG_SIZE] store_data_to_dmem,

    // Each bit determines whether to write the corresponding byte of store_data_to_dmem to memory location addr_to_dmem.
    // E.g., 4'b1111 will write 4 bytes. 4'b0001 will write only the least-significant byte.
    input wire [3:0] store_we_to_dmem
);

  // memory is arranged as an array of 4B words
  logic [`REG_SIZE] mem_array[NUM_WORDS];

`ifdef SYNTHESIS
  initial begin
    $readmemh("mem_initial_contents.hex", mem_array);
  end
`endif

  always_comb begin
    // memory addresses should always be 4B-aligned
    assert (pc_to_imem[1:0] == 2'b00);
    assert (addr_to_dmem[1:0] == 2'b00);
  end

  localparam int AddrMsb = $clog2(NUM_WORDS) + 1;
  localparam int AddrLsb = 2;

  always @(negedge clk) begin
    if (rst) begin
    end else begin
      insn_from_imem <= mem_array[{pc_to_imem[AddrMsb:AddrLsb]}];
    end
  end

  always @(negedge clk) begin
    if (rst) begin
    end else begin
      if (store_we_to_dmem[0]) begin
        mem_array[addr_to_dmem[AddrMsb:AddrLsb]][7:0] <= store_data_to_dmem[7:0];
      end
      if (store_we_to_dmem[1]) begin
        mem_array[addr_to_dmem[AddrMsb:AddrLsb]][15:8] <= store_data_to_dmem[15:8];
      end
      if (store_we_to_dmem[2]) begin
        mem_array[addr_to_dmem[AddrMsb:AddrLsb]][23:16] <= store_data_to_dmem[23:16];
      end
      if (store_we_to_dmem[3]) begin
        mem_array[addr_to_dmem[AddrMsb:AddrLsb]][31:24] <= store_data_to_dmem[31:24];
      end
      // dmem is "read-first": read returns value before the write
      load_data_from_dmem <= mem_array[{addr_to_dmem[AddrMsb:AddrLsb]}];
    end
  end
endmodule

/* This design has just one clock for both processor and memory. */
module Processor (
    input  wire  clk,
    input  wire  rst,
    output logic halt,
    output wire [`REG_SIZE] trace_writeback_pc,
    output wire [`INSN_SIZE] trace_writeback_insn,
    output cycle_status_e trace_writeback_cycle_status
);

  wire [`INSN_SIZE] insn_from_imem;
  wire [`REG_SIZE] pc_to_imem, mem_data_addr, mem_data_loaded_value, mem_data_to_write;
  wire [3:0] mem_data_we;

  // This wire is set by cocotb to the name of the currently-running test, to make it easier
  // to see what is going on in the waveforms.
  wire [(8*32)-1:0] test_case;

  MemorySingleCycle #(
      .NUM_WORDS(8192)
  ) memory (
      .rst                (rst),
      .clk                (clk),
      // imem is read-only
      .pc_to_imem         (pc_to_imem),
      .insn_from_imem     (insn_from_imem),
      // dmem is read-write
      .addr_to_dmem       (mem_data_addr),
      .load_data_from_dmem(mem_data_loaded_value),
      .store_data_to_dmem (mem_data_to_write),
      .store_we_to_dmem   (mem_data_we)
  );

  DatapathPipelined datapath (
      .clk(clk),
      .rst(rst),
      .pc_to_imem(pc_to_imem),
      .insn_from_imem(insn_from_imem),
      .addr_to_dmem(mem_data_addr),
      .store_data_to_dmem(mem_data_to_write),
      .store_we_to_dmem(mem_data_we),
      .load_data_from_dmem(mem_data_loaded_value),
      .halt(halt),
      .trace_writeback_pc(trace_writeback_pc),
      .trace_writeback_insn(trace_writeback_insn),
      .trace_writeback_cycle_status(trace_writeback_cycle_status)
  );

endmodule
