/* INSERT NAME AND PENNKEY HERE */

`timescale 1ns / 1ns

// registers are 32 bits in RV32
`define REG_SIZE 31:0

// RV opcodes are 7 bits
`define OPCODE_SIZE 6:0

`include "../hw2b-cla/cla.sv"
`include "DividerUnsignedPipelined.sv"

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

module DatapathMultiCycle (
    input wire clk,
    input wire rst,
    output logic halt,
    output logic [`REG_SIZE] pc_to_imem,
    input wire [`REG_SIZE] insn_from_imem,
    // addr_to_dmem is a read-write port
    output logic [`REG_SIZE] addr_to_dmem,
    input wire [`REG_SIZE] load_data_from_dmem,
    output logic [`REG_SIZE] store_data_to_dmem,
    output logic [3:0] store_we_to_dmem
);

  
  // components of the instruction
  wire [6:0] insn_funct7;
  wire [4:0] insn_rs2;
  wire [4:0] insn_rs1;
  wire [2:0] insn_funct3;
  wire [4:0] insn_rd;
  wire [`OPCODE_SIZE] insn_opcode;

  // split R-type instruction - see section 2.2 of RiscV spec
  assign {insn_funct7, insn_rs2, insn_rs1, insn_funct3, insn_rd, insn_opcode} = insn_from_imem;

  // setup for I, S, B & J type instructions
  // I - short immediates and loads
  wire [11:0] imm_i;
  assign imm_i = insn_from_imem[31:20];
  wire [ 4:0] imm_shamt = insn_from_imem[24:20];

  // S - stores
  wire [11:0] imm_s;
  assign imm_s[11:5] = insn_funct7, imm_s[4:0] = insn_rd;

  // B - conditionals
  wire [12:0] imm_b;
  assign {imm_b[12], imm_b[10:5]} = insn_funct7, {imm_b[4:1], imm_b[11]} = insn_rd, imm_b[0] = 1'b0;

  // J - unconditional jumps
  wire [20:0] imm_j;
  assign {imm_j[20], imm_j[10:1], imm_j[11], imm_j[19:12], imm_j[0]} = {insn_from_imem[31:12], 1'b0};

  wire [`REG_SIZE] imm_i_sext = {{20{imm_i[11]}}, imm_i[11:0]};
  wire [`REG_SIZE] imm_s_sext = {{20{imm_s[11]}}, imm_s[11:0]};
  wire [`REG_SIZE] imm_b_sext = {{19{imm_b[12]}}, imm_b[12:0]};
  wire [`REG_SIZE] imm_j_sext = {{11{imm_j[20]}}, imm_j[20:0]};

  // ADDED: U-type

  wire [19:0] imm_u = insn_from_imem[31:12];

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

  wire insn_lui   = insn_opcode == OpLui;
  wire insn_auipc = insn_opcode == OpAuipc;
  wire insn_jal   = insn_opcode == OpJal;
  wire insn_jalr  = insn_opcode == OpJalr;

  wire insn_beq  = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b000;
  wire insn_bne  = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b001;
  wire insn_blt  = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b100;
  wire insn_bge  = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b101;
  wire insn_bltu = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b110;
  wire insn_bgeu = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b111;

  wire insn_lb  = insn_opcode == OpLoad && insn_from_imem[14:12] == 3'b000;
  wire insn_lh  = insn_opcode == OpLoad && insn_from_imem[14:12] == 3'b001;
  wire insn_lw  = insn_opcode == OpLoad && insn_from_imem[14:12] == 3'b010;
  wire insn_lbu = insn_opcode == OpLoad && insn_from_imem[14:12] == 3'b100;
  wire insn_lhu = insn_opcode == OpLoad && insn_from_imem[14:12] == 3'b101;

  wire insn_sb = insn_opcode == OpStore && insn_from_imem[14:12] == 3'b000;
  wire insn_sh = insn_opcode == OpStore && insn_from_imem[14:12] == 3'b001;
  wire insn_sw = insn_opcode == OpStore && insn_from_imem[14:12] == 3'b010;

  wire insn_addi  = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b000;
  wire insn_slti  = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b010;
  wire insn_sltiu = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b011;
  wire insn_xori  = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b100;
  wire insn_ori   = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b110;
  wire insn_andi  = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b111;

  wire insn_slli = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b001 && insn_from_imem[31:25] == 7'd0;
  wire insn_srli = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b101 && insn_from_imem[31:25] == 7'd0;
  wire insn_srai = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b101 && insn_from_imem[31:25] == 7'b0100000;

  wire insn_add  = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b000 && insn_from_imem[31:25] == 7'd0;
  wire insn_sub  = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b000 && insn_from_imem[31:25] == 7'b0100000;
  wire insn_sll  = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b001 && insn_from_imem[31:25] == 7'd0;
  wire insn_slt  = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b010 && insn_from_imem[31:25] == 7'd0;
  wire insn_sltu = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b011 && insn_from_imem[31:25] == 7'd0;
  wire insn_xor  = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b100 && insn_from_imem[31:25] == 7'd0;
  wire insn_srl  = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b101 && insn_from_imem[31:25] == 7'd0;
  wire insn_sra  = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b101 && insn_from_imem[31:25] == 7'b0100000;
  wire insn_or   = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b110 && insn_from_imem[31:25] == 7'd0;
  wire insn_and  = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b111 && insn_from_imem[31:25] == 7'd0;

  wire insn_mul    = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b000;
  wire insn_mulh   = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b001;
  wire insn_mulhsu = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b010;
  wire insn_mulhu  = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b011;
  wire insn_div    = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b100;
  wire insn_divu   = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b101;
  wire insn_rem    = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b110;
  wire insn_remu   = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b111;

  wire insn_ecall = insn_opcode == OpEnviron && insn_from_imem[31:7] == 25'd0;
  wire insn_fence = insn_opcode == OpMiscMem;

  // this code is only for simulation, not synthesis
  `ifndef SYNTHESIS
  `include "../hw3-singlecycle/RvDisassembler.sv"
  string disasm_string;
  always_comb begin
    disasm_string = rv_disasm(insn_from_imem);
  end
  // HACK: get disasm_string to appear in GtkWave, which can apparently show only wire/logic...
  wire [(8*32)-1:0] disasm_wire;
  genvar i;
  for (i = 0; i < 32; i = i + 1) begin : gen_disasm
    assign disasm_wire[(((i+1))*8)-1:((i)*8)] = disasm_string[31-i];
  end
  `endif

  // program counter
  logic [`REG_SIZE] pcNext, pcCurrent;
  always @(posedge clk) begin
    if (rst) begin
      pcCurrent <= 32'd0;
    end else begin
      pcCurrent <= pcNext;
    end
  end
  assign pc_to_imem = pcCurrent;

  // cycle/insn_from_imem counters
  logic [`REG_SIZE] cycles_current, num_insns_current;
  always @(posedge clk) begin
    if (rst) begin
      cycles_current <= 0;
      num_insns_current <= 0;
    end else begin
      cycles_current <= cycles_current + 1;
      if (!rst && divide_count == 0) begin
        
        num_insns_current <= num_insns_current + 1;
        // ADJUSTMENT FOR DIVIDE INSNS
      end
    end
  end

  wire [`REG_SIZE] rs1_data;
  wire [`REG_SIZE] rs2_data;
  RegFile rf (
    .clk(clk),
    .rst(rst),
    .we(we),
    .rd(insn_rd),
    .rd_data(rd_data),
    .rs1(insn_rs1),
    .rs2(insn_rs2),
    .rs1_data(rs1_data),
    .rs2_data(rs2_data));

  // data to load into register
  logic [31:0] rd_data;

  // write enable
  logic we;

  logic illegal_insn;

  // sum for register register instructions
  // regregsum = rs1_data + rs2_data
  wire [31:0] regregsum;
  cla regregadder(.a(rs1_data), .b(rs2_data), .cin(0), .sum(regregsum));

  // diff for register register instructions
  // regregdiff = rs1_data - rs2_data
  wire [31:0] regregdiff;
  cla regregsubtracter(.a(rs1_data), .b(~rs2_data), .cin(1), .sum(regregdiff));

  // sum for register immediate instructions
  // regimmsum = rs1_data + imm_i_sext
  wire[31:0] regimmsum;
  cla regimmadder(.a(rs1_data), .b(imm_i_sext), .cin(0), .sum(regimmsum));

  // intermediary for multiplier instructions
  logic [63:0] multiple;
  logic [31:0] product_temp;

  // divider signed
  wire[31:0] squotient;
  wire[31:0] sremainder;

  wire [31:0] true_squotient;
  wire [31:0] true_sremainder;
  
  wire [31:0] sdivisor;
  wire [31:0] sdividend;

  //convert dividend and divisor to unsigned
  
  assign sdividend = rs1_data[31] ? (~rs1_data + 1) : rs1_data;
  //assign sdividend = rs1_data;
  assign sdivisor = rs2_data[31] ? (~rs2_data + 1) : rs2_data;

  // convert true quotient negative if applicable
  assign true_squotient = (rs1_data[31] ^ rs2_data[31]) ? (~squotient + 1) : squotient;
  assign true_sremainder = (rs1_data[31]) ? (~sremainder + 1) : sremainder;

  // need to wait 8 cycles to run
  DividerUnsignedPipelined sdivider(.clk(clk), .rst(rst), .stall(0), 
          .i_dividend(sdividend), .i_divisor(sdivisor), .o_quotient(squotient), .o_remainder(sremainder));

  // // divider unsigned
  wire[31:0] uquotient;
  wire[31:0] uremainder;

  DividerUnsignedPipelined udivider(.clk(clk), .rst(rst), .stall(0), 
          .i_dividend(rs1_data), .i_divisor(rs2_data), .o_quotient(uquotient), .o_remainder(uremainder));

  // handle divide insns -> wait 8 clock cycles instead of 1

  // signal to determine divide insns
  wire divide_insn = insn_div | insn_divu | insn_rem | insn_remu;

  // if divide_insn == 1, we need to wait 8 cycles
  // if we increment divide_count by one every divide cycle, when when we are done,
  // the divide count will overflow and go back to 0
  logic[2:0] divide_count;
  
  always @(posedge clk) begin
    if (rst) begin
      divide_count <= 0;
    end else if (divide_insn) begin
      divide_count <= divide_count + 1;
    end
  end

  
  // memory variables
  assign addr_to_dmem = mem;

  logic [31:0] mem;

  wire[31:0] raw_mem = rs1_data + imm_s_sext;

  logic[31:0] inverted_rs1data = (~rs1_data) + 32'b1;
  
  always_comb begin
    illegal_insn = 1'b0;
    we = 0;
    rd_data = 0;
    halt = 0;
    multiple = 0;
    
    mem = 0;
    store_data_to_dmem = 0;
    store_we_to_dmem = 0;
    pcNext = pcCurrent + 4;

    //addr_to_dmem = 0;    
    case (insn_opcode)
      OpLui: begin
        we = 1;
        rd_data = imm_u << 12;
               
      end

      OpAuipc : begin
        we = 1;
        rd_data = pcCurrent + (imm_u << 12);
      end

      // I-TYPE
      OpRegImm : begin // rs_data = rs1_data _ immi
        we = 1;
        
        case (1)
          insn_addi: begin
            rd_data = regimmsum;
          end
          insn_slti: begin
            rd_data = $signed(rs1_data) < $signed(imm_i_sext) ? 1 : 0;
          end
          insn_sltiu: begin
            rd_data = rs1_data < imm_i_sext ? 1 : 0;
          end
          insn_xori: begin
            rd_data = rs1_data ^ imm_i_sext;
          end
          insn_ori: begin
            rd_data = rs1_data | imm_i_sext;
          end
          insn_andi: begin
            rd_data = rs1_data & imm_i_sext;
          end
          insn_slli: begin
            rd_data = rs1_data << imm_i[4:0];
          end
          insn_srli: begin
            rd_data = rs1_data >> imm_i[4:0];
          end
          insn_srai: begin
            rd_data = $signed(rs1_data) >>> (imm_i[4:0]);
          end
          
        endcase
      // R-TYPE 
      end
      OpRegReg: begin // rs_data = rs1_data _ rs2_data
        we = 1;
        case (1) 
          insn_add: begin
            rd_data = regregsum;
          end
          insn_sub: begin
            rd_data = regregdiff;
          end
          insn_sll: begin
            rd_data = rs1_data << rs2_data[4:0];
          end
          insn_slt: begin
            rd_data = $signed(rs1_data) < $signed(rs2_data) ? 1 : 0;
          end
          insn_sltu: begin
            rd_data = rs1_data < rs2_data ? 1 : 0;
          end
          insn_xor: begin
            rd_data = rs1_data ^ rs2_data;
          end
          insn_srl: begin
            rd_data = rs1_data >> (rs2_data[4:0]);
          end
          insn_sra: begin
            rd_data = $signed(rs1_data) >>> (rs2_data[4:0]);
          end
          insn_or: begin
            rd_data = rs1_data | rs2_data;
          end
          insn_and: begin
            rd_data = rs1_data & rs2_data;
          end
          // Multiply
          insn_mul: begin
            multiple = (rs1_data * rs2_data);
            rd_data = multiple[31:0];
          end
          insn_mulh: begin
            multiple = $signed(rs1_data) * $signed(rs2_data);
            rd_data = multiple[63:32];
          end
          insn_mulhsu: begin
            // if (rs1_data[31]) begin
            //   multiple = ~(inverted_rs1data * (rs2_data)) + 64'b1;
            //   rd_data = multiple[63:32];
            // end else begin
            //   multiple = (rs1_data) * $unsigned(rs2_data);
            //   rd_data = multiple[63:32];
            // end

            multiple = {{32{rs1_data[31]}}, rs1_data} * {{32{1'b0}}, rs2_data};
            //multiple = $signed(rs1_data) * (rs2_data);
            rd_data = multiple[63:32];
          end
          insn_mulhu: begin
            multiple = $unsigned(rs1_data) * $unsigned(rs2_data);
            rd_data = multiple[63:32];
          end
          // Divide
          insn_div: begin
            if (sdivisor == 0) begin
              // return -1 if dividing by zero
              rd_data = 32'hFFFFFFFF; 
            end else begin
              rd_data = true_squotient;
            end

            // check if divide is not finished yet
            if (divide_count != 3'b111) begin
              pcNext = pcCurrent;
            end
          end
          insn_divu: begin
            rd_data = uquotient;
            // check if divide is not finished yet
            if (divide_count != 3'b111) begin
              pcNext = pcCurrent;
              
            end
          end
          // Modulus
          insn_rem: begin
            rd_data = true_sremainder;
            // check if divide is not finished yet
            if (divide_count != 3'b111) begin
              pcNext = pcCurrent;
              
            end
          end
          insn_remu: begin
            rd_data = uremainder;
            // check if divide is not finished yet
            if (divide_count != 3'b111) begin
              pcNext = pcCurrent;

            end
          end

      endcase

      end  
          
      OpBranch: begin
        case (1)
          insn_beq: begin
            if (rs1_data == rs2_data) begin
              pcNext = pcCurrent + (imm_b_sext);
            end 
          end
          insn_bne: begin
            if (rs1_data != rs2_data) begin
              pcNext = pcCurrent + (imm_b_sext);
            end
          end
          insn_blt: begin
            if ($signed(rs1_data) < $signed(rs2_data)) begin
              pcNext = pcCurrent + (imm_b_sext);
            end
          end
          insn_bge: begin
            if ($signed(rs1_data) >= $signed(rs2_data)) begin
              pcNext = pcCurrent + (imm_b_sext);
            end
          end
          insn_bltu: begin
            if (rs1_data < rs2_data) begin
              pcNext = pcCurrent + (imm_b_sext);
            end
          end
          insn_bgeu: begin
            if (rs1_data >= rs2_data) begin
              pcNext = pcCurrent + (imm_b_sext);
            end
          end
         
        endcase
        
      end

      OpLoad: begin
        we = 1;
        mem = regimmsum & 32'hFFFFFFFC;
        case (1) 
          insn_lb: begin
            // offset: 0, 1, 2, 3           
            case (regimmsum[1:0])
              0: begin
                // load first byte
                rd_data = {{24{load_data_from_dmem[7]}}, load_data_from_dmem[7:0]};
              end
              1: begin
                // load second byte
                rd_data = {{24{load_data_from_dmem[15]}}, load_data_from_dmem[15:8]};
              end
              2: begin
                // load third byte
                rd_data = {{24{load_data_from_dmem[23]}}, load_data_from_dmem[23:16]};
              end
              3: begin
                // load fourth byte
                rd_data = {{24{load_data_from_dmem[31]}}, load_data_from_dmem[31:24]};
              end
            endcase
            
          end
          insn_lh: begin
            // offset: 0 or 1
            
            
            if (regimmsum[1]) begin
              // load the second half of the word
              rd_data = {{16{load_data_from_dmem[31]}}, load_data_from_dmem[31:16]};
            end else begin
              // load the first half of the word
              rd_data = {{16{load_data_from_dmem[15]}}, load_data_from_dmem[15:0]};
            end
            
          end
          insn_lw: begin
            rd_data = load_data_from_dmem;
          end
          insn_lbu: begin 
            // offset: 0, 1, 2, 3      (zero extended)     
            case (regimmsum[1:0])
              0: begin
                // load first byte
                rd_data = {{24{1'b0}}, load_data_from_dmem[7:0]};
              end
              1: begin
                // load second byte
                rd_data = {{24{1'b0}}, load_data_from_dmem[15:8]};
              end
              2: begin
                // load third byte
                rd_data = {{24{1'b0}}, load_data_from_dmem[23:16]};
              end
              3: begin
                // load fourth byte
                rd_data = {{24{1'b0}}, load_data_from_dmem[31:24]};
              end
            endcase
          end
          insn_lhu: begin
            if (regimmsum[1]) begin
              // load the second half of the word (zero extended)
              rd_data = {{16{1'b0}}, load_data_from_dmem[31:16]};
            end else begin
              // load the first half of the word (zero extended)
              rd_data = {{16{1'b0}}, load_data_from_dmem[15:0]};
            end
          end
        endcase
      end

      OpStore: begin
        mem = (raw_mem) & 32'hFFFFFFFC;
        case (1)
          insn_sb: begin
            // store only one byte
            store_we_to_dmem = 4'b1 << raw_mem[1:0];
            store_data_to_dmem = ({24'd0, rs2_data[7:0]}) << ({3'b0, raw_mem[1:0]} << 3);
            
          end
          insn_sh: begin
            // store 2 bytes
            store_we_to_dmem = 4'b11 << raw_mem[1:0];
           
            store_data_to_dmem = ({16'd0, rs2_data[15:0]}) << ({3'b0, raw_mem[1:0]} << 3);
          end
          insn_sw: begin
            // store all 4 bytes
            store_we_to_dmem = 4'b1111;
            store_data_to_dmem = rs2_data;
          end
        endcase
        
      end

      OpJalr: begin
        we = 1;
        // load next instruction in register
        rd_data = pcCurrent + 4;
        // jump to desired location
        pcNext = (rs1_data + imm_i_sext) & ~(32'd1);
      end

      OpJal: begin
        we = 1;
        // load next instruction in register
        rd_data = pcCurrent + 4;
        // jump to desired offset
        pcNext = pcCurrent + imm_j_sext;

      end

      OpEnviron: begin
        // ecall > halt program, transfer control to OS (we don't have to do for now)
        halt = 1;
        
      end

      OpMiscMem: begin
        // fence > do nothing but increment PC

      end

      default: begin
        illegal_insn = 1'b1;
      end
    endcase
  end

endmodule

module MemorySingleCycle #(
    parameter int NUM_WORDS = 512
) (
    // rst for both imem and dmem
    input wire rst,

    // clock for both imem and dmem. See RiscvProcessor for clock details.
    input wire clock_mem,

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

  always @(posedge clock_mem) begin
    if (rst) begin
    end else begin
      insn_from_imem <= mem_array[{pc_to_imem[AddrMsb:AddrLsb]}];
    end
  end

  always @(negedge clock_mem) begin
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

/*
This shows the relationship between clock_proc and clock_mem. The clock_mem is
phase-shifted 90° from clock_proc. You could think of one proc cycle being
broken down into 3 parts. During part 1 (which starts @posedge clock_proc)
the current PC is sent to the imem. In part 2 (starting @posedge clock_mem) we
read from imem. In part 3 (starting @negedge clock_mem) we read/write memory and
prepare register/PC updates, which occur at @posedge clock_proc.

        ____
 proc: |    |______
           ____
 mem:  ___|    |___
*/
module Processor (
    input  wire  clock_proc,
    input  wire  clock_mem,
    input  wire  rst,
    output logic halt
);

  wire [`REG_SIZE] pc_to_imem, insn_from_imem, mem_data_addr, mem_data_loaded_value, mem_data_to_write;
  wire [3:0] mem_data_we;

  // This wire is set by cocotb to the name of the currently-running test, to make it easier
  // to see what is going on in the waveforms.
  wire [(8*32)-1:0] test_case;

  MemorySingleCycle #(
      .NUM_WORDS(8192)
  ) memory (
      .rst      (rst),
      .clock_mem (clock_mem),
      // imem is read-only
      .pc_to_imem(pc_to_imem),
      .insn_from_imem(insn_from_imem),
      // dmem is read-write
      .addr_to_dmem(mem_data_addr),
      .load_data_from_dmem(mem_data_loaded_value),
      .store_data_to_dmem (mem_data_to_write),
      .store_we_to_dmem  (mem_data_we)
  );

  DatapathMultiCycle datapath (
      .clk(clock_proc),
      .rst(rst),
      .pc_to_imem(pc_to_imem),
      .insn_from_imem(insn_from_imem),
      .addr_to_dmem(mem_data_addr),
      .store_data_to_dmem(mem_data_to_write),
      .store_we_to_dmem(mem_data_we),
      .load_data_from_dmem(mem_data_loaded_value),
      .halt(halt)
  );

endmodule
