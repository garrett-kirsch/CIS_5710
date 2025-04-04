module MyClockGen (
	input_clk_25MHz,
	clk_proc,
	locked
);
	input input_clk_25MHz;
	output wire clk_proc;
	output wire locked;
	wire clkfb;
	(* FREQUENCY_PIN_CLKI = "25" *) (* FREQUENCY_PIN_CLKOP = "20" *) (* ICP_CURRENT = "12" *) (* LPF_RESISTOR = "8" *) (* MFG_ENABLE_FILTEROPAMP = "1" *) (* MFG_GMCREF_SEL = "2" *) EHXPLLL #(
		.PLLRST_ENA("DISABLED"),
		.INTFB_WAKE("DISABLED"),
		.STDBY_ENABLE("DISABLED"),
		.DPHASE_SOURCE("DISABLED"),
		.OUTDIVIDER_MUXA("DIVA"),
		.OUTDIVIDER_MUXB("DIVB"),
		.OUTDIVIDER_MUXC("DIVC"),
		.OUTDIVIDER_MUXD("DIVD"),
		.CLKI_DIV(5),
		.CLKOP_ENABLE("ENABLED"),
		.CLKOP_DIV(30),
		.CLKOP_CPHASE(15),
		.CLKOP_FPHASE(0),
		.FEEDBK_PATH("INT_OP"),
		.CLKFB_DIV(4)
	) pll_i(
		.RST(1'b0),
		.STDBY(1'b0),
		.CLKI(input_clk_25MHz),
		.CLKOP(clk_proc),
		.CLKFB(clkfb),
		.CLKINTFB(clkfb),
		.PHASESEL0(1'b0),
		.PHASESEL1(1'b0),
		.PHASEDIR(1'b1),
		.PHASESTEP(1'b1),
		.PHASELOADREG(1'b1),
		.PLLWAKESYNC(1'b0),
		.ENCLKOP(1'b0),
		.LOCK(locked)
	);
endmodule
module gp1 (
	a,
	b,
	g,
	p
);
	input wire a;
	input wire b;
	output wire g;
	output wire p;
	assign g = a & b;
	assign p = a | b;
endmodule
module gp4 (
	gin,
	pin,
	cin,
	gout,
	pout,
	cout
);
	input wire [3:0] gin;
	input wire [3:0] pin;
	input wire cin;
	output wire gout;
	output wire pout;
	output wire [2:0] cout;
	assign pout = &pin;
	assign gout = ((gin[3] | (pin[3] & gin[2])) | (&pin[3:2] & gin[1])) | (&pin[3:1] & gin[0]);
	assign cout[0] = gin[0] | (pin[0] & cin);
	assign cout[1] = (gin[1] | (pin[1] & gin[0])) | (&pin[1:0] & cin);
	assign cout[2] = ((gin[2] | (pin[2] & gin[1])) | (&pin[2:1] & gin[0])) | (&pin[2:0] & cin);
endmodule
module gp8 (
	gin,
	pin,
	cin,
	gout,
	pout,
	cout
);
	input wire [7:0] gin;
	input wire [7:0] pin;
	input wire cin;
	output wire gout;
	output wire pout;
	output wire [6:0] cout;
	wire gout0;
	wire pout0;
	wire gout1;
	wire pout1;
	gp4 g0(
		.gin(gin[3:0]),
		.pin(pin[3:0]),
		.cin(cin),
		.gout(gout0),
		.pout(pout0),
		.cout(cout[2:0])
	);
	assign cout[3] = gout0 | (pout0 & cin);
	gp4 g1(
		.gin(gin[7:4]),
		.pin(pin[7:4]),
		.cin(cout[3]),
		.gout(gout1),
		.pout(pout1),
		.cout(cout[6:4])
	);
	assign pout = pout0 & pout1;
	assign gout = gout1 | (gout0 & pout1);
endmodule
module cla (
	a,
	b,
	cin,
	sum
);
	input wire [31:0] a;
	input wire [31:0] b;
	input wire cin;
	output wire [31:0] sum;
	wire [31:0] c;
	wire [31:0] g;
	wire [31:0] p;
	wire [3:0] gout;
	wire [3:0] pout;
	genvar _gv_i_1;
	generate
		for (_gv_i_1 = 0; _gv_i_1 < 32; _gv_i_1 = _gv_i_1 + 1) begin : genblk1
			localparam i = _gv_i_1;
			gp1 gp1(
				.a(a[i]),
				.b(b[i]),
				.g(g[i]),
				.p(p[i])
			);
		end
	endgenerate
	wire cout1;
	wire cout2;
	wire cout3;
	wire co;
	gp8 g_1(
		.gin(g[7:0]),
		.pin(p[7:0]),
		.cin(cin),
		.gout(gout[0]),
		.pout(pout[0]),
		.cout(c[7:1])
	);
	assign cout1 = gout[0] | (pout[0] & cin);
	gp8 g_2(
		.gin(g[15:8]),
		.pin(p[15:8]),
		.cin(cout1),
		.gout(gout[1]),
		.pout(pout[1]),
		.cout(c[15:9])
	);
	assign cout2 = gout[1] | (pout[1] & cout1);
	gp8 g_3(
		.gin(g[23:16]),
		.pin(p[23:16]),
		.cin(cout2),
		.gout(gout[2]),
		.pout(pout[2]),
		.cout(c[23:17])
	);
	assign cout3 = gout[2] | (pout[2] & cout2);
	gp8 g_4(
		.gin(g[31:24]),
		.pin(p[31:24]),
		.cin(cout3),
		.gout(gout[3]),
		.pout(pout[3]),
		.cout(c[31:25])
	);
	assign co = gout[3] | (pout[3] & cout3);
	assign c[0] = cin;
	assign c[8] = cout1;
	assign c[16] = cout2;
	assign c[24] = cout3;
	assign sum = (a ^ b) ^ c;
endmodule
module DividerUnsignedPipelined (
	clk,
	rst,
	stall,
	i_dividend,
	i_divisor,
	o_remainder,
	o_quotient
);
	input wire clk;
	input wire rst;
	input wire stall;
	input wire [31:0] i_dividend;
	input wire [31:0] i_divisor;
	output wire [31:0] o_remainder;
	output wire [31:0] o_quotient;
	reg [223:0] stored_dividend;
	reg [223:0] stored_remainder;
	reg [223:0] stored_quotient;
	reg [31:0] stored_divisor [0:6];
	wire [31:0] dividend [0:31];
	wire [31:0] remainder [0:31];
	wire [31:0] quotient [0:31];
	always @(posedge clk)
		if (rst) begin
			stored_dividend <= {7 {32'b00000000000000000000000000000000}};
			stored_quotient <= {7 {32'b00000000000000000000000000000000}};
			stored_remainder <= {7 {32'b00000000000000000000000000000000}};
		end
		else begin
			stored_dividend[192+:32] <= dividend[3];
			stored_quotient[192+:32] <= quotient[3];
			stored_remainder[192+:32] <= remainder[3];
			stored_dividend[160+:32] <= dividend[7];
			stored_quotient[160+:32] <= quotient[7];
			stored_remainder[160+:32] <= remainder[7];
			stored_dividend[128+:32] <= dividend[11];
			stored_quotient[128+:32] <= quotient[11];
			stored_remainder[128+:32] <= remainder[11];
			stored_dividend[96+:32] <= dividend[15];
			stored_quotient[96+:32] <= quotient[15];
			stored_remainder[96+:32] <= remainder[15];
			stored_dividend[64+:32] <= dividend[19];
			stored_quotient[64+:32] <= quotient[19];
			stored_remainder[64+:32] <= remainder[19];
			stored_dividend[32+:32] <= dividend[23];
			stored_quotient[32+:32] <= quotient[23];
			stored_remainder[32+:32] <= remainder[23];
			stored_dividend[0+:32] <= dividend[27];
			stored_quotient[0+:32] <= quotient[27];
			stored_remainder[0+:32] <= remainder[27];
			stored_divisor[0] <= i_divisor;
			stored_divisor[1] <= stored_divisor[0];
			stored_divisor[2] <= stored_divisor[1];
			stored_divisor[3] <= stored_divisor[2];
			stored_divisor[4] <= stored_divisor[3];
			stored_divisor[5] <= stored_divisor[4];
			stored_divisor[6] <= stored_divisor[5];
		end
	divu_1iter d1(
		.i_dividend(i_dividend),
		.i_divisor(i_divisor),
		.i_remainder(0),
		.i_quotient(0),
		.o_dividend(dividend[0]),
		.o_remainder(remainder[0]),
		.o_quotient(quotient[0])
	);
	genvar _gv_k_1;
	generate
		for (_gv_k_1 = 0; _gv_k_1 < 3; _gv_k_1 = _gv_k_1 + 1) begin : genblk1
			localparam k = _gv_k_1;
			divu_1iter d2(
				.i_dividend(dividend[k]),
				.i_divisor(i_divisor),
				.i_remainder(remainder[k]),
				.i_quotient(quotient[k]),
				.o_dividend(dividend[k + 1]),
				.o_remainder(remainder[k + 1]),
				.o_quotient(quotient[k + 1])
			);
		end
	endgenerate
	genvar _gv_j_1;
	generate
		for (_gv_j_1 = 0; _gv_j_1 < 7; _gv_j_1 = _gv_j_1 + 1) begin : genblk2
			localparam j = _gv_j_1;
			divu_1iter d3(
				.i_dividend(stored_dividend[(6 - j) * 32+:32]),
				.i_divisor(stored_divisor[j]),
				.i_remainder(stored_remainder[(6 - j) * 32+:32]),
				.i_quotient(stored_quotient[(6 - j) * 32+:32]),
				.o_dividend(dividend[4 * (j + 1)]),
				.o_remainder(remainder[4 * (j + 1)]),
				.o_quotient(quotient[4 * (j + 1)])
			);
			genvar _gv_i_2;
			for (_gv_i_2 = 4 * (j + 1); _gv_i_2 < ((4 * (j + 1)) + 3); _gv_i_2 = _gv_i_2 + 1) begin : genblk1
				localparam i = _gv_i_2;
				divu_1iter d4(
					.i_dividend(dividend[i]),
					.i_divisor(stored_divisor[j]),
					.i_remainder(remainder[i]),
					.i_quotient(quotient[i]),
					.o_dividend(dividend[i + 1]),
					.o_remainder(remainder[i + 1]),
					.o_quotient(quotient[i + 1])
				);
			end
		end
	endgenerate
	assign o_quotient = quotient[31];
	assign o_remainder = remainder[31];
endmodule
module divu_1iter (
	i_dividend,
	i_divisor,
	i_remainder,
	i_quotient,
	o_dividend,
	o_remainder,
	o_quotient
);
	input wire [31:0] i_dividend;
	input wire [31:0] i_divisor;
	input wire [31:0] i_remainder;
	input wire [31:0] i_quotient;
	output wire [31:0] o_dividend;
	output wire [31:0] o_remainder;
	output wire [31:0] o_quotient;
	wire [31:0] temp_rem = (i_remainder << 1) | (i_dividend >> 31);
	assign o_dividend = i_dividend << 1;
	assign o_quotient = (temp_rem < i_divisor ? i_quotient << 1 : (i_quotient << 1) | 1);
	assign o_remainder = (temp_rem < i_divisor ? temp_rem : temp_rem - i_divisor);
endmodule
module Disasm (
	insn,
	disasm
);
	parameter signed [7:0] PREFIX = "D";
	input wire [31:0] insn;
	output wire [255:0] disasm;
endmodule
module RegFile (
	rd,
	rd_data,
	rs1,
	rs1_data,
	rs2,
	rs2_data,
	clk,
	we,
	rst
);
	input wire [4:0] rd;
	input wire [31:0] rd_data;
	input wire [4:0] rs1;
	output wire [31:0] rs1_data;
	input wire [4:0] rs2;
	output wire [31:0] rs2_data;
	input wire clk;
	input wire we;
	input wire rst;
	localparam signed [31:0] NumRegs = 32;
	reg [1023:0] regs;
	wire [32:1] sv2v_tmp_D031E;
	assign sv2v_tmp_D031E = 0;
	always @(*) regs[992+:32] = sv2v_tmp_D031E;
	assign rs1_data = regs[(31 - rs1) * 32+:32];
	assign rs2_data = regs[(31 - rs2) * 32+:32];
	always @(posedge clk)
		if (rst)
			regs <= {NumRegs {32'b00000000000000000000000000000000}};
		else if (we && (rd != 0))
			regs[(31 - rd) * 32+:32] <= rd_data;
endmodule
module DatapathPipelined (
	clk,
	rst,
	pc_to_imem,
	insn_from_imem,
	addr_to_dmem,
	load_data_from_dmem,
	store_data_to_dmem,
	store_we_to_dmem,
	halt,
	trace_writeback_pc,
	trace_writeback_insn,
	trace_writeback_cycle_status
);
	reg _sv2v_0;
	input wire clk;
	input wire rst;
	output wire [31:0] pc_to_imem;
	input wire [31:0] insn_from_imem;
	output wire [31:0] addr_to_dmem;
	input wire [31:0] load_data_from_dmem;
	output wire [31:0] store_data_to_dmem;
	output wire [3:0] store_we_to_dmem;
	output wire halt;
	output wire [31:0] trace_writeback_pc;
	output wire [31:0] trace_writeback_insn;
	output wire [31:0] trace_writeback_cycle_status;
	localparam [6:0] OpLoad = 7'b0000011;
	localparam [6:0] OpStore = 7'b0100011;
	localparam [6:0] OpBranch = 7'b1100011;
	localparam [6:0] OpJalr = 7'b1100111;
	localparam [6:0] OpMiscMem = 7'b0001111;
	localparam [6:0] OpJal = 7'b1101111;
	localparam [6:0] OpRegImm = 7'b0010011;
	localparam [6:0] OpRegReg = 7'b0110011;
	localparam [6:0] OpEnviron = 7'b1110011;
	localparam [6:0] OpAuipc = 7'b0010111;
	localparam [6:0] OpLui = 7'b0110111;
	wire [4:0] d_insn_rs1;
	wire [4:0] d_insn_rs2;
	wire [31:0] d_rs1_data_temp;
	wire [31:0] d_rs2_data_temp;
	wire [4:0] w_insn_rd;
	wire [31:0] w_rd_data;
	wire w_we;
	RegFile rf(
		.clk(clk),
		.rst(rst),
		.we(w_we),
		.rd(w_insn_rd),
		.rd_data(w_rd_data),
		.rs1(d_insn_rs1),
		.rs2(d_insn_rs2),
		.rs1_data(d_rs1_data_temp),
		.rs2_data(d_rs2_data_temp)
	);
	wire [31:0] cla_a;
	reg [31:0] cla_b;
	reg cla_cin;
	wire [31:0] cla_sum;
	reg [31:0] x_rs1_data;
	assign cla_a = x_rs1_data;
	wire [31:0] x_imm_i_sext;
	wire [31:0] x_imm_s_sext;
	wire [46:0] x_insn_key;
	wire [6:0] x_opcode;
	reg [31:0] x_rs2_data;
	always @(*) begin
		if (_sv2v_0)
			;
		cla_b = x_rs2_data;
		cla_cin = 0;
		if (x_insn_key[18]) begin
			cla_b = ~x_rs2_data;
			cla_cin = 1;
		end
		else if (x_insn_key[28] || (x_opcode == OpLoad))
			cla_b = x_imm_i_sext;
		else if (x_opcode == OpStore)
			cla_b = x_imm_s_sext;
	end
	cla adder(
		.a(cla_a),
		.b(cla_b),
		.cin(cla_cin),
		.sum(cla_sum)
	);
	reg [63:0] multiple;
	wire [31:0] product_temp;
	wire [31:0] signed_quotient;
	wire [31:0] signed_remainder;
	wire [31:0] unsigned_divisor;
	wire [31:0] unsigned_dividend;
	wire [31:0] unsigned_quotient;
	wire [31:0] unsigned_remainder;
	reg [435:0] execute_state;
	assign unsigned_dividend = (execute_state[121] ? ~execute_state[121-:32] + 1 : execute_state[121-:32]);
	assign unsigned_divisor = (execute_state[89] ? ~execute_state[89-:32] + 1 : execute_state[89-:32]);
	assign signed_quotient = (execute_state[121] ^ execute_state[89] ? ~unsigned_quotient + 1 : unsigned_quotient);
	assign signed_remainder = (execute_state[121] ? ~unsigned_remainder + 1 : unsigned_remainder);
	DividerUnsignedPipelined divider(
		.clk(clk),
		.rst(rst),
		.stall(0),
		.i_dividend(unsigned_dividend),
		.i_divisor(unsigned_divisor),
		.o_quotient(unsigned_quotient),
		.o_remainder(unsigned_remainder)
	);
	reg [31:0] cycles_current;
	always @(posedge clk)
		if (rst)
			cycles_current <= 0;
		else
			cycles_current <= cycles_current + 1;
	reg [31:0] f_pc_current;
	wire [31:0] f_insn;
	reg [31:0] f_cycle_status;
	reg data_dependent_load;
	reg x_branch_taken;
	reg [31:0] x_branched_pc;
	always @(posedge clk)
		if (rst) begin
			f_pc_current <= 32'd0;
			f_cycle_status <= 32'd2;
		end
		else if (x_branch_taken) begin
			f_pc_current <= x_branched_pc;
			f_cycle_status <= 32'd2;
		end
		else if (data_dependent_load) begin
			f_pc_current <= f_pc_current;
			f_cycle_status <= 32'd2;
		end
		else begin
			f_cycle_status <= 32'd2;
			f_pc_current <= f_pc_current + 4;
		end
	assign pc_to_imem = f_pc_current;
	assign f_insn = insn_from_imem;
	wire [255:0] f_disasm;
	Disasm #(.PREFIX("F")) disasm_0fetch(
		.insn(f_insn),
		.disasm(f_disasm)
	);
	wire [255:0] d_disasm;
	reg [95:0] decode_state;
	Disasm #(.PREFIX("D")) disasm_1decode(
		.insn(decode_state[63-:32]),
		.disasm(d_disasm)
	);
	wire [255:0] x_disasm;
	Disasm #(.PREFIX("X")) disasm_2execute(
		.insn(execute_state[403-:32]),
		.disasm(x_disasm)
	);
	wire [255:0] m_disasm;
	reg [326:0] memory_state;
	Disasm #(.PREFIX("M")) disasm_3memory(
		.insn(memory_state[294-:32]),
		.disasm(m_disasm)
	);
	wire [255:0] w_disasm;
	reg [141:0] write_state;
	Disasm #(.PREFIX("W")) disasm_4write(
		.insn(write_state[109-:32]),
		.disasm(w_disasm)
	);
	wire [31:0] d_cycle_status;
	wire [31:0] d_insn;
	wire [31:0] d_pc_current;
	always @(posedge clk)
		if (rst)
			decode_state <= 96'h000000000000000000000001;
		else if (x_branch_taken)
			decode_state <= 96'h000000000000000000000004;
		else if (data_dependent_load)
			decode_state <= {d_pc_current, d_insn, d_cycle_status};
		else
			decode_state <= {f_pc_current, f_insn, f_cycle_status};
	assign d_pc_current = decode_state[95-:32];
	assign d_insn = decode_state[63-:32];
	assign d_cycle_status = decode_state[31-:32];
	wire [6:0] d_insn_funct7;
	wire [2:0] d_insn_funct3;
	wire [4:0] d_insn_rd;
	wire [4:0] d_insn_rd_temp;
	wire [6:0] d_insn_opcode;
	assign {d_insn_funct7, d_insn_rs2, d_insn_rs1, d_insn_funct3, d_insn_rd_temp, d_insn_opcode} = d_insn;
	assign d_insn_rd = (d_insn_opcode == OpBranch ? 0 : d_insn_rd_temp);
	wire [11:0] d_imm_i;
	assign d_imm_i = d_insn[31:20];
	wire [11:0] d_imm_s;
	assign d_imm_s[11:5] = d_insn_funct7;
	assign d_imm_s[4:0] = d_insn_rd;
	wire [12:0] d_imm_b;
	assign {d_imm_b[12], d_imm_b[10:5]} = d_insn_funct7;
	assign {d_imm_b[4:1], d_imm_b[11]} = d_insn_rd_temp;
	assign d_imm_b[0] = 1'b0;
	wire [20:0] d_imm_j;
	assign {d_imm_j[20], d_imm_j[10:1], d_imm_j[11], d_imm_j[19:12], d_imm_j[0]} = {d_insn[31:12], 1'b0};
	wire [31:0] d_imm_i_sext;
	wire [31:0] d_imm_s_sext;
	wire [31:0] d_imm_b_sext;
	wire [31:0] d_imm_j_sext;
	assign d_imm_i_sext = {{20 {d_imm_i[11]}}, d_imm_i[11:0]};
	assign d_imm_s_sext = {{20 {d_imm_s[11]}}, d_imm_s[11:0]};
	assign d_imm_b_sext = {{19 {d_imm_b[12]}}, d_imm_b[12:0]};
	assign d_imm_j_sext = {{11 {d_imm_j[20]}}, d_imm_j[20:0]};
	wire [19:0] d_imm_u;
	assign d_imm_u = d_insn[31:12];
	reg [31:0] d_rs1_data;
	reg [31:0] d_rs2_data;
	always @(*) begin
		if (_sv2v_0)
			;
		d_rs1_data = d_rs1_data_temp;
		d_rs2_data = d_rs2_data_temp;
		if ((w_insn_rd == d_insn_rs1) && (d_insn_rs1 != 0))
			d_rs1_data = w_rd_data;
		if ((w_insn_rd == d_insn_rs2) && (d_insn_rs2 != 0))
			d_rs2_data = w_rd_data;
	end
	wire load_data_dependency_stall;
	wire [4:0] x_insn_rd;
	assign load_data_dependency_stall = (x_opcode == OpLoad) && ((x_insn_rd == d_insn_rs1) || (x_insn_rd == d_insn_rs2));
	wire [46:0] d_insn_key;
	assign d_insn_key[46] = d_insn_opcode == OpLui;
	assign d_insn_key[45] = d_insn_opcode == OpAuipc;
	assign d_insn_key[44] = d_insn_opcode == OpJal;
	assign d_insn_key[43] = d_insn_opcode == OpJalr;
	assign d_insn_key[42] = (d_insn_opcode == OpBranch) && (d_insn_funct3 == 3'b000);
	assign d_insn_key[41] = (d_insn_opcode == OpBranch) && (d_insn_funct3 == 3'b001);
	assign d_insn_key[40] = (d_insn_opcode == OpBranch) && (d_insn_funct3 == 3'b100);
	assign d_insn_key[39] = (d_insn_opcode == OpBranch) && (d_insn_funct3 == 3'b101);
	assign d_insn_key[38] = (d_insn_opcode == OpBranch) && (d_insn_funct3 == 3'b110);
	assign d_insn_key[37] = (d_insn_opcode == OpBranch) && (d_insn_funct3 == 3'b111);
	assign d_insn_key[36] = (d_insn_opcode == OpLoad) && (d_insn_funct3 == 3'b000);
	assign d_insn_key[35] = (d_insn_opcode == OpLoad) && (d_insn_funct3 == 3'b001);
	assign d_insn_key[34] = (d_insn_opcode == OpLoad) && (d_insn_funct3 == 3'b010);
	assign d_insn_key[33] = (d_insn_opcode == OpLoad) && (d_insn_funct3 == 3'b100);
	assign d_insn_key[32] = (d_insn_opcode == OpLoad) && (d_insn_funct3 == 3'b101);
	assign d_insn_key[31] = (d_insn_opcode == OpStore) && (d_insn_funct3 == 3'b000);
	assign d_insn_key[30] = (d_insn_opcode == OpStore) && (d_insn_funct3 == 3'b001);
	assign d_insn_key[29] = (d_insn_opcode == OpStore) && (d_insn_funct3 == 3'b010);
	assign d_insn_key[28] = (d_insn_opcode == OpRegImm) && (d_insn_funct3 == 3'b000);
	assign d_insn_key[27] = (d_insn_opcode == OpRegImm) && (d_insn_funct3 == 3'b010);
	assign d_insn_key[26] = (d_insn_opcode == OpRegImm) && (d_insn_funct3 == 3'b011);
	assign d_insn_key[25] = (d_insn_opcode == OpRegImm) && (d_insn_funct3 == 3'b100);
	assign d_insn_key[24] = (d_insn_opcode == OpRegImm) && (d_insn_funct3 == 3'b110);
	assign d_insn_key[23] = (d_insn_opcode == OpRegImm) && (d_insn_funct3 == 3'b111);
	assign d_insn_key[22] = ((d_insn_opcode == OpRegImm) && (d_insn_funct3 == 3'b001)) && (d_insn_funct7 == 7'd0);
	assign d_insn_key[21] = ((d_insn_opcode == OpRegImm) && (d_insn_funct3 == 3'b101)) && (d_insn_funct7 == 7'd0);
	assign d_insn_key[20] = ((d_insn_opcode == OpRegImm) && (d_insn_funct3 == 3'b101)) && (d_insn_funct7 == 7'b0100000);
	assign d_insn_key[19] = ((d_insn_opcode == OpRegReg) && (d_insn_funct3 == 3'b000)) && (d_insn_funct7 == 7'd0);
	assign d_insn_key[18] = ((d_insn_opcode == OpRegReg) && (d_insn_funct3 == 3'b000)) && (d_insn_funct7 == 7'b0100000);
	assign d_insn_key[17] = ((d_insn_opcode == OpRegReg) && (d_insn_funct3 == 3'b001)) && (d_insn_funct7 == 7'd0);
	assign d_insn_key[16] = ((d_insn_opcode == OpRegReg) && (d_insn_funct3 == 3'b010)) && (d_insn_funct7 == 7'd0);
	assign d_insn_key[15] = ((d_insn_opcode == OpRegReg) && (d_insn_funct3 == 3'b011)) && (d_insn_funct7 == 7'd0);
	assign d_insn_key[14] = ((d_insn_opcode == OpRegReg) && (d_insn_funct3 == 3'b100)) && (d_insn_funct7 == 7'd0);
	assign d_insn_key[13] = ((d_insn_opcode == OpRegReg) && (d_insn_funct3 == 3'b101)) && (d_insn_funct7 == 7'd0);
	assign d_insn_key[12] = ((d_insn_opcode == OpRegReg) && (d_insn_funct3 == 3'b101)) && (d_insn_funct7 == 7'b0100000);
	assign d_insn_key[11] = ((d_insn_opcode == OpRegReg) && (d_insn_funct3 == 3'b110)) && (d_insn_funct7 == 7'd0);
	assign d_insn_key[10] = ((d_insn_opcode == OpRegReg) && (d_insn_funct3 == 3'b111)) && (d_insn_funct7 == 7'd0);
	assign d_insn_key[9] = ((d_insn_opcode == OpRegReg) && (d_insn_funct7 == 7'd1)) && (d_insn_funct3 == 3'b000);
	assign d_insn_key[8] = ((d_insn_opcode == OpRegReg) && (d_insn_funct7 == 7'd1)) && (d_insn_funct3 == 3'b001);
	assign d_insn_key[7] = ((d_insn_opcode == OpRegReg) && (d_insn_funct7 == 7'd1)) && (d_insn_funct3 == 3'b010);
	assign d_insn_key[6] = ((d_insn_opcode == OpRegReg) && (d_insn_funct7 == 7'd1)) && (d_insn_funct3 == 3'b011);
	assign d_insn_key[5] = ((d_insn_opcode == OpRegReg) && (d_insn_funct7 == 7'd1)) && (d_insn_funct3 == 3'b100);
	assign d_insn_key[4] = ((d_insn_opcode == OpRegReg) && (d_insn_funct7 == 7'd1)) && (d_insn_funct3 == 3'b101);
	assign d_insn_key[3] = ((d_insn_opcode == OpRegReg) && (d_insn_funct7 == 7'd1)) && (d_insn_funct3 == 3'b110);
	assign d_insn_key[2] = ((d_insn_opcode == OpRegReg) && (d_insn_funct7 == 7'd1)) && (d_insn_funct3 == 3'b111);
	assign d_insn_key[1] = (d_insn_opcode == OpEnviron) && (d_insn[31:7] == 25'd0);
	assign d_insn_key[0] = d_insn_opcode == OpMiscMem;
	wire [435:0] normal_execute_state;
	assign normal_execute_state = {d_pc_current, d_insn, d_cycle_status, d_insn_opcode, d_insn_rd, d_imm_i, d_imm_s, d_imm_b, d_imm_j, d_imm_i_sext, d_imm_s_sext, d_imm_b_sext, d_imm_j_sext, d_imm_u, d_rs1_data, d_rs2_data, d_insn_rs1, d_insn_rs2, d_insn_key, 1'd0};
	always @(posedge clk)
		if (rst) begin
			execute_state <= 0;
			execute_state[371-:32] <= 32'd1;
		end
		else if (x_branch_taken) begin
			execute_state <= 0;
			execute_state[371-:32] <= 32'd4;
		end
		else if (data_dependent_load) begin
			execute_state <= 0;
			execute_state[371-:32] <= 32'd16;
		end
		else
			execute_state <= normal_execute_state;
	reg x_we;
	reg [31:0] x_rd_data;
	wire [31:0] x_pc;
	assign x_pc = execute_state[435-:32];
	wire [31:0] x_insn;
	assign x_insn = execute_state[403-:32];
	wire [31:0] x_cycle_status;
	assign x_cycle_status = execute_state[371-:32];
	assign x_opcode = execute_state[339-:7];
	assign x_insn_rd = execute_state[332-:5];
	wire [11:0] x_imm_i;
	assign x_imm_i = execute_state[327-:12];
	wire [11:0] x_imm_s;
	assign x_imm_s = execute_state[315-:12];
	wire [12:0] x_imm_b;
	assign x_imm_b = execute_state[303-:13];
	wire [20:0] x_imm_j;
	assign x_imm_j = execute_state[290-:21];
	assign x_imm_i_sext = execute_state[269-:32];
	assign x_imm_s_sext = execute_state[237-:32];
	wire [31:0] x_imm_b_sext;
	assign x_imm_b_sext = execute_state[205-:32];
	wire [31:0] x_imm_j_sext;
	assign x_imm_j_sext = execute_state[173-:32];
	wire [19:0] x_imm_u;
	assign x_imm_u = execute_state[141-:20];
	wire [31:0] x_rs1_data_temp;
	assign x_rs1_data_temp = execute_state[121-:32];
	wire [31:0] x_rs2_data_temp;
	assign x_rs2_data_temp = execute_state[89-:32];
	wire [4:0] x_insn_rs1;
	assign x_insn_rs1 = execute_state[57-:5];
	wire [4:0] x_insn_rs2;
	assign x_insn_rs2 = execute_state[52-:5];
	assign x_insn_key = execute_state[47-:47];
	reg [31:0] x_addr_to_dmem;
	reg [31:0] x_store_mem_to_dmem;
	reg [3:0] x_store_we_to_dmem;
	reg [1:0] x_mem_bytes;
	wire [4:0] m_insn_rd;
	reg [31:0] m_rd_data;
	always @(*) begin
		if (_sv2v_0)
			;
		x_rs1_data = x_rs1_data_temp;
		x_rs2_data = x_rs2_data_temp;
		if (x_insn_rs1 != 0) begin
			if (m_insn_rd == x_insn_rs1)
				x_rs1_data = m_rd_data;
			else if (w_insn_rd == x_insn_rs1)
				x_rs1_data = w_rd_data;
		end
		if (x_insn_rs2 != 0) begin
			if (m_insn_rd == x_insn_rs2)
				x_rs2_data = m_rd_data;
			else if (w_insn_rd == x_insn_rs2)
				x_rs2_data = w_rd_data;
		end
	end
	reg x_halt;
	always @(*) begin
		if (_sv2v_0)
			;
		data_dependent_load = 0;
		if (x_opcode == OpLoad) begin
			if ((d_insn_opcode == OpStore) || (d_insn_opcode == OpRegImm))
				data_dependent_load = x_insn_rd == d_insn_rs1;
			else if (((d_insn_opcode != OpLui) && (d_insn_opcode != OpJal)) && (d_insn_opcode != OpJalr))
				data_dependent_load = (x_insn_rd == d_insn_rs1) || (x_insn_rd == d_insn_rs2);
		end
	end
	always @(*) begin
		if (_sv2v_0)
			;
		x_we = 0;
		x_rd_data = 0;
		x_addr_to_dmem = 0;
		x_store_mem_to_dmem = 0;
		x_store_we_to_dmem = 0;
		x_mem_bytes = 0;
		multiple = 0;
		x_branched_pc = x_pc;
		x_branch_taken = 0;
		x_halt = 0;
		case (x_opcode)
			OpLui: begin
				x_we = 1;
				x_rd_data = x_imm_u << 12;
			end
			OpAuipc: begin
				x_we = 1;
				x_rd_data = x_pc + (x_imm_u << 12);
			end
			OpRegImm: begin
				x_we = 1;
				case (1)
					x_insn_key[28]: x_rd_data = cla_sum;
					x_insn_key[27]: x_rd_data = ($signed(x_rs1_data) < $signed(x_imm_i_sext) ? 1 : 0);
					x_insn_key[26]: x_rd_data = (x_rs1_data < x_imm_i_sext ? 1 : 0);
					x_insn_key[25]: x_rd_data = x_rs1_data ^ x_imm_i_sext;
					x_insn_key[24]: x_rd_data = x_rs1_data | x_imm_i_sext;
					x_insn_key[23]: x_rd_data = x_rs1_data & x_imm_i_sext;
					x_insn_key[22]: x_rd_data = x_rs1_data << x_imm_i[4:0];
					x_insn_key[21]: x_rd_data = x_rs1_data >> x_imm_i[4:0];
					x_insn_key[20]: x_rd_data = $signed(x_rs1_data) >>> x_imm_i[4:0];
				endcase
			end
			OpRegReg: begin
				x_we = 1;
				case (1)
					x_insn_key[19]: x_rd_data = cla_sum;
					x_insn_key[18]: x_rd_data = cla_sum;
					x_insn_key[17]: x_rd_data = x_rs1_data << x_rs2_data[4:0];
					x_insn_key[16]: x_rd_data = ($signed(x_rs1_data) < $signed(x_rs2_data) ? 1 : 0);
					x_insn_key[15]: x_rd_data = (x_rs1_data < x_rs2_data ? 1 : 0);
					x_insn_key[14]: x_rd_data = x_rs1_data ^ x_rs2_data;
					x_insn_key[13]: x_rd_data = x_rs1_data >> x_rs2_data[4:0];
					x_insn_key[12]: x_rd_data = $signed(x_rs1_data) >>> x_rs2_data[4:0];
					x_insn_key[11]: x_rd_data = x_rs1_data | x_rs2_data;
					x_insn_key[10]: x_rd_data = x_rs1_data & x_rs2_data;
					x_insn_key[9]: begin
						multiple = x_rs1_data * x_rs2_data;
						x_rd_data = multiple[31:0];
					end
					x_insn_key[8]: begin
						multiple = $signed(x_rs1_data) * $signed(x_rs2_data);
						x_rd_data = multiple[63:32];
					end
					x_insn_key[7]: begin
						multiple = {{32 {x_rs1_data[31]}}, x_rs1_data} * {{32 {1'b0}}, x_rs2_data};
						x_rd_data = multiple[63:32];
					end
					x_insn_key[6]: begin
						multiple = $unsigned(x_rs1_data) * $unsigned(x_rs2_data);
						x_rd_data = multiple[63:32];
					end
				endcase
			end
			OpBranch: begin
				x_branched_pc = x_pc + x_imm_b_sext;
				case (1)
					x_insn_key[42]: x_branch_taken = x_rs1_data == x_rs2_data;
					x_insn_key[41]: x_branch_taken = x_rs1_data != x_rs2_data;
					x_insn_key[40]: x_branch_taken = $signed(x_rs1_data) < $signed(x_rs2_data);
					x_insn_key[39]: x_branch_taken = $signed(x_rs1_data) >= $signed(x_rs2_data);
					x_insn_key[38]: x_branch_taken = $signed(x_rs1_data) < $unsigned(x_rs2_data);
					x_insn_key[37]: x_branch_taken = $signed(x_rs1_data) >= $unsigned(x_rs2_data);
				endcase
			end
			OpLoad: begin
				x_we = 1;
				x_addr_to_dmem = cla_sum;
			end
			OpStore: begin
				x_addr_to_dmem = cla_sum;
				x_store_mem_to_dmem = x_rs2_data;
			end
			OpJalr: begin
				x_we = 1;
				x_rd_data = x_pc + 4;
				x_branch_taken = 1;
				x_branched_pc = (x_rs1_data + x_imm_i_sext) & ~32'd1;
			end
			OpJal: begin
				x_we = 1;
				x_rd_data = x_pc + 4;
				x_branch_taken = 1;
				x_branched_pc = x_pc + x_imm_j_sext;
			end
			OpEnviron: x_halt = 1;
			OpMiscMem:
				;
			default:
				;
		endcase
	end
	always @(posedge clk)
		if (rst) begin
			memory_state <= 0;
			memory_state[262-:32] <= 32'd1;
		end
		else
			memory_state <= {x_pc, x_insn, x_cycle_status, x_opcode, x_insn_rd, x_rd_data, x_we, x_addr_to_dmem, x_store_mem_to_dmem, x_store_we_to_dmem, x_rs2_data, x_insn_rs2, x_branched_pc, x_branch_taken, x_insn_key, x_halt};
	wire [31:0] m_pc;
	assign m_pc = memory_state[326-:32];
	wire [31:0] m_insn;
	assign m_insn = memory_state[294-:32];
	wire [31:0] m_cycle_status;
	assign m_cycle_status = memory_state[262-:32];
	wire [6:0] m_opcode;
	assign m_opcode = memory_state[230-:7];
	assign m_insn_rd = memory_state[223-:5];
	wire [31:0] m_rd_data_temp;
	assign m_rd_data_temp = memory_state[218-:32];
	wire m_we;
	assign m_we = memory_state[186];
	wire [31:0] m_addr_to_dmem;
	assign m_addr_to_dmem = memory_state[185-:32];
	reg [31:0] m_store_data_to_dmem;
	reg [31:0] m_rs2_data;
	wire [31:0] m_rs2_data_temp;
	assign m_rs2_data_temp = memory_state[117-:32];
	wire [4:0] m_insn_rs2;
	assign m_insn_rs2 = memory_state[85-:5];
	reg [3:0] m_store_we_to_dmem;
	wire [1:0] m_mem_bytes;
	assign m_mem_bytes = m_addr_to_dmem[1:0];
	wire [46:0] m_insn_key;
	assign m_insn_key = memory_state[47-:47];
	wire m_halt;
	assign m_halt = memory_state[0];
	assign addr_to_dmem = m_addr_to_dmem & 32'hfffffffc;
	assign store_data_to_dmem = m_store_data_to_dmem;
	assign store_we_to_dmem = m_store_we_to_dmem;
	wire w_insn_load;
	always @(*) begin
		if (_sv2v_0)
			;
		m_rs2_data = m_rs2_data_temp;
		if (((w_insn_load && (w_insn_rd == m_insn_rs2)) && (m_opcode == OpStore)) && (w_insn_rd != 0))
			m_rs2_data = w_rd_data;
	end
	always @(*) begin
		if (_sv2v_0)
			;
		m_rd_data = m_rd_data_temp;
		m_store_we_to_dmem = 0;
		m_store_data_to_dmem = 0;
		case (m_opcode)
			OpLoad:
				case (1)
					m_insn_key[36]:
						case (m_mem_bytes)
							0: m_rd_data = {{24 {load_data_from_dmem[7]}}, load_data_from_dmem[7:0]};
							1: m_rd_data = {{24 {load_data_from_dmem[15]}}, load_data_from_dmem[15:8]};
							2: m_rd_data = {{24 {load_data_from_dmem[23]}}, load_data_from_dmem[23:16]};
							3: m_rd_data = {{24 {load_data_from_dmem[31]}}, load_data_from_dmem[31:24]};
						endcase
					m_insn_key[35]:
						if (m_mem_bytes[1])
							m_rd_data = {{16 {load_data_from_dmem[31]}}, load_data_from_dmem[31:16]};
						else
							m_rd_data = {{16 {load_data_from_dmem[15]}}, load_data_from_dmem[15:0]};
					m_insn_key[34]: m_rd_data = load_data_from_dmem;
					m_insn_key[33]:
						case (m_mem_bytes)
							0: m_rd_data = {{24 {1'b0}}, load_data_from_dmem[7:0]};
							1: m_rd_data = {{24 {1'b0}}, load_data_from_dmem[15:8]};
							2: m_rd_data = {{24 {1'b0}}, load_data_from_dmem[23:16]};
							3: m_rd_data = {{24 {1'b0}}, load_data_from_dmem[31:24]};
						endcase
					m_insn_key[32]:
						if (m_mem_bytes[1])
							m_rd_data = {{16 {1'b0}}, load_data_from_dmem[31:16]};
						else
							m_rd_data = {{16 {1'b0}}, load_data_from_dmem[15:0]};
				endcase
			OpStore:
				case (1)
					m_insn_key[31]: begin
						m_store_we_to_dmem = 4'b0001 << m_mem_bytes;
						m_store_data_to_dmem = {24'd0, m_rs2_data[7:0]} << ({3'b000, m_mem_bytes} << 3);
					end
					m_insn_key[30]: begin
						m_store_we_to_dmem = 4'b0011 << m_mem_bytes;
						m_store_data_to_dmem = {16'd0, m_rs2_data[15:0]} << ({3'b000, m_mem_bytes} << 3);
					end
					m_insn_key[29]: begin
						m_store_we_to_dmem = 4'b1111;
						m_store_data_to_dmem = m_rs2_data;
					end
				endcase
			default:
				;
		endcase
	end
	always @(posedge clk)
		if (rst) begin
			write_state <= 0;
			write_state[77-:32] <= 32'd1;
		end
		else
			write_state <= {m_pc, m_insn, m_cycle_status, m_opcode, m_insn_rd, m_rd_data, m_we, m_halt};
	wire [31:0] w_pc;
	assign w_pc = write_state[141-:32];
	wire [31:0] w_insn;
	assign w_insn = write_state[109-:32];
	wire [31:0] w_cycle_status;
	assign w_cycle_status = write_state[77-:32];
	wire [6:0] w_opcode;
	assign w_insn_load = w_opcode == OpLoad;
	assign w_opcode = write_state[45-:7];
	assign w_insn_rd = write_state[38-:5];
	assign w_rd_data = write_state[33-:32];
	assign w_we = write_state[1];
	wire w_halt;
	assign w_halt = write_state[0];
	assign halt = w_halt;
	assign trace_writeback_pc = w_pc;
	assign trace_writeback_insn = w_insn;
	assign trace_writeback_cycle_status = w_cycle_status;
	initial _sv2v_0 = 0;
endmodule
module MemorySingleCycle (
	rst,
	clk,
	pc_to_imem,
	insn_from_imem,
	addr_to_dmem,
	load_data_from_dmem,
	store_data_to_dmem,
	store_we_to_dmem
);
	reg _sv2v_0;
	parameter signed [31:0] NUM_WORDS = 512;
	input wire rst;
	input wire clk;
	input wire [31:0] pc_to_imem;
	output reg [31:0] insn_from_imem;
	input wire [31:0] addr_to_dmem;
	output reg [31:0] load_data_from_dmem;
	input wire [31:0] store_data_to_dmem;
	input wire [3:0] store_we_to_dmem;
	reg [31:0] mem_array [0:NUM_WORDS - 1];
	initial $readmemh("mem_initial_contents.hex", mem_array);
	always @(*)
		if (_sv2v_0)
			;
	localparam signed [31:0] AddrMsb = $clog2(NUM_WORDS) + 1;
	localparam signed [31:0] AddrLsb = 2;
	always @(negedge clk)
		if (rst)
			;
		else
			insn_from_imem <= mem_array[{pc_to_imem[AddrMsb:AddrLsb]}];
	always @(negedge clk)
		if (rst)
			;
		else begin
			if (store_we_to_dmem[0])
				mem_array[addr_to_dmem[AddrMsb:AddrLsb]][7:0] <= store_data_to_dmem[7:0];
			if (store_we_to_dmem[1])
				mem_array[addr_to_dmem[AddrMsb:AddrLsb]][15:8] <= store_data_to_dmem[15:8];
			if (store_we_to_dmem[2])
				mem_array[addr_to_dmem[AddrMsb:AddrLsb]][23:16] <= store_data_to_dmem[23:16];
			if (store_we_to_dmem[3])
				mem_array[addr_to_dmem[AddrMsb:AddrLsb]][31:24] <= store_data_to_dmem[31:24];
			load_data_from_dmem <= mem_array[{addr_to_dmem[AddrMsb:AddrLsb]}];
		end
	initial _sv2v_0 = 0;
endmodule
`default_nettype none
`default_nettype none
module SystemResourceCheck (
	external_clk_25MHz,
	btn,
	led
);
	input wire external_clk_25MHz;
	input wire [6:0] btn;
	output wire [7:0] led;
	wire clk_proc;
	wire clk_locked;
	MyClockGen clock_gen(
		.input_clk_25MHz(external_clk_25MHz),
		.clk_proc(clk_proc),
		.locked(clk_locked)
	);
	wire [31:0] pc_to_imem;
	wire [31:0] insn_from_imem;
	wire [31:0] mem_data_addr;
	wire [31:0] mem_data_loaded_value;
	wire [31:0] mem_data_to_write;
	wire [3:0] mem_data_we;
	wire [31:0] trace_writeback_pc;
	wire [31:0] trace_writeback_insn;
	wire [31:0] trace_writeback_cycle_status;
	MemorySingleCycle #(.NUM_WORDS(128)) memory(
		.rst(!clk_locked),
		.clk(clk_proc),
		.pc_to_imem(pc_to_imem),
		.insn_from_imem(insn_from_imem),
		.addr_to_dmem(mem_data_addr),
		.load_data_from_dmem(mem_data_loaded_value),
		.store_data_to_dmem(mem_data_to_write),
		.store_we_to_dmem(mem_data_we)
	);
	DatapathPipelined datapath(
		.clk(clk_proc),
		.rst(!clk_locked),
		.pc_to_imem(pc_to_imem),
		.insn_from_imem(insn_from_imem),
		.addr_to_dmem(mem_data_addr),
		.store_data_to_dmem(mem_data_to_write),
		.store_we_to_dmem(mem_data_we),
		.load_data_from_dmem(mem_data_loaded_value),
		.halt(led[0]),
		.trace_writeback_pc(trace_writeback_pc),
		.trace_writeback_insn(trace_writeback_insn),
		.trace_writeback_cycle_status(trace_writeback_cycle_status)
	);
endmodule