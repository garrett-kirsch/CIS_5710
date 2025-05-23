module MyClockGen (
	input_clk_25MHz,
	clk_proc,
	clk_mem,
	locked
);
	input input_clk_25MHz;
	output wire clk_proc;
	output wire clk_mem;
	output wire locked;
	wire clkfb;
	(* FREQUENCY_PIN_CLKI = "25" *) (* FREQUENCY_PIN_CLKOP = "4.16667" *) (* FREQUENCY_PIN_CLKOS = "4.01003" *) (* ICP_CURRENT = "12" *) (* LPF_RESISTOR = "8" *) (* MFG_ENABLE_FILTEROPAMP = "1" *) (* MFG_GMCREF_SEL = "2" *) EHXPLLL #(
		.PLLRST_ENA("DISABLED"),
		.INTFB_WAKE("DISABLED"),
		.STDBY_ENABLE("DISABLED"),
		.DPHASE_SOURCE("DISABLED"),
		.OUTDIVIDER_MUXA("DIVA"),
		.OUTDIVIDER_MUXB("DIVB"),
		.OUTDIVIDER_MUXC("DIVC"),
		.OUTDIVIDER_MUXD("DIVD"),
		.CLKI_DIV(6),
		.CLKOP_ENABLE("ENABLED"),
		.CLKOP_DIV(128),
		.CLKOP_CPHASE(64),
		.CLKOP_FPHASE(0),
		.CLKOS_ENABLE("ENABLED"),
		.CLKOS_DIV(133),
		.CLKOS_CPHASE(97),
		.CLKOS_FPHASE(2),
		.FEEDBK_PATH("INT_OP"),
		.CLKFB_DIV(1)
	) pll_i(
		.RST(1'b0),
		.STDBY(1'b0),
		.CLKI(input_clk_25MHz),
		.CLKOP(clk_proc),
		.CLKOS(clk_mem),
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
module divider_unsigned (
	i_dividend,
	i_divisor,
	o_remainder,
	o_quotient
);
	input wire [31:0] i_dividend;
	input wire [31:0] i_divisor;
	output wire [31:0] o_remainder;
	output wire [31:0] o_quotient;
	wire [31:0] dividend [0:32];
	wire [31:0] remainder [0:32];
	wire [31:0] quotient [0:32];
	assign dividend[0] = i_dividend;
	assign remainder[0] = 0;
	assign quotient[0] = 0;
	genvar _gv_i_1;
	generate
		for (_gv_i_1 = 0; _gv_i_1 < 32; _gv_i_1 = _gv_i_1 + 1) begin : genblk1
			localparam i = _gv_i_1;
			divu_1iter d(
				.i_dividend(dividend[i]),
				.i_divisor(i_divisor),
				.i_remainder(remainder[i]),
				.i_quotient(quotient[i]),
				.o_dividend(dividend[i + 1]),
				.o_remainder(remainder[i + 1]),
				.o_quotient(quotient[i + 1])
			);
		end
	endgenerate
	assign o_remainder = remainder[32];
	assign o_quotient = quotient[32];
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
	wire [31:0] temp_rem = (i_remainder << 1) | ((i_dividend >> 31) & 1);
	assign o_dividend = i_dividend << 1;
	assign o_quotient = (temp_rem < i_divisor ? i_quotient << 1 : (i_quotient << 1) | 1);
	assign o_remainder = (temp_rem < i_divisor ? temp_rem : temp_rem - i_divisor);
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
	genvar _gv_i_2;
	generate
		for (_gv_i_2 = 0; _gv_i_2 < 32; _gv_i_2 = _gv_i_2 + 1) begin : genblk1
			localparam i = _gv_i_2;
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
module DatapathSingleCycle (
	clk,
	rst,
	halt,
	pc_to_imem,
	insn_from_imem,
	addr_to_dmem,
	load_data_from_dmem,
	store_data_to_dmem,
	store_we_to_dmem
);
	reg _sv2v_0;
	input wire clk;
	input wire rst;
	output reg halt;
	output wire [31:0] pc_to_imem;
	input wire [31:0] insn_from_imem;
	output wire [31:0] addr_to_dmem;
	input wire [31:0] load_data_from_dmem;
	output reg [31:0] store_data_to_dmem;
	output reg [3:0] store_we_to_dmem;
	wire [6:0] insn_funct7;
	wire [4:0] insn_rs2;
	wire [4:0] insn_rs1;
	wire [2:0] insn_funct3;
	wire [4:0] insn_rd;
	wire [6:0] insn_opcode;
	assign {insn_funct7, insn_rs2, insn_rs1, insn_funct3, insn_rd, insn_opcode} = insn_from_imem;
	wire [11:0] imm_i;
	assign imm_i = insn_from_imem[31:20];
	wire [4:0] imm_shamt = insn_from_imem[24:20];
	wire [11:0] imm_s;
	assign imm_s[11:5] = insn_funct7;
	assign imm_s[4:0] = insn_rd;
	wire [12:0] imm_b;
	assign {imm_b[12], imm_b[10:5]} = insn_funct7;
	assign {imm_b[4:1], imm_b[11]} = insn_rd;
	assign imm_b[0] = 1'b0;
	wire [20:0] imm_j;
	assign {imm_j[20], imm_j[10:1], imm_j[11], imm_j[19:12], imm_j[0]} = {insn_from_imem[31:12], 1'b0};
	wire [31:0] imm_i_sext = {{20 {imm_i[11]}}, imm_i[11:0]};
	wire [31:0] imm_s_sext = {{20 {imm_s[11]}}, imm_s[11:0]};
	wire [31:0] imm_b_sext = {{19 {imm_b[12]}}, imm_b[12:0]};
	wire [31:0] imm_j_sext = {{11 {imm_j[20]}}, imm_j[20:0]};
	wire [19:0] imm_u = insn_from_imem[31:12];
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
	wire insn_lui = insn_opcode == OpLui;
	wire insn_auipc = insn_opcode == OpAuipc;
	wire insn_jal = insn_opcode == OpJal;
	wire insn_jalr = insn_opcode == OpJalr;
	wire insn_beq = (insn_opcode == OpBranch) && (insn_from_imem[14:12] == 3'b000);
	wire insn_bne = (insn_opcode == OpBranch) && (insn_from_imem[14:12] == 3'b001);
	wire insn_blt = (insn_opcode == OpBranch) && (insn_from_imem[14:12] == 3'b100);
	wire insn_bge = (insn_opcode == OpBranch) && (insn_from_imem[14:12] == 3'b101);
	wire insn_bltu = (insn_opcode == OpBranch) && (insn_from_imem[14:12] == 3'b110);
	wire insn_bgeu = (insn_opcode == OpBranch) && (insn_from_imem[14:12] == 3'b111);
	wire insn_lb = (insn_opcode == OpLoad) && (insn_from_imem[14:12] == 3'b000);
	wire insn_lh = (insn_opcode == OpLoad) && (insn_from_imem[14:12] == 3'b001);
	wire insn_lw = (insn_opcode == OpLoad) && (insn_from_imem[14:12] == 3'b010);
	wire insn_lbu = (insn_opcode == OpLoad) && (insn_from_imem[14:12] == 3'b100);
	wire insn_lhu = (insn_opcode == OpLoad) && (insn_from_imem[14:12] == 3'b101);
	wire insn_sb = (insn_opcode == OpStore) && (insn_from_imem[14:12] == 3'b000);
	wire insn_sh = (insn_opcode == OpStore) && (insn_from_imem[14:12] == 3'b001);
	wire insn_sw = (insn_opcode == OpStore) && (insn_from_imem[14:12] == 3'b010);
	wire insn_addi = (insn_opcode == OpRegImm) && (insn_from_imem[14:12] == 3'b000);
	wire insn_slti = (insn_opcode == OpRegImm) && (insn_from_imem[14:12] == 3'b010);
	wire insn_sltiu = (insn_opcode == OpRegImm) && (insn_from_imem[14:12] == 3'b011);
	wire insn_xori = (insn_opcode == OpRegImm) && (insn_from_imem[14:12] == 3'b100);
	wire insn_ori = (insn_opcode == OpRegImm) && (insn_from_imem[14:12] == 3'b110);
	wire insn_andi = (insn_opcode == OpRegImm) && (insn_from_imem[14:12] == 3'b111);
	wire insn_slli = ((insn_opcode == OpRegImm) && (insn_from_imem[14:12] == 3'b001)) && (insn_from_imem[31:25] == 7'd0);
	wire insn_srli = ((insn_opcode == OpRegImm) && (insn_from_imem[14:12] == 3'b101)) && (insn_from_imem[31:25] == 7'd0);
	wire insn_srai = ((insn_opcode == OpRegImm) && (insn_from_imem[14:12] == 3'b101)) && (insn_from_imem[31:25] == 7'b0100000);
	wire insn_add = ((insn_opcode == OpRegReg) && (insn_from_imem[14:12] == 3'b000)) && (insn_from_imem[31:25] == 7'd0);
	wire insn_sub = ((insn_opcode == OpRegReg) && (insn_from_imem[14:12] == 3'b000)) && (insn_from_imem[31:25] == 7'b0100000);
	wire insn_sll = ((insn_opcode == OpRegReg) && (insn_from_imem[14:12] == 3'b001)) && (insn_from_imem[31:25] == 7'd0);
	wire insn_slt = ((insn_opcode == OpRegReg) && (insn_from_imem[14:12] == 3'b010)) && (insn_from_imem[31:25] == 7'd0);
	wire insn_sltu = ((insn_opcode == OpRegReg) && (insn_from_imem[14:12] == 3'b011)) && (insn_from_imem[31:25] == 7'd0);
	wire insn_xor = ((insn_opcode == OpRegReg) && (insn_from_imem[14:12] == 3'b100)) && (insn_from_imem[31:25] == 7'd0);
	wire insn_srl = ((insn_opcode == OpRegReg) && (insn_from_imem[14:12] == 3'b101)) && (insn_from_imem[31:25] == 7'd0);
	wire insn_sra = ((insn_opcode == OpRegReg) && (insn_from_imem[14:12] == 3'b101)) && (insn_from_imem[31:25] == 7'b0100000);
	wire insn_or = ((insn_opcode == OpRegReg) && (insn_from_imem[14:12] == 3'b110)) && (insn_from_imem[31:25] == 7'd0);
	wire insn_and = ((insn_opcode == OpRegReg) && (insn_from_imem[14:12] == 3'b111)) && (insn_from_imem[31:25] == 7'd0);
	wire insn_mul = ((insn_opcode == OpRegReg) && (insn_from_imem[31:25] == 7'd1)) && (insn_from_imem[14:12] == 3'b000);
	wire insn_mulh = ((insn_opcode == OpRegReg) && (insn_from_imem[31:25] == 7'd1)) && (insn_from_imem[14:12] == 3'b001);
	wire insn_mulhsu = ((insn_opcode == OpRegReg) && (insn_from_imem[31:25] == 7'd1)) && (insn_from_imem[14:12] == 3'b010);
	wire insn_mulhu = ((insn_opcode == OpRegReg) && (insn_from_imem[31:25] == 7'd1)) && (insn_from_imem[14:12] == 3'b011);
	wire insn_div = ((insn_opcode == OpRegReg) && (insn_from_imem[31:25] == 7'd1)) && (insn_from_imem[14:12] == 3'b100);
	wire insn_divu = ((insn_opcode == OpRegReg) && (insn_from_imem[31:25] == 7'd1)) && (insn_from_imem[14:12] == 3'b101);
	wire insn_rem = ((insn_opcode == OpRegReg) && (insn_from_imem[31:25] == 7'd1)) && (insn_from_imem[14:12] == 3'b110);
	wire insn_remu = ((insn_opcode == OpRegReg) && (insn_from_imem[31:25] == 7'd1)) && (insn_from_imem[14:12] == 3'b111);
	wire insn_ecall = (insn_opcode == OpEnviron) && (insn_from_imem[31:7] == 25'd0);
	wire insn_fence = insn_opcode == OpMiscMem;
	reg [31:0] pcNext;
	reg [31:0] pcCurrent;
	always @(posedge clk)
		if (rst)
			pcCurrent <= 32'd0;
		else
			pcCurrent <= pcNext;
	assign pc_to_imem = pcCurrent;
	reg [31:0] cycles_current;
	reg [31:0] num_insns_current;
	always @(posedge clk)
		if (rst) begin
			cycles_current <= 0;
			num_insns_current <= 0;
		end
		else begin
			cycles_current <= cycles_current + 1;
			if (!rst)
				num_insns_current <= num_insns_current + 1;
		end
	wire [31:0] rs1_data;
	wire [31:0] rs2_data;
	reg [31:0] rd_data;
	reg we;
	RegFile rf(
		.clk(clk),
		.rst(rst),
		.we(we),
		.rd(insn_rd),
		.rd_data(rd_data),
		.rs1(insn_rs1),
		.rs2(insn_rs2),
		.rs1_data(rs1_data),
		.rs2_data(rs2_data)
	);
	reg illegal_insn;
	wire [31:0] regregsum;
	cla regregadder(
		.a(rs1_data),
		.b(rs2_data),
		.cin(0),
		.sum(regregsum)
	);
	wire [31:0] regregdiff;
	cla regregsubtracter(
		.a(rs1_data),
		.b(~rs2_data),
		.cin(1),
		.sum(regregdiff)
	);
	wire [31:0] regimmsum;
	cla regimmadder(
		.a(rs1_data),
		.b(imm_i_sext),
		.cin(0),
		.sum(regimmsum)
	);
	reg [63:0] multiple;
	wire [31:0] product_temp;
	wire [31:0] squotient;
	wire [31:0] sremainder;
	wire [31:0] true_squotient;
	wire [31:0] true_sremainder;
	wire [31:0] sdivisor;
	wire [31:0] sdividend;
	assign sdividend = (rs1_data[31] ? ~rs1_data + 1 : rs1_data);
	assign sdivisor = (rs2_data[31] ? ~rs2_data + 1 : rs2_data);
	assign true_squotient = (rs1_data[31] ^ rs2_data[31] ? ~squotient + 1 : squotient);
	assign true_sremainder = (rs1_data[31] ? ~sremainder + 1 : sremainder);
	divider_unsigned sdivider(
		.i_dividend(sdividend),
		.i_divisor(sdivisor),
		.o_quotient(squotient),
		.o_remainder(sremainder)
	);
	wire [31:0] uquotient;
	wire [31:0] uremainder;
	divider_unsigned udivider(
		.i_dividend(rs1_data),
		.i_divisor(rs2_data),
		.o_quotient(uquotient),
		.o_remainder(uremainder)
	);
	reg [31:0] mem;
	assign addr_to_dmem = mem;
	wire [31:0] raw_mem = rs1_data + imm_s_sext;
	reg [31:0] inverted_rs1data = ~rs1_data + 32'b00000000000000000000000000000001;
	always @(*) begin
		if (_sv2v_0)
			;
		illegal_insn = 1'b0;
		we = 0;
		rd_data = 0;
		halt = 0;
		multiple = 0;
		mem = 0;
		store_data_to_dmem = 0;
		store_we_to_dmem = 0;
		pcNext = pcCurrent + 4;
		case (insn_opcode)
			OpLui: begin
				we = 1;
				rd_data = imm_u << 12;
			end
			OpAuipc: begin
				we = 1;
				rd_data = pcCurrent + (imm_u << 12);
			end
			OpRegImm: begin
				we = 1;
				case (1)
					insn_addi: rd_data = regimmsum;
					insn_slti: rd_data = ($signed(rs1_data) < $signed(imm_i_sext) ? 1 : 0);
					insn_sltiu: rd_data = (rs1_data < imm_i_sext ? 1 : 0);
					insn_xori: rd_data = rs1_data ^ imm_i_sext;
					insn_ori: rd_data = rs1_data | imm_i_sext;
					insn_andi: rd_data = rs1_data & imm_i_sext;
					insn_slli: rd_data = rs1_data << imm_i[4:0];
					insn_srli: rd_data = rs1_data >> imm_i[4:0];
					insn_srai: rd_data = $signed(rs1_data) >>> imm_i[4:0];
				endcase
			end
			OpRegReg: begin
				we = 1;
				case (1)
					insn_add: rd_data = regregsum;
					insn_sub: rd_data = regregdiff;
					insn_sll: rd_data = rs1_data << rs2_data[4:0];
					insn_slt: rd_data = ($signed(rs1_data) < $signed(rs2_data) ? 1 : 0);
					insn_sltu: rd_data = (rs1_data < rs2_data ? 1 : 0);
					insn_xor: rd_data = rs1_data ^ rs2_data;
					insn_srl: rd_data = rs1_data >> rs2_data[4:0];
					insn_sra: rd_data = $signed(rs1_data) >>> rs2_data[4:0];
					insn_or: rd_data = rs1_data | rs2_data;
					insn_and: rd_data = rs1_data & rs2_data;
					insn_mul: begin
						multiple = rs1_data * rs2_data;
						rd_data = multiple[31:0];
					end
					insn_mulh: begin
						multiple = $signed(rs1_data) * $signed(rs2_data);
						rd_data = multiple[63:32];
					end
					insn_mulhsu: begin
						multiple = {{32 {rs1_data[31]}}, rs1_data} * {{32 {1'b0}}, rs2_data};
						rd_data = multiple[63:32];
					end
					insn_mulhu: begin
						multiple = $unsigned(rs1_data) * $unsigned(rs2_data);
						rd_data = multiple[63:32];
					end
					insn_div:
						if (sdivisor == 0)
							rd_data = 32'hffffffff;
						else
							rd_data = true_squotient;
					insn_divu: rd_data = uquotient;
					insn_rem: rd_data = true_sremainder;
					insn_remu: rd_data = uremainder;
				endcase
			end
			OpBranch:
				case (1)
					insn_beq:
						if (rs1_data == rs2_data)
							pcNext = pcCurrent + imm_b_sext;
					insn_bne:
						if (rs1_data != rs2_data)
							pcNext = pcCurrent + imm_b_sext;
					insn_blt:
						if ($signed(rs1_data) < $signed(rs2_data))
							pcNext = pcCurrent + imm_b_sext;
					insn_bge:
						if ($signed(rs1_data) >= $signed(rs2_data))
							pcNext = pcCurrent + imm_b_sext;
					insn_bltu:
						if (rs1_data < rs2_data)
							pcNext = pcCurrent + imm_b_sext;
					insn_bgeu:
						if (rs1_data >= rs2_data)
							pcNext = pcCurrent + imm_b_sext;
				endcase
			OpLoad: begin
				we = 1;
				mem = regimmsum & 32'hfffffffc;
				case (1)
					insn_lb:
						case (regimmsum[1:0])
							0: rd_data = {{24 {load_data_from_dmem[7]}}, load_data_from_dmem[7:0]};
							1: rd_data = {{24 {load_data_from_dmem[15]}}, load_data_from_dmem[15:8]};
							2: rd_data = {{24 {load_data_from_dmem[23]}}, load_data_from_dmem[23:16]};
							3: rd_data = {{24 {load_data_from_dmem[31]}}, load_data_from_dmem[31:24]};
						endcase
					insn_lh:
						if (regimmsum[1])
							rd_data = {{16 {load_data_from_dmem[31]}}, load_data_from_dmem[31:16]};
						else
							rd_data = {{16 {load_data_from_dmem[15]}}, load_data_from_dmem[15:0]};
					insn_lw: rd_data = load_data_from_dmem;
					insn_lbu:
						case (regimmsum[1:0])
							0: rd_data = {{24 {1'b0}}, load_data_from_dmem[7:0]};
							1: rd_data = {{24 {1'b0}}, load_data_from_dmem[15:8]};
							2: rd_data = {{24 {1'b0}}, load_data_from_dmem[23:16]};
							3: rd_data = {{24 {1'b0}}, load_data_from_dmem[31:24]};
						endcase
					insn_lhu:
						if (regimmsum[1])
							rd_data = {{16 {1'b0}}, load_data_from_dmem[31:16]};
						else
							rd_data = {{16 {1'b0}}, load_data_from_dmem[15:0]};
				endcase
			end
			OpStore: begin
				mem = raw_mem & 32'hfffffffc;
				case (1)
					insn_sb: begin
						store_we_to_dmem = 4'b0001 << raw_mem[1:0];
						store_data_to_dmem = {24'd0, rs2_data[7:0]} << ({3'b000, raw_mem[1:0]} << 3);
					end
					insn_sh: begin
						store_we_to_dmem = 4'b0011 << raw_mem[1:0];
						store_data_to_dmem = {16'd0, rs2_data[15:0]} << ({3'b000, raw_mem[1:0]} << 3);
					end
					insn_sw: begin
						store_we_to_dmem = 4'b1111;
						store_data_to_dmem = rs2_data;
					end
				endcase
			end
			OpJalr: begin
				we = 1;
				rd_data = pcCurrent + 4;
				pcNext = (rs1_data + imm_i_sext) & ~32'd1;
			end
			OpJal: begin
				we = 1;
				rd_data = pcCurrent + 4;
				pcNext = pcCurrent + imm_j_sext;
			end
			OpEnviron: halt = 1;
			OpMiscMem:
				;
			default: illegal_insn = 1'b1;
		endcase
	end
	initial _sv2v_0 = 0;
endmodule
module MemorySingleCycle (
	rst,
	clock_mem,
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
	input wire clock_mem;
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
	always @(posedge clock_mem)
		if (rst)
			;
		else
			insn_from_imem <= mem_array[{pc_to_imem[AddrMsb:AddrLsb]}];
	always @(negedge clock_mem)
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
module debouncer (
	i_clk,
	i_in,
	o_debounced,
	o_debug
);
	parameter NIN = 21;
	parameter LGWAIT = 17;
	input wire i_clk;
	input wire [NIN - 1:0] i_in;
	output reg [NIN - 1:0] o_debounced;
	output wire [30:0] o_debug;
	reg different;
	reg ztimer;
	reg [NIN - 1:0] r_in;
	reg [NIN - 1:0] q_in;
	reg [NIN - 1:0] r_last;
	reg [LGWAIT - 1:0] timer;
	initial q_in = 0;
	initial r_in = 0;
	initial different = 0;
	always @(posedge i_clk) q_in <= i_in;
	always @(posedge i_clk) r_in <= q_in;
	always @(posedge i_clk) r_last <= r_in;
	initial ztimer = 1'b1;
	initial timer = 0;
	always @(posedge i_clk)
		if (ztimer && different) begin
			timer <= {LGWAIT {1'b1}};
			ztimer <= 1'b0;
		end
		else if (!ztimer) begin
			timer <= timer - 1'b1;
			ztimer <= timer[LGWAIT - 1:1] == 0;
		end
		else begin
			ztimer <= 1'b1;
			timer <= 0;
		end
	always @(posedge i_clk) different <= (different && !ztimer) || (r_in != o_debounced);
	initial o_debounced = {NIN {1'b0}};
	always @(posedge i_clk)
		if (ztimer)
			o_debounced <= r_last;
	reg trigger;
	initial trigger = 1'b0;
	always @(posedge i_clk) trigger <= (((!ztimer && !different) && !(|i_in)) && (timer[LGWAIT - 1:2] == 0)) && timer[1];
	wire [30:0] debug;
	assign debug[30] = ztimer;
	assign debug[29] = trigger;
	assign debug[28] = 1'b0;
	generate
		if (NIN >= 14) begin : genblk1
			assign debug[27:14] = o_debounced[13:0];
			assign debug[13:0] = r_in[13:0];
		end
		else begin : genblk1
			assign debug[27:14 + NIN] = 0;
			assign debug[(14 + NIN) - 1:14] = o_debounced;
			assign debug[13:NIN] = 0;
			assign debug[NIN - 1:0] = r_in;
		end
	endgenerate
	assign o_debug = debug;
endmodule
module SystemDemo (
	external_clk_25MHz,
	btn,
	led
);
	input wire external_clk_25MHz;
	input wire [6:0] btn;
	output wire [7:0] led;
	localparam signed [31:0] MmapButtons = 32'hff001000;
	localparam signed [31:0] MmapLeds = 32'hff002000;
	wire rst_button_n;
	wire [30:0] ignore;
	wire clk_proc;
	debouncer #(.NIN(1)) db(
		.i_clk(clk_proc),
		.i_in(btn[0]),
		.o_debounced(rst_button_n),
		.o_debug(ignore)
	);
	wire clk_mem;
	wire clk_locked;
	MyClockGen clock_gen(
		.input_clk_25MHz(external_clk_25MHz),
		.clk_proc(clk_proc),
		.clk_mem(clk_mem),
		.locked(clk_locked)
	);
	wire rst = !rst_button_n || !clk_locked;
	wire [31:0] pc_to_imem;
	wire [31:0] insn_from_imem;
	wire [31:0] mem_data_addr;
	wire [31:0] mem_data_loaded_value;
	wire [31:0] mem_data_to_write;
	wire [3:0] mem_data_we;
	reg [7:0] led_state;
	assign led = led_state;
	always @(posedge clk_mem)
		if (rst)
			led_state <= 0;
		else if ((mem_data_addr == MmapLeds) && (mem_data_we[0] == 1))
			led_state <= mem_data_to_write[7:0];
	MemorySingleCycle #(.NUM_WORDS(1024)) memory(
		.rst(rst),
		.clock_mem(clk_mem),
		.pc_to_imem(pc_to_imem),
		.insn_from_imem(insn_from_imem),
		.addr_to_dmem(mem_data_addr),
		.load_data_from_dmem(mem_data_loaded_value),
		.store_data_to_dmem(mem_data_to_write),
		.store_we_to_dmem((mem_data_addr == MmapLeds ? 4'd0 : mem_data_we))
	);
	wire halt;
	DatapathSingleCycle datapath(
		.clk(clk_proc),
		.rst(rst),
		.pc_to_imem(pc_to_imem),
		.insn_from_imem(insn_from_imem),
		.addr_to_dmem(mem_data_addr),
		.store_data_to_dmem(mem_data_to_write),
		.store_we_to_dmem(mem_data_we),
		.load_data_from_dmem((mem_data_addr == MmapButtons ? {25'd0, btn} : mem_data_loaded_value)),
		.halt(halt)
	);
endmodule