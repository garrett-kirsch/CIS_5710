`default_nettype none
module MyClockGen (
	input_clk_25MHz,
	clk_proc,
	locked
);
	input input_clk_25MHz;
	output wire clk_proc;
	output wire locked;
	wire clkfb;
	(* FREQUENCY_PIN_CLKI = "25" *) (* FREQUENCY_PIN_CLKOP = "12.5" *) (* ICP_CURRENT = "12" *) (* LPF_RESISTOR = "8" *) (* MFG_ENABLE_FILTEROPAMP = "1" *) (* MFG_GMCREF_SEL = "2" *) EHXPLLL #(
		.PLLRST_ENA("DISABLED"),
		.INTFB_WAKE("DISABLED"),
		.STDBY_ENABLE("DISABLED"),
		.DPHASE_SOURCE("DISABLED"),
		.OUTDIVIDER_MUXA("DIVA"),
		.OUTDIVIDER_MUXB("DIVB"),
		.OUTDIVIDER_MUXC("DIVC"),
		.OUTDIVIDER_MUXD("DIVD"),
		.CLKI_DIV(2),
		.CLKOP_ENABLE("ENABLED"),
		.CLKOP_DIV(48),
		.CLKOP_CPHASE(23),
		.CLKOP_FPHASE(0),
		.FEEDBK_PATH("INT_OP"),
		.CLKFB_DIV(1)
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
module encoder (
	one_hot,
	binary
);
	reg _sv2v_0;
	parameter signed [31:0] INPUT_WIDTH = 0;
	input wire [INPUT_WIDTH - 1:0] one_hot;
	output reg [(1 == INPUT_WIDTH ? 0 : $clog2(INPUT_WIDTH) - 1):0] binary;
	always @(*) begin
		if (_sv2v_0)
			;
		binary = 1'sb0;
		begin : sv2v_autoblock_1
			reg signed [31:0] i;
			for (i = 0; i < INPUT_WIDTH; i = i + 1)
				if (one_hot[i])
					binary = i[(1 == INPUT_WIDTH ? 0 : $clog2(INPUT_WIDTH) - 1):0];
		end
	end
	initial _sv2v_0 = 0;
endmodule
module Disasm (
	insn,
	disasm
);
	parameter PREFIX = "D";
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
`default_nettype none
module SystemResourceCheck (
	external_clk_25MHz,
	btn,
	led
);
	input wire external_clk_25MHz;
	input wire [6:0] btn;
	output wire [7:0] led;
	wire clk;
	wire clk_locked;
	MyClockGen clock_gen(
		.input_clk_25MHz(external_clk_25MHz),
		.clk_proc(clk),
		.locked(clk_locked)
	);
	wire rst = !clk_locked;
	generate
		if (1) begin : axi_data_cache
			localparam signed [31:0] ADDR_WIDTH = 32;
			localparam signed [31:0] DATA_WIDTH = 32;
			reg ARREADY;
			reg ARVALID;
			reg [31:0] ARADDR;
			wire [2:0] ARPROT;
			wire RREADY;
			reg RVALID;
			reg [31:0] RDATA;
			wire [1:0] RRESP;
			reg AWREADY;
			reg AWVALID;
			reg [31:0] AWADDR;
			wire [2:0] AWPROT;
			reg WREADY;
			reg WVALID;
			reg [31:0] WDATA;
			reg [3:0] WSTRB;
			wire BREADY;
			reg BVALID;
			wire [1:0] BRESP;
		end
		if (1) begin : axi_mem_ro
			localparam signed [31:0] ADDR_WIDTH = 32;
			localparam signed [31:0] DATA_WIDTH = 32;
			reg ARREADY;
			reg ARVALID;
			reg [31:0] ARADDR;
			wire [2:0] ARPROT;
			reg RREADY;
			reg RVALID;
			reg [31:0] RDATA;
			wire [1:0] RRESP;
			reg AWREADY;
			wire AWVALID;
			wire [31:0] AWADDR;
			wire [2:0] AWPROT;
			reg WREADY;
			wire WVALID;
			wire [31:0] WDATA;
			wire [3:0] WSTRB;
			wire BREADY;
			wire BVALID;
			wire [1:0] BRESP;
		end
		if (1) begin : axi_mem_rw
			localparam signed [31:0] ADDR_WIDTH = 32;
			localparam signed [31:0] DATA_WIDTH = 32;
			reg ARREADY;
			reg ARVALID;
			reg [31:0] ARADDR;
			wire [2:0] ARPROT;
			reg RREADY;
			reg RVALID;
			reg [31:0] RDATA;
			wire [1:0] RRESP;
			reg AWREADY;
			reg AWVALID;
			reg [31:0] AWADDR;
			wire [2:0] AWPROT;
			reg WREADY;
			reg WVALID;
			reg [31:0] WDATA;
			reg [3:0] WSTRB;
			reg BREADY;
			reg BVALID;
			wire [1:0] BRESP;
		end
	endgenerate
	localparam _param_957C3_NUM_WORDS = 128;
	generate
		if (1) begin : memory
			localparam signed [31:0] NUM_WORDS = _param_957C3_NUM_WORDS;
			wire ACLK;
			wire ARESETn;
			localparam [0:0] True = 1'b1;
			localparam [0:0] False = 1'b0;
			localparam signed [31:0] AddrLsb = 2;
			localparam signed [31:0] AddrMsb = 8;
			reg [31:0] mem_array [0:127];
			reg [31:0] ro_araddr;
			reg ro_araddr_valid;
			initial $readmemh("mem_initial_contents.hex", mem_array);
			assign SystemResourceCheck.axi_mem_ro.RRESP = 2'b00;
			assign SystemResourceCheck.axi_mem_ro.BRESP = 2'b00;
			assign SystemResourceCheck.axi_mem_rw.RRESP = 2'b00;
			assign SystemResourceCheck.axi_mem_rw.BRESP = 2'b00;
			always @(posedge ACLK)
				if (!ARESETn) begin
					ro_araddr <= 0;
					ro_araddr_valid <= False;
					SystemResourceCheck.axi_mem_ro.ARREADY <= True;
					SystemResourceCheck.axi_mem_ro.AWREADY <= False;
					SystemResourceCheck.axi_mem_ro.WREADY <= False;
					SystemResourceCheck.axi_mem_ro.RVALID <= False;
					SystemResourceCheck.axi_mem_ro.RDATA <= 0;
					SystemResourceCheck.axi_mem_rw.ARREADY <= True;
					SystemResourceCheck.axi_mem_rw.AWREADY <= True;
					SystemResourceCheck.axi_mem_rw.WREADY <= True;
					SystemResourceCheck.axi_mem_rw.RVALID <= False;
					SystemResourceCheck.axi_mem_rw.RDATA <= 0;
				end
				else begin
					if (ro_araddr_valid) begin
						if (SystemResourceCheck.axi_mem_ro.RREADY) begin
							SystemResourceCheck.axi_mem_ro.RVALID <= True;
							SystemResourceCheck.axi_mem_ro.RDATA <= mem_array[ro_araddr[AddrMsb:AddrLsb]];
							ro_araddr <= 0;
							ro_araddr_valid <= False;
							SystemResourceCheck.axi_mem_ro.ARREADY <= True;
						end
					end
					else if (SystemResourceCheck.axi_mem_ro.ARVALID && SystemResourceCheck.axi_mem_ro.ARREADY) begin
						if (SystemResourceCheck.axi_mem_ro.RVALID && !SystemResourceCheck.axi_mem_ro.RREADY) begin
							ro_araddr <= SystemResourceCheck.axi_mem_ro.ARADDR;
							ro_araddr_valid <= True;
							SystemResourceCheck.axi_mem_ro.ARREADY <= False;
						end
						else begin
							SystemResourceCheck.axi_mem_ro.RVALID <= True;
							SystemResourceCheck.axi_mem_ro.RDATA <= mem_array[SystemResourceCheck.axi_mem_ro.ARADDR[AddrMsb:AddrLsb]];
						end
					end
					else if (SystemResourceCheck.axi_mem_ro.RVALID && SystemResourceCheck.axi_mem_ro.RREADY) begin
						SystemResourceCheck.axi_mem_ro.RVALID <= False;
						SystemResourceCheck.axi_mem_ro.RDATA <= 0;
						SystemResourceCheck.axi_mem_ro.ARREADY <= True;
					end
					if (SystemResourceCheck.axi_mem_rw.ARVALID && SystemResourceCheck.axi_mem_rw.ARREADY) begin
						SystemResourceCheck.axi_mem_rw.RVALID <= True;
						SystemResourceCheck.axi_mem_rw.RDATA <= mem_array[SystemResourceCheck.axi_mem_rw.ARADDR[AddrMsb:AddrLsb]];
					end
					else if (SystemResourceCheck.axi_mem_rw.RVALID) begin
						SystemResourceCheck.axi_mem_rw.RVALID <= False;
						SystemResourceCheck.axi_mem_rw.RDATA <= 0;
					end
					if (((SystemResourceCheck.axi_mem_rw.AWVALID && SystemResourceCheck.axi_mem_rw.AWREADY) && SystemResourceCheck.axi_mem_rw.WVALID) && SystemResourceCheck.axi_mem_rw.WREADY) begin
						if (SystemResourceCheck.axi_mem_rw.WSTRB[0])
							mem_array[SystemResourceCheck.axi_mem_rw.AWADDR[AddrMsb:AddrLsb]][7:0] <= SystemResourceCheck.axi_mem_rw.WDATA[7:0];
						if (SystemResourceCheck.axi_mem_rw.WSTRB[1])
							mem_array[SystemResourceCheck.axi_mem_rw.AWADDR[AddrMsb:AddrLsb]][15:8] <= SystemResourceCheck.axi_mem_rw.WDATA[15:8];
						if (SystemResourceCheck.axi_mem_rw.WSTRB[2])
							mem_array[SystemResourceCheck.axi_mem_rw.AWADDR[AddrMsb:AddrLsb]][23:16] <= SystemResourceCheck.axi_mem_rw.WDATA[23:16];
						if (SystemResourceCheck.axi_mem_rw.WSTRB[3])
							mem_array[SystemResourceCheck.axi_mem_rw.AWADDR[AddrMsb:AddrLsb]][31:24] <= SystemResourceCheck.axi_mem_rw.WDATA[31:24];
						SystemResourceCheck.axi_mem_rw.BVALID <= True;
					end
					else if (SystemResourceCheck.axi_mem_rw.BVALID)
						SystemResourceCheck.axi_mem_rw.BVALID <= False;
				end
		end
	endgenerate
	assign memory.ACLK = clk;
	assign memory.ARESETn = ~rst;
	localparam _param_7E3C6_BLOCK_SIZE_BITS = 32;
	localparam _param_7E3C6_NUM_SETS = 8;
	generate
		if (1) begin : dcache
			reg _sv2v_0;
			localparam signed [31:0] BLOCK_SIZE_BITS = _param_7E3C6_BLOCK_SIZE_BITS;
			localparam signed [31:0] WAYS = 1;
			localparam signed [31:0] NUM_SETS = _param_7E3C6_NUM_SETS;
			wire ACLK;
			wire ARESETn;
			localparam signed [31:0] BlockOffsetBits = 2;
			localparam signed [31:0] IndexBits = 3;
			localparam signed [31:0] TagBits = 32'sd32 - (IndexBits + BlockOffsetBits);
			localparam signed [31:0] AddrMsb = (IndexBits + BlockOffsetBits) - 1;
			reg [31:0] current_state;
			reg [31:0] data [0:7];
			reg [TagBits - 1:0] tag [0:7];
			reg [0:0] valid [0:7];
			reg [0:0] dirty [0:7];
			reg [0:0] lru [0:7];
			genvar _gv_seti_1;
			genvar _gv_wayi_1;
			for (_gv_seti_1 = 0; _gv_seti_1 < NUM_SETS; _gv_seti_1 = _gv_seti_1 + 1) begin : gen_cache_init
				localparam seti = _gv_seti_1;
				initial begin
					valid[seti] = 1'sb0;
					dirty[seti] = 1'sb0;
					lru[seti] = 1'sb0;
					data[seti] = 0;
					tag[seti] = 0;
				end
			end
			always @(*)
				if (_sv2v_0)
					;
			assign SystemResourceCheck.axi_data_cache.RRESP = 2'b00;
			assign SystemResourceCheck.axi_data_cache.BRESP = 2'b00;
			localparam [0:0] True = 1'b1;
			localparam [0:0] False = 1'b0;
			wire [31:0] req_addr = (SystemResourceCheck.axi_data_cache.ARVALID ? SystemResourceCheck.axi_data_cache.ARADDR : (SystemResourceCheck.axi_data_cache.AWVALID ? SystemResourceCheck.axi_data_cache.AWADDR : 0));
			wire [2:0] cache_index = req_addr[AddrMsb-:IndexBits];
			wire [TagBits - 1:0] req_tag = req_addr[31-:TagBits];
			wire is_read_request = SystemResourceCheck.axi_data_cache.ARVALID && SystemResourceCheck.axi_data_cache.ARREADY;
			wire is_write_request = ((SystemResourceCheck.axi_data_cache.AWVALID && SystemResourceCheck.axi_data_cache.WVALID) && SystemResourceCheck.axi_data_cache.AWREADY) && SystemResourceCheck.axi_data_cache.WREADY;
			wire is_request = is_read_request || is_write_request;
			wire can_send_new_response = !SystemResourceCheck.axi_data_cache.RVALID || (SystemResourceCheck.axi_data_cache.RVALID && SystemResourceCheck.axi_data_cache.RREADY);
			wire [0:0] way_hit_1hot;
			for (_gv_wayi_1 = 0; _gv_wayi_1 < WAYS; _gv_wayi_1 = _gv_wayi_1 + 1) begin : gen_way_hit
				localparam wayi = _gv_wayi_1;
				assign way_hit_1hot[wayi] = valid[cache_index][wayi] && (tag[cache_index] == req_tag);
			end
			wire [0:0] way_hit_index;
			encoder #(.INPUT_WIDTH(WAYS)) way_encoder(
				.one_hot(way_hit_1hot),
				.binary(way_hit_index)
			);
			wire cache_hit = |way_hit_1hot;
			wire is_read = SystemResourceCheck.axi_data_cache.ARVALID;
			wire victim_way_index = 0;
			wire victim_is_dirty = dirty[cache_index][victim_way_index];
			wire [31:0] victim_addr = {tag[cache_index], cache_index, {BlockOffsetBits {1'b0}}};
			reg read_miss;
			reg [(72 + TagBits) + 1:0] saved;
			always @(posedge ACLK)
				if (!ARESETn) begin
					current_state <= 32'd0;
					read_miss <= False;
					saved <= 1'sb0;
					SystemResourceCheck.axi_data_cache.ARREADY <= True;
					SystemResourceCheck.axi_data_cache.RVALID <= False;
					SystemResourceCheck.axi_data_cache.RDATA <= 0;
					SystemResourceCheck.axi_data_cache.AWREADY <= True;
					SystemResourceCheck.axi_data_cache.WREADY <= True;
					SystemResourceCheck.axi_data_cache.BVALID <= 0;
					SystemResourceCheck.axi_mem_rw.ARVALID <= False;
					SystemResourceCheck.axi_mem_rw.ARADDR <= 0;
					SystemResourceCheck.axi_mem_rw.RREADY <= False;
					SystemResourceCheck.axi_mem_rw.AWVALID <= False;
					SystemResourceCheck.axi_mem_rw.AWADDR <= 0;
					SystemResourceCheck.axi_mem_rw.WVALID <= False;
					SystemResourceCheck.axi_mem_rw.WDATA <= 0;
					SystemResourceCheck.axi_mem_rw.WSTRB <= 0;
					SystemResourceCheck.axi_mem_rw.BREADY <= False;
				end
				else
					case (current_state)
						32'd0: begin
							SystemResourceCheck.axi_data_cache.ARREADY <= True;
							SystemResourceCheck.axi_data_cache.AWREADY <= True;
							SystemResourceCheck.axi_data_cache.WREADY <= True;
							if (is_request && cache_hit) begin
								if (can_send_new_response) begin
									lru[cache_index][0] <= ~way_hit_index;
									if (is_read) begin
										SystemResourceCheck.axi_data_cache.RVALID <= True;
										SystemResourceCheck.axi_data_cache.RDATA <= data[cache_index];
									end
									else begin
										SystemResourceCheck.axi_data_cache.BVALID <= True;
										if (SystemResourceCheck.axi_data_cache.WSTRB[0]) begin
											data[cache_index][7:0] <= SystemResourceCheck.axi_data_cache.WDATA[7:0];
											dirty[cache_index][way_hit_index] <= 1;
										end
										if (SystemResourceCheck.axi_data_cache.WSTRB[1]) begin
											data[cache_index][15:8] <= SystemResourceCheck.axi_data_cache.WDATA[15:8];
											dirty[cache_index][way_hit_index] <= 1;
										end
										if (SystemResourceCheck.axi_data_cache.WSTRB[2]) begin
											data[cache_index][23:16] <= SystemResourceCheck.axi_data_cache.WDATA[23:16];
											dirty[cache_index][way_hit_index] <= 1;
										end
										if (SystemResourceCheck.axi_data_cache.WSTRB[3]) begin
											data[cache_index][31:24] <= SystemResourceCheck.axi_data_cache.WDATA[31:24];
											dirty[cache_index][way_hit_index] <= 1;
										end
									end
								end
								else begin
									SystemResourceCheck.axi_data_cache.ARREADY <= False;
									begin : sv2v_autoblock_1
										reg [0:0] sv2v_tmp_cast;
										reg [0:0] sv2v_tmp_cast_1;
										sv2v_tmp_cast = way_hit_index;
										sv2v_tmp_cast_1 = victim_way_index;
										saved <= {is_read, req_addr, SystemResourceCheck.axi_data_cache.WDATA, SystemResourceCheck.axi_data_cache.WSTRB, cache_index, req_tag, sv2v_tmp_cast, sv2v_tmp_cast_1};
									end
									current_state <= 32'd3;
								end
								if (!SystemResourceCheck.axi_data_cache.RREADY || !SystemResourceCheck.axi_data_cache.BREADY) begin
									SystemResourceCheck.axi_data_cache.ARREADY <= False;
									SystemResourceCheck.axi_data_cache.AWREADY <= False;
									SystemResourceCheck.axi_data_cache.WREADY <= False;
								end
							end
							else if (is_request && !cache_hit) begin
								SystemResourceCheck.axi_data_cache.ARREADY <= False;
								SystemResourceCheck.axi_data_cache.AWREADY <= False;
								SystemResourceCheck.axi_data_cache.WREADY <= False;
								read_miss <= is_read;
								begin : sv2v_autoblock_2
									reg [0:0] sv2v_tmp_cast;
									reg [0:0] sv2v_tmp_cast_1;
									sv2v_tmp_cast = way_hit_index;
									sv2v_tmp_cast_1 = victim_way_index;
									saved <= {is_read, req_addr, SystemResourceCheck.axi_data_cache.WDATA, SystemResourceCheck.axi_data_cache.WSTRB, cache_index, req_tag, sv2v_tmp_cast, sv2v_tmp_cast_1};
								end
								if (!victim_is_dirty) begin
									SystemResourceCheck.axi_mem_rw.ARVALID <= True;
									SystemResourceCheck.axi_mem_rw.ARADDR <= req_addr;
									SystemResourceCheck.axi_mem_rw.RREADY <= True;
									current_state <= 32'd1;
								end
								else begin
									SystemResourceCheck.axi_mem_rw.AWVALID <= True;
									SystemResourceCheck.axi_mem_rw.AWADDR <= victim_addr;
									SystemResourceCheck.axi_mem_rw.WVALID <= True;
									SystemResourceCheck.axi_mem_rw.WDATA <= data[cache_index];
									SystemResourceCheck.axi_mem_rw.WSTRB <= 4'hf;
									SystemResourceCheck.axi_mem_rw.BREADY <= True;
									current_state <= 32'd2;
								end
							end
							if ((SystemResourceCheck.axi_data_cache.RVALID && SystemResourceCheck.axi_data_cache.RREADY) && !(is_read_request && cache_hit)) begin
								SystemResourceCheck.axi_data_cache.RVALID <= False;
								SystemResourceCheck.axi_data_cache.RDATA <= 0;
							end
							if ((SystemResourceCheck.axi_data_cache.BVALID && SystemResourceCheck.axi_data_cache.BREADY) && !(is_write_request && cache_hit))
								SystemResourceCheck.axi_data_cache.BVALID <= False;
						end
						32'd3:
							if (SystemResourceCheck.axi_data_cache.RREADY) begin
								lru[saved[IndexBits + (TagBits + 1)-:((IndexBits + (TagBits + 1)) >= (TagBits + 2) ? ((IndexBits + (TagBits + 1)) - (TagBits + 2)) + 1 : ((TagBits + 2) - (IndexBits + (TagBits + 1))) + 1)]][0] <= ~saved[1-:1];
								SystemResourceCheck.axi_data_cache.RVALID <= True;
								SystemResourceCheck.axi_data_cache.RDATA <= data[saved[IndexBits + (TagBits + 1)-:((IndexBits + (TagBits + 1)) >= (TagBits + 2) ? ((IndexBits + (TagBits + 1)) - (TagBits + 2)) + 1 : ((TagBits + 2) - (IndexBits + (TagBits + 1))) + 1)]];
								current_state <= 32'd0;
							end
						32'd1: begin
							if (SystemResourceCheck.axi_mem_rw.ARREADY) begin
								SystemResourceCheck.axi_mem_rw.ARVALID <= False;
								SystemResourceCheck.axi_mem_rw.ARADDR <= 0;
							end
							if (SystemResourceCheck.axi_mem_rw.RVALID && (SystemResourceCheck.axi_mem_rw.RRESP == 2'b00)) begin
								data[saved[IndexBits + (TagBits + 1)-:((IndexBits + (TagBits + 1)) >= (TagBits + 2) ? ((IndexBits + (TagBits + 1)) - (TagBits + 2)) + 1 : ((TagBits + 2) - (IndexBits + (TagBits + 1))) + 1)]] <= SystemResourceCheck.axi_mem_rw.RDATA;
								valid[saved[IndexBits + (TagBits + 1)-:((IndexBits + (TagBits + 1)) >= (TagBits + 2) ? ((IndexBits + (TagBits + 1)) - (TagBits + 2)) + 1 : ((TagBits + 2) - (IndexBits + (TagBits + 1))) + 1)]][saved[0-:1]] <= True;
								dirty[saved[IndexBits + (TagBits + 1)-:((IndexBits + (TagBits + 1)) >= (TagBits + 2) ? ((IndexBits + (TagBits + 1)) - (TagBits + 2)) + 1 : ((TagBits + 2) - (IndexBits + (TagBits + 1))) + 1)]][saved[0-:1]] <= False;
								tag[saved[IndexBits + (TagBits + 1)-:((IndexBits + (TagBits + 1)) >= (TagBits + 2) ? ((IndexBits + (TagBits + 1)) - (TagBits + 2)) + 1 : ((TagBits + 2) - (IndexBits + (TagBits + 1))) + 1)]] <= saved[TagBits + 1-:((TagBits + 1) >= 2 ? TagBits : 3 - (TagBits + 1))];
								SystemResourceCheck.axi_mem_rw.RREADY <= False;
								current_state <= 32'd0;
								SystemResourceCheck.axi_data_cache.ARREADY <= True;
								SystemResourceCheck.axi_data_cache.AWREADY <= True;
								SystemResourceCheck.axi_data_cache.WREADY <= True;
								lru[saved[IndexBits + (TagBits + 1)-:((IndexBits + (TagBits + 1)) >= (TagBits + 2) ? ((IndexBits + (TagBits + 1)) - (TagBits + 2)) + 1 : ((TagBits + 2) - (IndexBits + (TagBits + 1))) + 1)]][0] <= ~saved[1-:1];
								if (read_miss) begin
									SystemResourceCheck.axi_data_cache.RDATA <= SystemResourceCheck.axi_mem_rw.RDATA;
									SystemResourceCheck.axi_data_cache.RVALID <= True;
								end
								else begin
									SystemResourceCheck.axi_data_cache.BVALID <= True;
									if (saved[(4 + (IndexBits + (TagBits + 1))) - 3]) begin
										data[saved[IndexBits + (TagBits + 1)-:((IndexBits + (TagBits + 1)) >= (TagBits + 2) ? ((IndexBits + (TagBits + 1)) - (TagBits + 2)) + 1 : ((TagBits + 2) - (IndexBits + (TagBits + 1))) + 1)]][7:0] <= saved[(36 + (IndexBits + (TagBits + 1))) - 24:(36 + (IndexBits + (TagBits + 1))) - 31];
										dirty[saved[IndexBits + (TagBits + 1)-:((IndexBits + (TagBits + 1)) >= (TagBits + 2) ? ((IndexBits + (TagBits + 1)) - (TagBits + 2)) + 1 : ((TagBits + 2) - (IndexBits + (TagBits + 1))) + 1)]][saved[1-:1]] <= 1;
									end
									if (saved[(4 + (IndexBits + (TagBits + 1))) - 2]) begin
										data[saved[IndexBits + (TagBits + 1)-:((IndexBits + (TagBits + 1)) >= (TagBits + 2) ? ((IndexBits + (TagBits + 1)) - (TagBits + 2)) + 1 : ((TagBits + 2) - (IndexBits + (TagBits + 1))) + 1)]][15:8] <= saved[(36 + (IndexBits + (TagBits + 1))) - 16:(36 + (IndexBits + (TagBits + 1))) - 23];
										dirty[saved[IndexBits + (TagBits + 1)-:((IndexBits + (TagBits + 1)) >= (TagBits + 2) ? ((IndexBits + (TagBits + 1)) - (TagBits + 2)) + 1 : ((TagBits + 2) - (IndexBits + (TagBits + 1))) + 1)]][saved[1-:1]] <= 1;
									end
									if (saved[(4 + (IndexBits + (TagBits + 1))) - 1]) begin
										data[saved[IndexBits + (TagBits + 1)-:((IndexBits + (TagBits + 1)) >= (TagBits + 2) ? ((IndexBits + (TagBits + 1)) - (TagBits + 2)) + 1 : ((TagBits + 2) - (IndexBits + (TagBits + 1))) + 1)]][23:16] <= saved[(36 + (IndexBits + (TagBits + 1))) - 8:(36 + (IndexBits + (TagBits + 1))) - 15];
										dirty[saved[IndexBits + (TagBits + 1)-:((IndexBits + (TagBits + 1)) >= (TagBits + 2) ? ((IndexBits + (TagBits + 1)) - (TagBits + 2)) + 1 : ((TagBits + 2) - (IndexBits + (TagBits + 1))) + 1)]][saved[1-:1]] <= 1;
									end
									if (saved[4 + (IndexBits + (TagBits + 1))]) begin
										data[saved[IndexBits + (TagBits + 1)-:((IndexBits + (TagBits + 1)) >= (TagBits + 2) ? ((IndexBits + (TagBits + 1)) - (TagBits + 2)) + 1 : ((TagBits + 2) - (IndexBits + (TagBits + 1))) + 1)]][31:24] <= saved[36 + (IndexBits + (TagBits + 1)):(36 + (IndexBits + (TagBits + 1))) - 7];
										dirty[saved[IndexBits + (TagBits + 1)-:((IndexBits + (TagBits + 1)) >= (TagBits + 2) ? ((IndexBits + (TagBits + 1)) - (TagBits + 2)) + 1 : ((TagBits + 2) - (IndexBits + (TagBits + 1))) + 1)]][saved[1-:1]] <= 1;
									end
								end
							end
						end
						32'd2: begin
							if (SystemResourceCheck.axi_mem_rw.AWREADY) begin
								SystemResourceCheck.axi_mem_rw.AWVALID <= False;
								SystemResourceCheck.axi_mem_rw.AWADDR <= 0;
								SystemResourceCheck.axi_mem_rw.WVALID <= False;
								SystemResourceCheck.axi_mem_rw.WDATA <= 0;
								SystemResourceCheck.axi_mem_rw.WSTRB <= 0;
							end
							if (SystemResourceCheck.axi_mem_rw.BVALID && (SystemResourceCheck.axi_mem_rw.BRESP == 2'b00)) begin
								SystemResourceCheck.axi_mem_rw.ARVALID <= True;
								SystemResourceCheck.axi_mem_rw.ARADDR <= saved[68 + (IndexBits + (TagBits + 1))-:((71 + (TagBits + 1)) >= (39 + (TagBits + 2)) ? ((68 + (IndexBits + (TagBits + 1))) - (36 + (IndexBits + (TagBits + 2)))) + 1 : ((36 + (IndexBits + (TagBits + 2))) - (68 + (IndexBits + (TagBits + 1)))) + 1)];
								SystemResourceCheck.axi_mem_rw.RREADY <= True;
								SystemResourceCheck.axi_mem_rw.BREADY <= False;
								current_state <= 32'd1;
							end
						end
						default:
							;
					endcase
			initial _sv2v_0 = 0;
		end
	endgenerate
	assign dcache.ACLK = clk;
	assign dcache.ARESETn = ~rst;
	function automatic [1:0] sv2v_cast_2;
		input reg [1:0] inp;
		sv2v_cast_2 = inp;
	endfunction
	generate
		if (1) begin : datapath
			reg _sv2v_0;
			wire clk;
			wire rst;
			wire halt;
			wire [31:0] trace_writeback_pc;
			wire [31:0] trace_writeback_insn;
			wire [31:0] trace_writeback_cycle_status;
			reg [31:0] cycles_current;
			always @(posedge clk)
				if (rst)
					cycles_current <= 0;
				else
					cycles_current <= cycles_current + 1;
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
			reg [31:0] w_rd_data;
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
			assign unsigned_dividend = (x_rs1_data[31] ? ~x_rs1_data + 1 : x_rs1_data);
			assign unsigned_divisor = (x_rs2_data[31] ? ~x_rs2_data + 1 : x_rs2_data);
			reg [31:0] dividend;
			reg [31:0] divisor;
			always @(*) begin
				if (_sv2v_0)
					;
				dividend = x_rs1_data;
				divisor = x_rs2_data;
				if (x_insn_key[5] || x_insn_key[3]) begin
					dividend = unsigned_dividend;
					divisor = unsigned_divisor;
				end
			end
			reg div_sign_7;
			assign signed_quotient = (div_sign_7 ? ~unsigned_quotient + 1 : unsigned_quotient);
			reg dividend_sign_7;
			assign signed_remainder = (dividend_sign_7 ? ~unsigned_remainder + 1 : unsigned_remainder);
			DividerUnsignedPipelined divider(
				.clk(clk),
				.rst(rst),
				.stall(0),
				.i_dividend(dividend),
				.i_divisor(divisor),
				.o_quotient(unsigned_quotient),
				.o_remainder(unsigned_remainder)
			);
			reg [2:0] div_count_latest;
			reg [2:0] div_count_first;
			wire d_div_insn;
			wire [46:0] d_insn_key;
			assign d_div_insn = ((d_insn_key[5] || d_insn_key[4]) || d_insn_key[3]) || d_insn_key[2];
			wire x_div_insn;
			assign x_div_insn = ((x_insn_key[5] || x_insn_key[4]) || x_insn_key[3]) || x_insn_key[2];
			wire div_stall;
			wire [4:0] x_insn_rd;
			assign div_stall = (x_div_insn && (~d_div_insn || ((x_insn_rd == d_insn_rs1) || (x_insn_rd == d_insn_rs2)))) && (div_count_latest != 0);
			always @(posedge clk) begin
				div_count_first <= 0;
				div_count_latest <= 0;
				if (rst) begin
					div_count_first <= 0;
					div_count_latest <= 0;
				end
				else begin
					if ((div_count_latest > div_count_first) && (div_count_first == 0))
						div_count_first <= 0;
					else if (d_div_insn || x_div_insn)
						div_count_first <= div_count_first + 1;
					if (div_stall)
						div_count_latest <= div_count_latest + 1;
					else if (d_div_insn || x_div_insn)
						div_count_latest <= 1;
				end
			end
			reg div_by_zero_1;
			reg div_sign_1;
			reg dividend_sign_1;
			reg [31:0] div_pc_1;
			reg [31:0] div_insn_1;
			reg [4:0] div_insn_rd_1;
			wire [31:0] x_insn;
			wire [31:0] x_pc;
			always @(posedge clk)
				if (rst) begin
					div_by_zero_1 <= 0;
					div_sign_1 <= 0;
					dividend_sign_1 <= 0;
					div_pc_1 <= 0;
					div_insn_1 <= 0;
					div_insn_rd_1 <= 0;
				end
				else begin
					div_by_zero_1 <= x_rs2_data == 0;
					div_sign_1 <= x_rs1_data[31] ^ x_rs2_data[31];
					dividend_sign_1 <= x_rs1_data[31];
					div_pc_1 <= x_pc;
					div_insn_1 <= x_insn;
					div_insn_rd_1 <= x_insn_rd;
				end
			reg div_by_zero_2;
			reg div_sign_2;
			reg dividend_sign_2;
			reg [31:0] div_pc_2;
			reg [31:0] div_insn_2;
			reg [4:0] div_insn_rd_2;
			always @(posedge clk)
				if (rst) begin
					div_by_zero_2 <= 0;
					div_sign_2 <= 0;
					dividend_sign_2 <= 0;
					div_pc_2 <= 0;
					div_insn_2 <= 0;
					div_insn_rd_2 <= 0;
				end
				else begin
					div_by_zero_2 <= div_by_zero_1;
					div_sign_2 <= div_sign_1;
					dividend_sign_2 <= dividend_sign_1;
					div_pc_2 <= div_pc_1;
					div_insn_2 <= div_insn_1;
					div_insn_rd_2 <= div_insn_rd_1;
				end
			reg div_by_zero_3;
			reg div_sign_3;
			reg dividend_sign_3;
			reg [31:0] div_pc_3;
			reg [31:0] div_insn_3;
			reg [4:0] div_insn_rd_3;
			always @(posedge clk)
				if (rst) begin
					div_by_zero_3 <= 0;
					div_sign_3 <= 0;
					dividend_sign_3 <= 0;
					div_pc_3 <= 0;
					div_insn_3 <= 0;
					div_insn_rd_3 <= 0;
				end
				else begin
					div_by_zero_3 <= div_by_zero_2;
					div_sign_3 <= div_sign_2;
					dividend_sign_3 <= dividend_sign_2;
					div_pc_3 <= div_pc_2;
					div_insn_3 <= div_insn_2;
					div_insn_rd_3 <= div_insn_rd_2;
				end
			reg div_by_zero_4;
			reg div_sign_4;
			reg dividend_sign_4;
			reg [31:0] div_pc_4;
			reg [31:0] div_insn_4;
			reg [4:0] div_insn_rd_4;
			always @(posedge clk)
				if (rst) begin
					div_by_zero_4 <= 0;
					div_sign_4 <= 0;
					dividend_sign_4 <= 0;
					div_pc_4 <= 0;
					div_insn_4 <= 0;
					div_insn_rd_4 <= 0;
				end
				else begin
					div_by_zero_4 <= div_by_zero_3;
					div_sign_4 <= div_sign_3;
					dividend_sign_4 <= dividend_sign_3;
					div_pc_4 <= div_pc_3;
					div_insn_4 <= div_insn_3;
					div_insn_rd_4 <= div_insn_rd_3;
				end
			reg div_by_zero_5;
			reg div_sign_5;
			reg dividend_sign_5;
			reg [31:0] div_pc_5;
			reg [31:0] div_insn_5;
			reg [4:0] div_insn_rd_5;
			always @(posedge clk)
				if (rst) begin
					div_by_zero_5 <= 0;
					div_sign_5 <= 0;
					dividend_sign_5 <= 0;
					div_pc_5 <= 0;
					div_insn_5 <= 0;
					div_insn_rd_5 <= 0;
				end
				else begin
					div_by_zero_5 <= div_by_zero_4;
					div_sign_5 <= div_sign_4;
					dividend_sign_5 <= dividend_sign_4;
					div_pc_5 <= div_pc_4;
					div_insn_5 <= div_insn_4;
					div_insn_rd_5 <= div_insn_rd_4;
				end
			reg div_by_zero_6;
			reg div_sign_6;
			reg dividend_sign_6;
			reg [31:0] div_pc_6;
			reg [31:0] div_insn_6;
			reg [4:0] div_insn_rd_6;
			always @(posedge clk)
				if (rst) begin
					div_by_zero_6 <= 0;
					div_sign_6 <= 0;
					dividend_sign_6 <= 0;
					div_pc_6 <= 0;
					div_insn_6 <= 0;
					div_insn_rd_6 <= 0;
				end
				else begin
					div_by_zero_6 <= div_by_zero_5;
					div_sign_6 <= div_sign_5;
					dividend_sign_6 <= dividend_sign_5;
					div_pc_6 <= div_pc_5;
					div_insn_6 <= div_insn_5;
					div_insn_rd_6 <= div_insn_rd_5;
				end
			reg div_by_zero_7;
			reg [31:0] div_pc_7;
			reg [31:0] div_insn_7;
			reg [4:0] div_insn_rd_7;
			always @(posedge clk)
				if (rst) begin
					div_by_zero_7 <= 0;
					div_sign_7 <= 0;
					dividend_sign_7 <= 0;
					div_pc_7 <= 0;
					div_insn_7 <= 0;
					div_insn_rd_7 <= 0;
				end
				else begin
					div_by_zero_7 <= div_by_zero_6;
					div_sign_7 <= div_sign_6;
					dividend_sign_7 <= dividend_sign_6;
					div_pc_7 <= div_pc_6;
					div_insn_7 <= div_insn_6;
					div_insn_rd_7 <= div_insn_rd_6;
				end
			reg [31:0] f_pc_current;
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
				else if (data_dependent_load || div_stall) begin
					f_pc_current <= f_pc_current;
					f_cycle_status <= 32'd2;
				end
				else begin
					f_cycle_status <= 32'd2;
					f_pc_current <= f_pc_current + 4;
				end
			wire fetch_insn;
			assign fetch_insn = 1;
			always @(*) begin
				if (_sv2v_0)
					;
				SystemResourceCheck.axi_mem_ro.ARVALID = 0;
				SystemResourceCheck.axi_mem_ro.ARADDR = 0;
				SystemResourceCheck.axi_mem_ro.RREADY = 0;
				if (fetch_insn) begin
					SystemResourceCheck.axi_mem_ro.ARVALID = 1;
					SystemResourceCheck.axi_mem_ro.ARADDR = f_pc_current;
					SystemResourceCheck.axi_mem_ro.RREADY = 1;
				end
			end
			wire [255:0] d_disasm;
			reg [31:0] d_insn;
			Disasm #(.PREFIX("D")) disasm_1decode(
				.insn(d_insn),
				.disasm(d_disasm)
			);
			wire [255:0] x_disasm;
			reg [435:0] execute_state;
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
			reg [190:0] write_state;
			Disasm #(.PREFIX("W")) disasm_4write(
				.insn(write_state[158-:32]),
				.disasm(w_disasm)
			);
			reg [99:0] decode_state_temp;
			wire d_branch_mispredict;
			wire [31:0] d_cycle_status;
			reg d_data_dep_load_in_x;
			wire [31:0] d_pc_current;
			reg [99:0] decode_state;
			wire [31:0] icache_rdata;
			always @(*) begin
				if (_sv2v_0)
					;
				if (rst) begin
					decode_state_temp = 0;
					decode_state_temp[35-:32] = 32'd1;
				end
				else if (d_branch_mispredict) begin
					decode_state_temp = 0;
					decode_state_temp[35-:32] = 32'd4;
					decode_state_temp[3] = 1;
					decode_state_temp[1-:2] = 1;
				end
				else if (data_dependent_load || ((decode_state[1-:2] > 0) && decode_state[2])) begin
					decode_state_temp = {d_pc_current, icache_rdata, d_cycle_status, 2'h1, sv2v_cast_2(0 + d_data_dep_load_in_x)};
					if (decode_state[1-:2] > 0) begin
						decode_state_temp[67-:32] = decode_state[67-:32];
						decode_state_temp[1-:2] = decode_state[1-:2] - 1;
					end
				end
				else if (div_stall) begin
					decode_state_temp = {d_pc_current, icache_rdata, d_cycle_status, 4'h0};
					if (div_count_latest > 1)
						decode_state_temp[67-:32] = decode_state[67-:32];
				end
				else begin
					decode_state_temp = {f_pc_current, 32'd0, f_cycle_status, decode_state[3], decode_state[2], sv2v_cast_2(decode_state[1-:2] - 1)};
					if (decode_state[1-:2] == 0) begin
						decode_state_temp[1-:2] = 0;
						decode_state_temp[2] = 0;
						decode_state_temp[3] = 0;
					end
				end
			end
			always @(posedge clk) decode_state <= decode_state_temp;
			assign d_pc_current = decode_state[99-:32];
			assign d_cycle_status = decode_state[35-:32];
			assign d_branch_mispredict = x_branch_taken;
			reg [4:0] d_rs1;
			reg [4:0] d_rs2;
			reg [6:0] d_opcode;
			always @(*) begin
				if (_sv2v_0)
					;
				d_rs1 = icache_rdata[19:15];
				d_rs2 = icache_rdata[24:20];
				d_opcode = icache_rdata[6:0];
				if (decode_state[67-:32] != 0) begin
					d_rs1 = decode_state[55:51];
					d_rs2 = decode_state[60:56];
					d_opcode = decode_state[42:36];
				end
			end
			wire d_branch_stall;
			wire d_load_stall;
			wire [1:0] d_stall_count;
			wire [4:0] m_insn_rd;
			wire [6:0] m_opcode;
			always @(*) begin
				if (_sv2v_0)
					;
				data_dependent_load = 0;
				d_data_dep_load_in_x = 0;
				if (x_opcode == OpLoad) begin
					if (((d_opcode == OpStore) || (d_opcode == OpRegImm)) || (d_opcode == OpLoad)) begin
						data_dependent_load = x_insn_rd == d_rs1;
						d_data_dep_load_in_x = 1;
					end
					else if ((d_opcode != OpLui) && (d_opcode != OpJal)) begin
						data_dependent_load = (x_insn_rd == d_rs1) || (x_insn_rd == d_rs2);
						d_data_dep_load_in_x = 1;
					end
				end
				else if (m_opcode == OpLoad) begin
					if (((d_opcode == OpStore) || (d_opcode == OpRegImm)) || (d_opcode == OpLoad))
						data_dependent_load = m_insn_rd == d_rs1;
					else if ((d_opcode != OpLui) && (d_opcode != OpJal))
						data_dependent_load = (m_insn_rd == d_rs1) || (m_insn_rd == d_rs2);
				end
			end
			assign icache_rdata = SystemResourceCheck.axi_mem_ro.RDATA;
			always @(*) begin
				if (_sv2v_0)
					;
				d_insn = icache_rdata;
				if (d_branch_mispredict || data_dependent_load)
					d_insn = 0;
				else if (decode_state[1-:2] > 0)
					d_insn = 0;
				else if ((decode_state[1-:2] == 0) && decode_state[2])
					d_insn = decode_state[67-:32];
				else if (x_div_insn && (div_count_latest == 0))
					d_insn = decode_state[67-:32];
			end
			wire [6:0] d_insn_funct7;
			wire [2:0] d_insn_funct3;
			wire [4:0] d_insn_rd;
			wire [4:0] d_insn_rd_temp;
			wire [6:0] d_insn_opcode;
			assign {d_insn_funct7, d_insn_rs2, d_insn_rs1, d_insn_funct3, d_insn_rd_temp, d_insn_opcode} = d_insn;
			assign d_insn_rd = ((d_insn_opcode == OpBranch) || (d_insn_opcode == OpStore) ? 0 : d_insn_rd_temp);
			wire [11:0] d_imm_i;
			assign d_imm_i = d_insn[31:20];
			wire [11:0] d_imm_s;
			assign d_imm_s[11:5] = d_insn_funct7;
			assign d_imm_s[4:0] = d_insn_rd_temp;
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
				else if (div_stall) begin
					execute_state <= execute_state;
					execute_state[371-:32] <= 32'd8;
				end
				else
					execute_state <= normal_execute_state;
			reg x_we;
			reg [31:0] x_rd_data;
			assign x_pc = execute_state[435-:32];
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
							x_insn_key[5]:
								if (div_by_zero_7)
									x_rd_data = 32'hffffffff;
								else
									x_rd_data = signed_quotient;
							x_insn_key[4]: x_rd_data = unsigned_quotient;
							x_insn_key[3]: x_rd_data = signed_remainder;
							x_insn_key[2]: x_rd_data = unsigned_remainder;
						endcase
					end
					OpBranch: begin
						x_branched_pc = x_pc + x_imm_b_sext;
						case (1)
							x_insn_key[42]: x_branch_taken = x_rs1_data == x_rs2_data;
							x_insn_key[41]: x_branch_taken = x_rs1_data != x_rs2_data;
							x_insn_key[40]: x_branch_taken = $signed(x_rs1_data) < $signed(x_rs2_data);
							x_insn_key[39]: x_branch_taken = $signed(x_rs1_data) >= $signed(x_rs2_data);
							x_insn_key[38]: x_branch_taken = $unsigned(x_rs1_data) < $unsigned(x_rs2_data);
							x_insn_key[37]: x_branch_taken = $unsigned(x_rs1_data) >= $unsigned(x_rs2_data);
						endcase
					end
					OpLoad: begin
						x_we = 1;
						x_addr_to_dmem = cla_sum;
					end
					OpStore: x_addr_to_dmem = cla_sum;
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
				else if (x_div_insn && ~(div_count_first == 3'b000)) begin
					memory_state <= 0;
					memory_state[262-:32] <= 32'd8;
				end
				else if (x_div_insn)
					memory_state <= {div_pc_7, div_insn_7, 32'd2, div_insn_7[6:0], div_insn_rd_7, x_rd_data, 187'h40000000000000000000000000000000000000000000000};
				else
					memory_state <= {x_pc, x_insn, x_cycle_status, x_opcode, x_insn_rd, x_rd_data, x_we, x_addr_to_dmem, x_store_mem_to_dmem, x_store_we_to_dmem, x_rs2_data, x_insn_rs2, x_branched_pc, x_branch_taken, x_insn_key, x_halt};
			wire [31:0] m_pc;
			assign m_pc = memory_state[326-:32];
			wire [31:0] m_insn;
			assign m_insn = memory_state[294-:32];
			wire [31:0] m_cycle_status;
			assign m_cycle_status = memory_state[262-:32];
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
			reg m_write;
			reg m_read;
			always @(*) begin
				if (_sv2v_0)
					;
				SystemResourceCheck.axi_data_cache.ARVALID = 0;
				SystemResourceCheck.axi_data_cache.ARADDR = 0;
				SystemResourceCheck.axi_data_cache.AWVALID = 0;
				SystemResourceCheck.axi_data_cache.AWADDR = 0;
				SystemResourceCheck.axi_data_cache.WDATA = 0;
				SystemResourceCheck.axi_data_cache.WSTRB = 0;
				SystemResourceCheck.axi_data_cache.WVALID = 0;
				if (m_read) begin
					SystemResourceCheck.axi_data_cache.ARVALID = 1;
					SystemResourceCheck.axi_data_cache.ARADDR = m_addr_to_dmem & 32'hfffffffc;
				end
				else if (m_write) begin
					SystemResourceCheck.axi_data_cache.AWVALID = 1;
					SystemResourceCheck.axi_data_cache.AWADDR = m_addr_to_dmem & 32'hfffffffc;
					SystemResourceCheck.axi_data_cache.WDATA = m_store_data_to_dmem;
					SystemResourceCheck.axi_data_cache.WSTRB = m_store_we_to_dmem;
					SystemResourceCheck.axi_data_cache.WVALID = 1;
				end
			end
			wire w_insn_load;
			always @(*) begin
				if (_sv2v_0)
					;
				m_rs2_data = m_rs2_data_temp;
				if ((m_opcode == OpStore) && (m_insn_rs2 != 0)) begin
					if (w_insn_load && (w_insn_rd == m_insn_rs2))
						m_rs2_data = w_rd_data;
				end
			end
			always @(*) begin
				if (_sv2v_0)
					;
				m_rd_data = m_rd_data_temp;
				m_store_we_to_dmem = 0;
				m_store_data_to_dmem = 0;
				m_write = 0;
				m_read = 0;
				case (m_opcode)
					OpLoad: m_read = 1;
					OpStore: begin
						m_write = 1;
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
					end
					default:
						;
				endcase
			end
			always @(posedge clk)
				if (rst) begin
					write_state <= 0;
					write_state[126-:32] <= 32'd1;
				end
				else
					write_state <= {m_pc, m_insn, m_cycle_status, m_opcode, m_insn_rd, m_rd_data, m_we, m_insn_key, m_mem_bytes, m_halt};
			wire [31:0] w_pc;
			assign w_pc = write_state[190-:32];
			wire [31:0] w_insn;
			assign w_insn = write_state[158-:32];
			wire [31:0] w_cycle_status;
			assign w_cycle_status = write_state[126-:32];
			wire [46:0] w_insn_key;
			assign w_insn_key = write_state[49-:47];
			wire [6:0] w_opcode;
			assign w_insn_load = w_opcode == OpLoad;
			assign w_opcode = write_state[94-:7];
			assign w_insn_rd = write_state[87-:5];
			wire [31:0] w_rd_data_temp;
			assign w_rd_data_temp = write_state[82-:32];
			wire [1:0] w_mem_bytes;
			assign w_mem_bytes = write_state[2-:2];
			assign w_we = write_state[50];
			wire w_halt;
			assign w_halt = write_state[0];
			assign halt = w_halt;
			assign trace_writeback_pc = w_pc;
			assign trace_writeback_insn = w_insn;
			assign trace_writeback_cycle_status = w_cycle_status;
			always @(*) begin
				if (_sv2v_0)
					;
				w_rd_data = w_rd_data_temp;
				if (w_opcode == OpLoad)
					case (1)
						w_insn_key[36]:
							case (w_mem_bytes)
								0: w_rd_data = {{24 {SystemResourceCheck.axi_data_cache.RDATA[7]}}, SystemResourceCheck.axi_data_cache.RDATA[7:0]};
								1: w_rd_data = {{24 {SystemResourceCheck.axi_data_cache.RDATA[15]}}, SystemResourceCheck.axi_data_cache.RDATA[15:8]};
								2: w_rd_data = {{24 {SystemResourceCheck.axi_data_cache.RDATA[23]}}, SystemResourceCheck.axi_data_cache.RDATA[23:16]};
								3: w_rd_data = {{24 {SystemResourceCheck.axi_data_cache.RDATA[31]}}, SystemResourceCheck.axi_data_cache.RDATA[31:24]};
							endcase
						w_insn_key[35]:
							if (w_mem_bytes[1])
								w_rd_data = {{16 {SystemResourceCheck.axi_data_cache.RDATA[31]}}, SystemResourceCheck.axi_data_cache.RDATA[31:16]};
							else
								w_rd_data = {{16 {SystemResourceCheck.axi_data_cache.RDATA[15]}}, SystemResourceCheck.axi_data_cache.RDATA[15:0]};
						w_insn_key[34]: w_rd_data = SystemResourceCheck.axi_data_cache.RDATA;
						w_insn_key[33]:
							case (w_mem_bytes)
								0: w_rd_data = {{24 {1'b0}}, SystemResourceCheck.axi_data_cache.RDATA[7:0]};
								1: w_rd_data = {{24 {1'b0}}, SystemResourceCheck.axi_data_cache.RDATA[15:8]};
								2: w_rd_data = {{24 {1'b0}}, SystemResourceCheck.axi_data_cache.RDATA[23:16]};
								3: w_rd_data = {{24 {1'b0}}, SystemResourceCheck.axi_data_cache.RDATA[31:24]};
							endcase
						w_insn_key[32]:
							if (w_mem_bytes[1])
								w_rd_data = {{16 {1'b0}}, SystemResourceCheck.axi_data_cache.RDATA[31:16]};
							else
								w_rd_data = {{16 {1'b0}}, SystemResourceCheck.axi_data_cache.RDATA[15:0]};
					endcase
			end
			initial _sv2v_0 = 0;
		end
	endgenerate
	assign datapath.clk = clk;
	assign datapath.rst = rst;
	assign led[0] = datapath.halt;
endmodule