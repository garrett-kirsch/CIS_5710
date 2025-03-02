/* INSERT NAME AND PENNKEY HERE */

`timescale 1ns / 1ns

// quotient = dividend / divisor

module DividerUnsignedPipelined (
    input wire clk, rst, stall,
    input  wire  [31:0] i_dividend,
    input  wire  [31:0] i_divisor,
    output logic [31:0] o_remainder,
    output logic [31:0] o_quotient
);
    // values we will be storing in registers each cycle
    logic[31:0] stored_dividend [7];
    logic[31:0] stored_remainder [7];
    logic[31:0] stored_quotient [7];
    logic[31:0] stored_divisor [7];

    // values we will using for in-stage calculations
    wire [31:0] dividend [32];
    wire [31:0] remainder [32];
    wire [31:0] quotient [32];

    // every stage, we want to go through 4 divu_1iter's 
    // then store the calculated value in a register
    // 1 -> reg -> 2 -> reg -> 3 -> reg -> 4 -> reg -> 5 -> reg -> 6 -> reg -> 7 -> reg -> 8

    // store values in registers
    always @(posedge clk) begin
        if (rst) begin
            stored_dividend <= '{default: '0};
            stored_quotient <= '{default: '0};
            stored_remainder <= '{default: '0};
        end else begin
            // save divu_iter outputs
            stored_dividend[0] <= dividend[3];
            stored_quotient[0] <= quotient[3];
            stored_remainder[0] <= remainder[3];

            stored_dividend[1] <= dividend[7];
            stored_quotient[1] <= quotient[7];
            stored_remainder[1] <= remainder[7];

            stored_dividend[2] <= dividend[11];
            stored_quotient[2] <= quotient[11];
            stored_remainder[2] <= remainder[11];

            stored_dividend[3] <= dividend[15];
            stored_quotient[3] <= quotient[15];
            stored_remainder[3] <= remainder[15];

            stored_dividend[4] <= dividend[19];
            stored_quotient[4] <= quotient[19];
            stored_remainder[4] <= remainder[19];

            stored_dividend[5] <= dividend[23];
            stored_quotient[5] <= quotient[23];
            stored_remainder[5] <= remainder[23];

            stored_dividend[6] <= dividend[27];
            stored_quotient[6] <= quotient[27];
            stored_remainder[6] <= remainder[27];

            // save divisor
            stored_divisor[0] <= i_divisor;
            stored_divisor[1] <= stored_divisor[0];
            stored_divisor[2] <= stored_divisor[1];
            stored_divisor[3] <= stored_divisor[2];
            stored_divisor[4] <= stored_divisor[3];
            stored_divisor[5] <= stored_divisor[4];
            stored_divisor[6] <= stored_divisor[5];
        end
    end

    // Cycle 1

    divu_1iter d1(.i_dividend(i_dividend), .i_divisor(i_divisor), .i_remainder(0), .i_quotient(0),
                    .o_dividend(dividend[0]), .o_remainder(remainder[0]), .o_quotient(quotient[0]));

    genvar k;
    for (k = 0; k < 3; k = k + 1) begin
        divu_1iter d2(.i_dividend(dividend[k]), .i_divisor(i_divisor), .i_remainder(remainder[k]), .i_quotient(quotient[k]),
                    .o_dividend(dividend[k+1]), .o_remainder(remainder[k+1]), .o_quotient(quotient[k+1]));
    end

    // Cycle 2 - 8

    genvar j;
    for (j = 0; j < 7; j = j + 1) begin
        divu_1iter d3(.i_dividend(stored_dividend[j]), .i_divisor(stored_divisor[j]), .i_remainder(stored_remainder[j]), 
            .i_quotient(stored_quotient[j]), .o_dividend(dividend[4 * (j + 1)]), .o_remainder(remainder[4 * (j + 1)]), .o_quotient(quotient[4 * (j + 1)]));

        genvar i;
        for (i = 4 * (j + 1); i < 4 * (j + 1) + 3; i = i + 1) begin
            divu_1iter d4(.i_dividend(dividend[i]), .i_divisor(stored_divisor[j]), .i_remainder(remainder[i]), .i_quotient(quotient[i]),
                        .o_dividend(dividend[i+1]), .o_remainder(remainder[i+1]), .o_quotient(quotient[i+1]));
        end
    end

    // Read Output
    assign o_quotient = quotient[31];
    assign o_remainder = remainder[31];


endmodule


module divu_1iter (
    input  wire  [31:0] i_dividend,
    input  wire  [31:0] i_divisor,
    input  wire  [31:0] i_remainder,
    input  wire  [31:0] i_quotient,
    output logic [31:0] o_dividend,
    output logic [31:0] o_remainder,
    output logic [31:0] o_quotient
);

    // NOTE: I changed (i_dividend >> 31) & 32'b1 to just (i_dividend >> 31)
    wire[31:0] temp_rem = (i_remainder << 1) | ((i_dividend >> 31));
    assign o_dividend = i_dividend << 1;

    assign o_quotient = (temp_rem < i_divisor) ? i_quotient << 1 : (i_quotient << 1) | 1;
    assign o_remainder = (temp_rem < i_divisor) ? temp_rem : temp_rem - i_divisor;

endmodule
