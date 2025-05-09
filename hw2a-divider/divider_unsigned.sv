/* INSERT NAME AND PENNKEY HERE */

`timescale 1ns / 1ns

// quotient = dividend / divisor

module divider_unsigned (
    input  wire [31:0] i_dividend,
    input  wire [31:0] i_divisor,
    output wire [31:0] o_remainder,
    output wire [31:0] o_quotient
);

    // TODO: your code here

    // create buses for each stage
    wire [31:0] dividend [33];
    wire [31:0] remainder [33];
    wire [31:0] quotient [33];
    
    // assign initial conditions
    assign dividend[0] = i_dividend;
    assign remainder[0] = 0;
    assign quotient[0] = 0;

    genvar i;
    for (i = 0; i < 32; i ++) begin
        divu_1iter d(.i_dividend(dividend[i]), .i_divisor(i_divisor), .i_remainder(remainder[i]), .i_quotient(quotient[i]),
                    .o_dividend(dividend[i + 1]), .o_remainder(remainder[i + 1]), .o_quotient(quotient[i + 1]));
    end

    // read out
    assign o_remainder = remainder[32];
    assign o_quotient = quotient[32];


endmodule


module divu_1iter (
    input  wire [31:0] i_dividend,
    input  wire [31:0] i_divisor,
    input  wire [31:0] i_remainder,
    input  wire [31:0] i_quotient,
    output wire [31:0] o_dividend,
    output wire [31:0] o_remainder,
    output wire [31:0] o_quotient
);
  /*
    for (int i = 0; i < 32; i++) {
        remainder = (remainder << 1) | ((dividend >> 31) & 0x1);
        if (remainder < divisor) {
            quotient = (quotient << 1);
        } else {
            quotient = (quotient << 1) | 0x1;
            remainder = remainder - divisor;
        }
        dividend = dividend << 1;
    }
    */

    // TODO: your code here
    wire[31:0] temp_rem = (i_remainder << 1) | ((i_dividend >> 31) & 1);
    assign o_dividend = i_dividend << 1;

    assign o_quotient = (temp_rem < i_divisor) ? i_quotient << 1 : (i_quotient << 1) | 1;
    assign o_remainder = (temp_rem < i_divisor) ? temp_rem : temp_rem - i_divisor;
    

endmodule
