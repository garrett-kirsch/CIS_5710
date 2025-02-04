`timescale 1ns / 1ps

/**
 * @param a first 1-bit input
 * @param b second 1-bit input
 * @param g whether a and b generate a carry
 * @param p whether a and b would propagate an incoming carry
 */
module gp1(input wire a, b,
           output wire g, p);
   assign g = a & b;
   assign p = a | b;
endmodule

/**
 * Computes aggregate generate/propagate signals over a 4-bit window.
 * @param gin incoming generate signals
 * @param pin incoming propagate signals
 * @param cin the incoming carry
 * @param gout whether these 4 bits internally would generate a carry-out (independent of cin)
 * @param pout whether these 4 bits internally would propagate an incoming carry from cin
 * @param cout the carry outs for the low-order 3 bits
 */
module gp4(input wire [3:0] gin, pin,
           input wire cin,
           output wire gout, pout,
           output wire [2:0] cout);

   assign pout = &pin;
   assign gout = gin[3] | pin[3] & gin[2] | &pin[3:2] & gin[1] | &pin[3:1] & gin[0];
   assign cout[0] = gin[0] | pin[0] & cin;
   assign cout[1] = gin[1] | pin[1] & gin[0] | &pin[1:0] & cin;
   assign cout[2] = gin[2] | pin[2] & gin[1] | &pin[2:1] & gin[0] | &pin[2:0] & cin;
   

endmodule

/** Same as gp4 but for an 8-bit window instead */
module gp8(input wire [7:0] gin, pin,
           input wire cin,
           output wire gout, pout,
           output wire [6:0] cout);
   wire gout0, pout0, gout1, pout1;
   gp4 g0(.gin(gin[3:0]), .pin(pin[3:0]), .cin(cin), .gout(gout0), .pout(pout0), .cout(cout[2:0]));

   assign cout[3] = gout0 | pout0 & cin;
   gp4 g1(.gin(gin[7:4]), .pin(pin[7:4]), .cin(cout[3]), .gout(gout1), .pout(pout1), .cout(cout[6:4]));

   assign pout = pout0 & pout1;
   assign gout = gout1 | gout0 & pout1;
   

endmodule

module cla
  (input wire [31:0]  a, b,
   input wire         cin,
   output wire [31:0] sum);

   wire [31:0] c;
   wire [31:0] g;
   wire [31:0] p;
   wire [3:0] gout;
   wire [3:0] pout;

   // first layer -> individual g&p's
   genvar i;
   for (i = 0; i < 32; i = i + 1) begin
      gp1 gp1(.a(a[i]), .b(b[i]), .g(g[i]), .p(p[i]));
   end

   // generate the 4 gp8's and determine intermediate carries

   
   wire cout1, cout2, cout3, co;
   
   // due to problems I've been having with circular signals, I'm going to try to make 
   // individual carry outs and see if that works

   gp8 g_1(.gin(g[7:0]), .pin(p[7:0]), .cin(cin), 
          .gout(gout[0]), .pout(pout[0]), .cout(c[7:1]));

   assign cout1 = gout[0] | pout[0] & cin;

   gp8 g_2(.gin(g[15:8]), .pin(p[15:8]), .cin(cout1), 
          .gout(gout[1]), .pout(pout[1]), .cout(c[15:9]));

   assign cout2 = gout[1] | pout[1] & cout1;

   gp8 g_3(.gin(g[23:16]), .pin(p[23:16]), .cin(cout2), 
          .gout(gout[2]), .pout(pout[2]), .cout(c[23:17]));

   assign cout3 = gout[2] | pout[2] & cout2;

   gp8 g_4(.gin(g[31:24]), .pin(p[31:24]), .cin(cout3), 
          .gout(gout[3]), .pout(pout[3]), .cout(c[31:25]));

   assign co = gout[3] | pout[3] & cout3;

   // assign final carries
   assign c[0] = cin;
   assign c[8] = cout1;
   assign c[16] = cout2;
   assign c[24] = cout3;

   assign sum = a ^ b ^ c;
   // could get carry out by outputing co

endmodule
