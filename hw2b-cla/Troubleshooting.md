# Troubleshooting

## Circular Signals

I found out that System Verilog (or Verilator) doesn't like it when you make a bus then use certain elements of that bus to determine other elements. Apparently, it makes it impossible to properly optimize, so the best solution seems to be making different signals. This doesn't seem like a HW problem - more so it seems like a problem with the tools, but one that is relatively easy to figure out.

## gp8 outputs
When I first made this module, I had gout and pout be the output of my second gp4 instantiation. This was stupid in several ways since that module only half of the information, so it would never be able to make a completely accurate decision. What I needed to do was collect the outputs of the two gp4's, then combine them to determine my gp8 module's outputs.