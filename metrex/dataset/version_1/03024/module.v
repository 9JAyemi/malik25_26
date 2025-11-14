
module DFF(input D, CLK, EN, output reg Q); // positive-edge triggered DFF
  always@(posedge CLK)
    if (EN)
      Q <= D;
endmodule
module TLATCH(input D, E, TE, output reg Q); // transparent latch
  always@(posedge E, posedge TE)
    if (!TE)
      Q <= D;
    else
      Q <= 1'b0;
endmodule