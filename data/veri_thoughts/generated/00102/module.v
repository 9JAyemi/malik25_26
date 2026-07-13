module Adder(
    input [19:0] Data_A_i,
    input [19:0] Data_B_i,
    output [20:0] O,
    output CO,
    output [3:0] S,
    output [3:0] DI
);

  wire [20:0] O;
  wire CO;
  wire [3:0] S;
  wire [3:0] DI;

  assign O = Data_A_i + Data_B_i;
  assign CO = (O[20] == 1'b1);
  assign S = Data_A_i + Data_B_i + CO;
  assign DI = {CO, S[3:1]};

endmodule