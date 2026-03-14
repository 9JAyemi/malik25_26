
module four_bit_adder(
  input [3:0] A,
  input [3:0] B,
  input CIN,
  input CLK,
  output [3:0] SUM,
  output COUT
);

  reg [3:0] sum;
  reg cout;

  always @(posedge CLK) begin
    {cout, sum} = A + B + CIN;
  end

  assign SUM = sum;
  assign COUT = cout;

endmodule
