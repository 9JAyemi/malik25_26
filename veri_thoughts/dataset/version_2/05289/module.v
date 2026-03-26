module four_bit_adder(
  input clk,
  input [3:0] A,
  input [3:0] B,
  input Cin,
  output [3:0] C,
  output Cout
);

  reg [4:0] sum;
  
  always @(posedge clk) begin
    sum <= A + B + Cin;
  end
  
  assign Cout = (sum[4] == 1);
  assign C = sum[3:0];
  
endmodule