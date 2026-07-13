module xor_adder (
  input clk,
  input [1:0] a,
  input [1:0] b,
  output reg [1:0] sum
);

  always @(posedge clk) begin
    sum <= a ^ b;
  end

endmodule