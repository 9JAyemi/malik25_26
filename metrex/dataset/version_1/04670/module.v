
module dual_edge_triggered_ff (
  input clk,
  input d,
  output reg q
);
  reg _q;

  always @(posedge clk) begin
    _q <= d;
  end

  always @(negedge clk) begin
    q <= _q;
  end
endmodule
module full_adder (
  input a,
  input b,
  input cin,
  output sum,
  output cout
);
  assign sum = a ^ b ^ cin;
  assign cout = (a & b) | (b & cin) | (cin & a);
endmodule
module ripple_carry_adder (
  input [3:0] A,
  input [3:0] B,
  output [3:0] S,
  output cout
);
  wire [3:0] sum;
  wire c1, c2, c3;

  full_adder fa0(.a(A[0]), .b(B[0]), .cin(1'b0), .sum(sum[0]), .cout(c1));
  full_adder fa1(.a(A[1]), .b(B[1]), .cin(c1), .sum(sum[1]), .cout(c2));
  full_adder fa2(.a(A[2]), .b(B[2]), .cin(c2), .sum(sum[2]), .cout(c3));
  full_adder fa3(.a(A[3]), .b(B[3]), .cin(c3), .sum(sum[3]), .cout(cout));

  assign S = sum;
endmodule
module functional_module (
  input [3:0] adder_output,
  input flip_flop_output,
  output [3:0] final_output
);
  assign final_output = adder_output ^ flip_flop_output;
endmodule
module top_module (
  input clk,
  input reset,
  input [3:0] A,
  input [3:0] B,
  input d,
  output [3:0] S,
  output q,
  output [3:0] final_output
);
  wire ff_output;
  wire [3:0] adder_output;
  wire carry_out;

  dual_edge_triggered_ff ff(.clk(clk), .d(d), .q(ff_output));
  ripple_carry_adder adder(.A(A), .B(B), .S(adder_output), .cout(carry_out));
  functional_module fm(.adder_output(adder_output), .flip_flop_output(ff_output), .final_output(final_output));

  assign S = adder_output;
  assign q = ff_output;
endmodule