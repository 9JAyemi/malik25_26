
module binary_adder(SUM, A, B, CLK);
  output [1:0] SUM; // Change SUM to a wire
  input [1:0] A, B;
  input CLK;
  
  wire [1:0] carry;
  full_adder FA0(SUM[0], carry[0], A[0], B[0], CLK);
  full_adder FA1(SUM[1], carry[1], A[1], B[1], CLK);

endmodule

module full_adder(S, C, A, B, CLK);
  output S, C;
  input A, B, CLK;
  
  wire t_sum, t_carry;
  assign t_sum = A ^ B;
  assign t_carry = A & B;
  
  DFF s_dff(.q(S), .d(t_sum), .clk(CLK));
  DFF c_dff(.q(C), .d(t_carry), .clk(CLK));
  
endmodule

module DFF(q, d, clk);
  output reg q;
  input d, clk;
  
  always @(posedge clk) begin
    q <= d;
  end
  
endmodule
