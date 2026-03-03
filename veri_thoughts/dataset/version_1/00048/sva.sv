// SVA checkers for full_adder and adder_4bit.
// Connect a free-running clk when binding.

module full_adder_sva (
  input logic clk,
  input logic a, b, cin,
  input logic sum, cout
);
  default clocking cb @(posedge clk); endclocking

  // Inputs known -> outputs known
  assert property ( !$isunknown({a,b,cin}) |-> ##0 !$isunknown({sum,cout}) );

  // Functional correctness
  assert property ( !$isunknown({a,b,cin}) |-> ##0 {cout,sum} == a + b + cin );

  // Coverage: all input combos and both cout states
  genvar i;
  generate
    for (i=0; i<8; i++) begin : C_FA
      cover property ( !$isunknown({a,b,cin}) && {a,b,cin} == i[2:0] );
    end
  endgenerate
  cover property ( cout == 1'b0 );
  cover property ( cout == 1'b1 );
endmodule


module adder_4bit_sva (
  input  logic       clk,
  input  logic [3:0] A, B, S,
  input  logic       Cout,
  // bind to internals for per-bit/ripple checks
  input  logic [3:0] carry_i,
  input  logic [3:0] sum_i
);
  default clocking cb @(posedge clk); endclocking

  // Inputs known -> outputs known
  assert property ( !$isunknown({A,B}) |-> ##0 !$isunknown({S,Cout}) );

  // End-to-end correctness
  assert property ( !$isunknown({A,B}) |-> ##0 {Cout,S} == A + B );

  // Bit-slice/ripple correctness
  assert property ( !$isunknown({A[0],B[0]})            |-> ##0 {carry_i[0], sum_i[0]} == A[0] + B[0] );
  assert property ( !$isunknown({A[1],B[1],carry_i[0]}) |-> ##0 {carry_i[1], sum_i[1]} == A[1] + B[1] + carry_i[0] );
  assert property ( !$isunknown({A[2],B[2],carry_i[1]}) |-> ##0 {carry_i[2], sum_i[2]} == A[2] + B[2] + carry_i[1] );
  assert property ( !$isunknown({A[3],B[3],carry_i[2]}) |-> ##0 {Cout,      S[3]}      == A[3] + B[3] + carry_i[2] );

  // Connectivity
  assert property ( S == sum_i );

  // Coverage: carry activity and corner cases
  cover property ( carry_i[0] );
  cover property ( carry_i[1] );
  cover property ( carry_i[2] );
  cover property ( Cout );

  cover property ( A==4'd0  && B==4'd0  && S==4'd0  && Cout==1'b0 );
  cover property ( A==4'hF  && B==4'hF  && S==4'hE  && Cout==1'b1 ); // 15+15=30
  cover property ( A==4'b1111 && B==4'b0001 && Cout==1'b1 );         // full ripple
endmodule


// Bind examples (provide clk from your environment)
bind full_adder  full_adder_sva  u_full_adder_sva (.clk(clk), .a(a), .b(b), .cin(cin), .sum(sum), .cout(cout));
bind adder_4bit  adder_4bit_sva  u_adder4_sva     (.clk(clk), .A(A), .B(B), .S(S), .Cout(Cout), .carry_i(carry), .sum_i(sum));