// SVA for adder_with_multiplexer
module adder_with_multiplexer_sva (
  input  logic        clk,
  input  logic        rst_n,
  input  logic [3:0]  A,
  input  logic [3:0]  B,
  input  logic        sel,
  input  logic [3:0]  sum,
  input  logic        carry_out,
  input  logic        greater_than_7
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n)

  // Arithmetic correctness (implicitly checks mux + adder)
  assert property ( {carry_out, sum} == ({1'b0, A} + {1'b0, (sel ? B : A)}) );

  // No X/Z on outputs when inputs known
  assert property ( !$isunknown({A,B,sel}) |-> !$isunknown({sum,carry_out,greater_than_7}) );

  // Functional intent of greater_than_7 (true sum > 7)
  assert property ( greater_than_7 == (({1'b0, A} + {1'b0, (sel ? B : A)}) > 5'd7) );

  // Coverage
  cover property ( sel == 0 );
  cover property ( sel == 1 );
  cover property ( carry_out );
  cover property ( greater_than_7 );
  cover property ( (A == 4'h0) && (B == 4'h0) );
  cover property ( (A == 4'hF) && (B == 4'hF) );
  cover property ( (A == 4'hF) && (B == 4'h0) );
  cover property ( (A == 4'h0) && (B == 4'hF) );
endmodule

// Example bind (replace tb_clk/tb_rst_n with your TB signals):
// bind adder_with_multiplexer adder_with_multiplexer_sva sva_i (
//   .clk(tb_clk), .rst_n(tb_rst_n),
//   .A(A), .B(B), .sel(sel),
//   .sum(sum), .carry_out(carry_out), .greater_than_7(greater_than_7)
// );