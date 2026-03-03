// SVA for adder_8bit
// Bind these assertions to the DUT and provide a sampling clock from your TB.

module adder_8bit_sva (
  input  logic         clk,     // sampling clock
  input  logic  [7:0]  A,
  input  logic  [7:0]  B,
  input  logic         enable,
  input  logic  [7:0]  C
);
  default clocking cb @(posedge clk); endclocking

  logic [8:0] sum9;
  assign sum9 = {1'b0, A} + {1'b0, B};

  // Inputs known -> output known and functionally correct
  assert property ( !$isunknown({A,B,enable}) |-> ( enable ? (C == sum9[7:0]) : (C == 8'h00) ) );
  assert property ( !$isunknown({A,B,enable}) |-> !$isunknown(C) );

  // Enabled: overflow and non-overflow behavioral checks
  assert property ( !$isunknown({A,B,enable}) && enable &&  sum9[8] |-> (C == sum9[7:0]) && (C < A) && (C < B) );
  assert property ( !$isunknown({A,B,enable}) && enable && !sum9[8] |-> (C >= A) && (C >= B) );

  // Disabled: output must be zero regardless of A/B
  assert property ( !$isunknown({A,B,enable}) && !enable |-> (C == 8'h00) );

  // Functional coverage
  cover property ( enable );
  cover property ( !enable );
  cover property ( enable &&  sum9[8] );                     // overflow
  cover property ( enable && !sum9[8] );                     // no overflow
  cover property ( enable && (A==8'h00) && (B==8'h00) );     // zero add
  cover property ( enable && (A==8'hFF) && (B==8'h01) );     // wrap to 0
endmodule

// Bind example (ensure 'clk' is visible at bind scope)
// bind adder_8bit adder_8bit_sva sva_i(.clk(tb_clk), .A(A), .B(B), .enable(enable), .C(C));